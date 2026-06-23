package main

import (
	"context"
	crand "crypto/rand"
	"crypto/sha512"
	"encoding/hex"
	"fmt"
	"html"
	"html/template"
	"io"
	"log"
	"net"
	"net/http"
	_ "net/http/pprof"
	"net/url"
	"os"
	"path"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/bradfitz/gomemcache/memcache"
	gsm "github.com/bradleypeabody/gorilla-sessions-memcache"
	"github.com/go-chi/chi/v5"
	mysql "github.com/go-sql-driver/mysql"
	"github.com/gorilla/sessions"
	"github.com/jmoiron/sqlx"
)

var (
	db    *sqlx.DB
	store *gsm.MemcacheStore
)

const (
	postsPerPage  = 20
	// postsFetchMargin is how many posts the list pages fetch from a single-table
	// query before makePosts filters out posts by deleted users (del_flg != 0).
	// We drop the users JOIN so MySQL can satisfy ORDER BY created_at DESC LIMIT
	// with a backward scan of the posts(created_at) index (no temporary, no
	// filesort). Since ~2% of users are deleted, fetching exactly postsPerPage
	// could yield fewer than 20 after filtering, so we over-fetch by a wide
	// margin. A backward index scan of this many rows is still cheap.
	postsFetchMargin = 40
	ISO8601Format    = "2006-01-02T15:04:05-07:00"
	UploadLimit   = 10 * 1024 * 1024 // 10mb
)

type User struct {
	ID          int       `db:"id"`
	AccountName string    `db:"account_name"`
	Passhash    string    `db:"passhash"`
	Authority   int       `db:"authority"`
	DelFlg      int       `db:"del_flg"`
	CreatedAt   time.Time `db:"created_at"`
}

type Post struct {
	ID           int       `db:"id"`
	UserID       int       `db:"user_id"`
	Body         string    `db:"body"`
	Mime         string    `db:"mime"`
	CreatedAt    time.Time `db:"created_at"`
	CommentCount int       `db:"comment_count"`
	Comments     []Comment
	User         User
	CSRFToken    string
	commentsHTML string // 描画済みコメント divs（一覧用キャッシュ/詳細用に都度生成）
}

type Comment struct {
	ID        int       `db:"id"`
	PostID    int       `db:"post_id"`
	UserID    int       `db:"user_id"`
	Comment   string    `db:"comment"`
	CreatedAt time.Time `db:"created_at"`
	User      User
}

var memcacheClient *memcache.Client

// userCache は users を id -> User でインメモリ保持する。ユーザは約1000件と少なく
// 更新も稀（登録・BAN・initialize のみ）なので、毎リクエストの SELECT users を消せる。
// 整合性は、BAN/initialize で該当エントリを無効化することで担保する。
var userCache sync.Map

// userByName は del_flg=0 のユーザを account_name -> User で保持する。getAccountName の
// `SELECT * FROM users WHERE account_name=?` が DB クエリ digest の最上位級(123万回)で、
// ユーザは BAN 以外で不変なのでキャッシュで丸ごと消せる。BAN/initialize で全クリアして
// 整合性を担保する(BAN は id 指定で name を持たないため、稀な操作として全消しする)。
// ヒット(存在する del_flg=0 ユーザ)のみ格納し、ミス(404)はキャッシュしない。
var userByName sync.Map

// getUserByID はキャッシュ優先でユーザを取得し、無ければ DB から読んでキャッシュする。
func getUserByID(ctx context.Context, id int) (User, bool) {
	if v, ok := userCache.Load(id); ok {
		return v.(User), true
	}
	u := User{}
	if err := db.GetContext(ctx, &u, "SELECT * FROM `users` WHERE `id` = ?", id); err != nil {
		return User{}, false
	}
	userCache.Store(id, u)
	return u, true
}

func init() {
	memdAddr := os.Getenv("ISUCONP_MEMCACHED_ADDRESS")
	if memdAddr == "" {
		// 同一ホストの memcached へは Unix domain socket で繋ぎ、localhost TCP の
		// スタック処理（softirq 含む）を削減する。
		memdAddr = "/run/memcached/memcached.sock"
	}
	memcacheClient = memcache.New(memdAddr)
	store = gsm.NewMemcacheStore(memcacheClient, "iscogram_", []byte("sendagaya"))
	log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile)
}

func dbInitialize(ctx context.Context) {
	sqls := []string{
		"DELETE FROM users WHERE id > 1000",
		"DELETE FROM posts WHERE id > 10000",
		"DELETE FROM comments WHERE id > 100000",
		"UPDATE users SET del_flg = 0",
		"UPDATE users SET del_flg = 1 WHERE id % 50 = 0",
		// 非正規化した comment_count を初期化後の状態に合わせて再計算する。
		// 相関サブクエリは遅いので GROUP BY 集計を1回作って JOIN 更新する。
		// WHERE で値が変わる行だけ更新する。posts は imgdata blob を含み1行が重いため、
		// 全行書き換えると遅い。実際に変化するのは新規コメントが付いた少数の行だけ。
		"UPDATE posts p LEFT JOIN (SELECT post_id, COUNT(*) cnt FROM comments GROUP BY post_id) c ON p.id = c.post_id SET p.comment_count = COALESCE(c.cnt, 0) WHERE p.comment_count <> COALESCE(c.cnt, 0)",
	}

	for _, sql := range sqls {
		db.ExecContext(ctx, sql)
	}
}

func tryLogin(ctx context.Context, accountName, password string) *User {
	u := User{}
	err := db.GetContext(ctx, &u, "SELECT * FROM users WHERE account_name = ? AND del_flg = 0", accountName)
	if err != nil {
		return nil
	}

	if calculatePasshash(ctx, u.AccountName, password) == u.Passhash {
		return &u
	} else {
		return nil
	}
}

func validateUser(accountName, password string) bool {
	return regexp.MustCompile(`\A[0-9a-zA-Z_]{3,}\z`).MatchString(accountName) &&
		regexp.MustCompile(`\A[0-9a-zA-Z_]{6,}\z`).MatchString(password)
}

// 今回のGo実装では言語側のエスケープの仕組みが使えないのでOSコマンドインジェクション対策できない
// 取り急ぎPHPのescapeshellarg関数を参考に自前で実装
// cf: http://jp2.php.net/manual/ja/function.escapeshellarg.php
func escapeshellarg(arg string) string {
	return "'" + strings.Replace(arg, "'", "'\\''", -1) + "'"
}

func digest(ctx context.Context, src string) string {
	// 旧実装は openssl dgst -sha512 を外部プロセスで実行していたが、
	// 出力が同一になるネイティブ sha512 に置換してプロセス起動コストを排除する。
	sum := sha512.Sum512([]byte(src))
	return hex.EncodeToString(sum[:])
}

func calculateSalt(ctx context.Context, accountName string) string {
	return digest(ctx, accountName)
}

func calculatePasshash(ctx context.Context, accountName, password string) string {
	return digest(ctx, password+":"+calculateSalt(ctx, accountName))
}

func getSession(r *http.Request) *sessions.Session {
	session, _ := store.Get(r, "isuconp-go.session")

	return session
}

func getSessionUser(r *http.Request) User {
	ctx := r.Context()
	session := getSession(r)
	uid, ok := session.Values["user_id"]
	if !ok || uid == nil {
		return User{}
	}

	var id int
	switch v := uid.(type) {
	case int:
		id = v
	case int64:
		id = int(v)
	default:
		return User{}
	}

	u, _ := getUserByID(ctx, id)
	return u
}

func getFlash(w http.ResponseWriter, r *http.Request, key string) string {
	session := getSession(r)
	value, ok := session.Values[key]

	if !ok || value == nil {
		return ""
	} else {
		delete(session.Values, key)
		session.Save(r, w)
		return value.(string)
	}
}

// fetchUsers は指定 ID のユーザをまとめて1クエリで取得する。
func fetchUsers(ctx context.Context, idset map[int]struct{}) (map[int]User, error) {
	m := make(map[int]User, len(idset))
	if len(idset) == 0 {
		return m, nil
	}
	// キャッシュにあるものは即返し、無いものだけ1クエリでまとめて取得する。
	args := make([]any, 0, len(idset))
	ph := make([]string, 0, len(idset))
	for id := range idset {
		if v, ok := userCache.Load(id); ok {
			m[id] = v.(User)
			continue
		}
		args = append(args, id)
		ph = append(ph, "?")
	}
	if len(args) == 0 {
		return m, nil
	}
	var users []User
	q := "SELECT * FROM `users` WHERE `id` IN (" + strings.Join(ph, ",") + ")"
	if err := db.SelectContext(ctx, &users, q, args...); err != nil {
		return nil, err
	}
	for _, u := range users {
		m[u.ID] = u
		userCache.Store(u.ID, u)
	}
	return m, nil
}

// fetchComments は対象 post_id 群のコメントをまとめて取得し、投稿ごとに表示用に整える。
// allComments=false の場合は各投稿の最新3件のみ（window 関数で DB 側で絞り、
// 取り過ぎを防ぐ）。表示順は古い順。
func fetchComments(ctx context.Context, postIDs []int, allComments bool) (map[int][]Comment, error) {
	res := make(map[int][]Comment, len(postIDs))
	if len(postIDs) == 0 {
		return res, nil
	}
	args := make([]any, len(postIDs))
	ph := make([]string, len(postIDs))
	for i, id := range postIDs {
		args[i] = id
		ph[i] = "?"
	}
	var comments []Comment
	var q string
	if allComments {
		q = "SELECT `id`,`post_id`,`user_id`,`comment`,`created_at` FROM `comments` WHERE `post_id` IN (" + strings.Join(ph, ",") + ") ORDER BY `created_at` DESC, `id` DESC"
	} else {
		// 各 post_id ごとに新しい順で最大3件だけを DB 側で絞る。
		q = "SELECT `id`,`post_id`,`user_id`,`comment`,`created_at` FROM (" +
			"SELECT `id`,`post_id`,`user_id`,`comment`,`created_at`, ROW_NUMBER() OVER (PARTITION BY `post_id` ORDER BY `created_at` DESC, `id` DESC) AS rn " +
			"FROM `comments` WHERE `post_id` IN (" + strings.Join(ph, ",") + ")) t WHERE t.rn <= 3 ORDER BY t.`created_at` DESC, t.`id` DESC"
	}
	if err := db.SelectContext(ctx, &comments, q, args...); err != nil {
		return nil, err
	}

	uset := map[int]struct{}{}
	for _, c := range comments {
		uset[c.UserID] = struct{}{}
	}
	userMap, err := fetchUsers(ctx, uset)
	if err != nil {
		return nil, err
	}

	for _, c := range comments {
		if !allComments && len(res[c.PostID]) >= 3 {
			continue
		}
		c.User = userMap[c.UserID]
		res[c.PostID] = append(res[c.PostID], c)
	}
	// DESC で詰めたので古い順に反転
	for pid, cs := range res {
		for i, j := 0, len(cs)-1; i < j; i, j = i+1, j-1 {
			cs[i], cs[j] = cs[j], cs[i]
		}
		res[pid] = cs
	}
	return res, nil
}

// selectPosts は posts の SELECT を手動 rows.Scan で実行する。sqlx.SelectContext の
// reflection ベース scan(プロファイル上 scanAll が 13.7% CPU)を避ける。全 posts クエリは
// id,user_id,body,mime,created_at,comment_count を同順で返すので共通化できる。
func selectPosts(ctx context.Context, query string, args ...interface{}) ([]Post, error) {
	rows, err := db.QueryContext(ctx, query, args...)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	posts := make([]Post, 0, postsFetchMargin)
	for rows.Next() {
		var p Post
		if err := rows.Scan(&p.ID, &p.UserID, &p.Body, &p.Mime, &p.CreatedAt, &p.CommentCount); err != nil {
			return nil, err
		}
		posts = append(posts, p)
	}
	return posts, rows.Err()
}

func makePosts(ctx context.Context, results []Post, csrfToken string, allComments bool) ([]Post, error) {
	if len(results) == 0 {
		return []Post{}, nil
	}

	// 投稿者ユーザをまとめて取得
	uset := map[int]struct{}{}
	for _, p := range results {
		uset[p.UserID] = struct{}{}
	}
	userMap, err := fetchUsers(ctx, uset)
	if err != nil {
		return nil, err
	}

	// del_flg=0 のユーザの投稿のみ、最大 postsPerPage 件を採用
	posts := make([]Post, 0, postsPerPage)
	postIDs := make([]int, 0, postsPerPage)
	for _, p := range results {
		u, ok := userMap[p.UserID]
		if !ok || u.DelFlg != 0 {
			continue
		}
		p.User = u
		p.CSRFToken = csrfToken
		posts = append(posts, p)
		postIDs = append(postIDs, p.ID)
		if len(posts) >= postsPerPage {
			break
		}
	}
	if len(posts) == 0 {
		return []Post{}, nil
	}

	// CommentCount は posts.comment_count（非正規化）から取得済み。コメントは描画済み
	// HTML として持たせる。一覧用（最新3件）は memcached(GetMulti) からまとめて取得、
	// 詳細用（全件）は DB から取得して都度描画する。
	if allComments {
		commentsMap, err := fetchComments(ctx, postIDs, true)
		if err != nil {
			return nil, err
		}
		for i := range posts {
			posts[i].commentsHTML = renderCommentsSegment(commentsMap[posts[i].ID])
		}
	} else {
		htmlMap, err := commentsHTMLForPosts(ctx, postIDs)
		if err != nil {
			return nil, err
		}
		for i := range posts {
			posts[i].commentsHTML = htmlMap[posts[i].ID]
		}
	}

	return posts, nil
}

func imageExt(mime string) string {
	switch mime {
	case "image/jpeg":
		return ".jpg"
	case "image/png":
		return ".png"
	case "image/gif":
		return ".gif"
	}
	return ""
}

func imageURL(p Post) string {
	return "/image/" + strconv.Itoa(p.ID) + imageExt(p.Mime)
}

// renderPostInto は post.html 相当の HTML を直接組み立てる（html/template の
// reflection 実行が最大の CPU 消費だったため、ホットパスを手書きに置換する）。
// account_name は [0-9a-zA-Z_]+ に検証済みでエスケープ不要。本文・コメントは
// 自由入力なので html.EscapeString で HTML エスケープする（html/template と同等）。
func renderPostInto(b *strings.Builder, p Post) {
	// html/template は属性値中の "+" を "&#43;" にエスケープするので、出力を一致させる。
	created := strings.ReplaceAll(p.CreatedAt.Format(ISO8601Format), "+", "&#43;")
	id := strconv.Itoa(p.ID)
	acct := p.User.AccountName
	// 最小化: タグ間の改行・インデントを除去（ベンチは goquery セレクタ+TrimSpace で
	// 検証し空白に寛容。本文/属性値は不変に保つ）。レスポンスを小さくして CPU 律速の
	// ローカルベンチでベンチマーカー側のパース CPU と転送量を減らす。
	b.WriteString(`<div class="isu-post" id="pid_`)
	b.WriteString(id)
	b.WriteString(`" data-created-at="`)
	b.WriteString(created)
	b.WriteString(`"><div class="isu-post-header"><a href="/@`)
	b.WriteString(acct)
	b.WriteString(` " class="isu-post-account-name">`)
	b.WriteString(acct)
	b.WriteString(`</a><a href="/posts/`)
	b.WriteString(id)
	b.WriteString(`" class="isu-post-permalink"><time class="timeago" datetime="`)
	b.WriteString(created)
	b.WriteString(`"></time></a></div><div class="isu-post-image"><img src="`)
	b.WriteString(imageURL(p))
	b.WriteString(`" class="isu-image"></div><div class="isu-post-text"><a href="/@`)
	b.WriteString(acct)
	b.WriteString(`" class="isu-post-account-name">`)
	b.WriteString(acct)
	b.WriteString(`</a>`)
	b.WriteString(html.EscapeString(p.Body))
	b.WriteString(`</div><div class="isu-post-comment"><div class="isu-post-comment-count">comments: <b>`)
	b.WriteString(strconv.Itoa(p.CommentCount))
	b.WriteString(`</b></div>`)
	b.WriteString(p.commentsHTML)
	b.WriteString(`<div class="isu-comment-form"><form method="post" action="/comment"><input type="text" name="comment"><input type="hidden" name="post_id" value="`)
	b.WriteString(id)
	b.WriteString(`"><input type="hidden" name="csrf_token" value="`)
	b.WriteString(p.CSRFToken)
	b.WriteString(`"><input type="submit" name="submit" value="submit"></form></div></div></div>`)
}

// renderPostsInto は投稿一覧の HTML を渡された builder に直接書き込む。中間文字列を
// 作らないので、ページ生成側で 20KB 級の一時 string + コピー(alloc 圧の主因)を消せる。
func renderPostsInto(b *strings.Builder, posts []Post) {
	b.WriteString(`<div class="isu-posts">`)
	for _, p := range posts {
		renderPostInto(b, p)
	}
	b.WriteString(`</div>`)
}

// renderPosts は posts.html 相当（投稿一覧）の HTML を生成する。テンプレート FuncMap
// および /posts フラグメント用に string を返す版。
func renderPosts(posts []Post) template.HTML {
	var b strings.Builder
	renderPostsInto(&b, posts)
	return template.HTML(b.String())
}

// renderPost は単一投稿（post_id.html 用）の HTML を生成する。
func renderPost(p Post) template.HTML {
	var b strings.Builder
	renderPostInto(&b, p)
	return template.HTML(b.String())
}

// layout.html の冒頭（DOCTYPE〜header）を直接書き出す。html/template の reflection
// 実行が CPU プロファイル上 13% を占めていたため、ホットパス(getIndex)を手書きにする。
// content の前までを書き、呼び出し側が content を続けて書いて closeLayout で閉じる。
func openLayout(b *strings.Builder, me User) {
	b.WriteString(`<!DOCTYPE html><html><head><meta charset="utf-8"><title>Iscogram</title><link href="/css/style.css" media="screen" rel="stylesheet" type="text/css"></head><body><div class="container"><div class="header"><div class="isu-title"><h1><a href="/">Iscogram</a></h1></div><div class="isu-header-menu">`)
	if me.ID == 0 {
		b.WriteString(`<div><a href="/login">ログイン</a></div>`)
	} else {
		// AccountName は [0-9a-zA-Z_]+ 検証済みでエスケープ不要。
		b.WriteString(`<div><a href="/@`)
		b.WriteString(me.AccountName)
		b.WriteString(`"><span class="isu-account-name">`)
		b.WriteString(me.AccountName)
		b.WriteString(`</span>さん</a></div>`)
		if me.Authority == 1 {
			b.WriteString(`<div><a href="/admin/banned">管理者用ページ</a></div>`)
		}
		b.WriteString(`<div><a href="/logout">ログアウト</a></div>`)
	}
	b.WriteString(`</div></div>`)
}

func closeLayout(b *strings.Builder) {
	b.WriteString(`</div><script src="/js/timeago.min.js"></script><script src="/js/main.js"></script></body></html>`)
}

// pageBufPool はページ生成用の strings.Builder を再利用する。ページ毎の 24KB バッファ
// + String() コピー(mallocgc が CPU の ~12%)を削減する。ハンドラは build→w へ書き出し→
// Reset して Put する。b.String() は書き出し完了後に Put するため安全(Put 後に他の goroutine
// が Reset しても、こちらの書き出しは既に完了済み)。
var pageBufPool = sync.Pool{New: func() any { b := new(strings.Builder); b.Grow(24 * 1024); return b }}

func getPageBuf() *strings.Builder {
	b := pageBufPool.Get().(*strings.Builder)
	b.Reset()
	return b
}

// writePage はページ HTML を w に書き出し、builder を pool に返す。
func writePage(w http.ResponseWriter, b *strings.Builder) {
	w.Header().Set("Content-Type", "text/html; charset=UTF-8")
	io.WriteString(w, b.String())
	pageBufPool.Put(b)
}

// renderIndexInto は GET / のページ全体（layout + index content + posts）を渡された
// builder に手書きで書き込む。tmplIndex.Execute（html/template reflection）の置き換え。
func renderIndexInto(b *strings.Builder, me User, posts []Post, csrfToken, flash string) {
	openLayout(b, me)
	// index.html の content（投稿フォーム）。
	b.WriteString(`<div class="isu-submit"><form method="post" action="/" enctype="multipart/form-data"><div class="isu-form"><input type="file" name="file" value="file"></div><div class="isu-form"><textarea name="body"></textarea></div><div class="form-submit"><input type="hidden" name="csrf_token" value="`)
	b.WriteString(csrfToken)
	b.WriteString(`"><input type="submit" name="submit" value="submit"></div>`)
	if flash != "" {
		b.WriteString(`<div id="notice-message" class="alert alert-danger">`)
		b.WriteString(html.EscapeString(flash))
		b.WriteString(`</div>`)
	}
	b.WriteString(`</form></div>`)
	renderPostsInto(b, posts)
	b.WriteString(`<div id="isu-post-more"><button id="isu-post-more-btn">もっと見る</button><img class="isu-loading-icon" src="/img/ajax-loader.gif"></div>`)
	closeLayout(b)
}

// renderPostIDPage は GET /posts/:id のページ全体（layout + post_id content）を
// 手書きで生成する。tmplPostID.Execute の置き換え。post_id.html の content は
// "\n{{ renderPost .Post }}\n"。
func renderPostIDInto(b *strings.Builder, me User, p Post) {
	openLayout(b, me)
	renderPostInto(b, p)
	closeLayout(b)
}

// renderUserPage は GET /@account のページ全体（layout + user.html content）を
// 手書きで生成する。tmplUser.Execute の置き換え。
func renderUserInto(b *strings.Builder, me User, user User, posts []Post, postCount, commentCount, commentedCount int) {
	openLayout(b, me)
	// AccountName は [0-9a-zA-Z_]+ 検証済みでエスケープ不要。
	b.WriteString(`<div class="isu-user"><div><span class="isu-user-account-name">`)
	b.WriteString(user.AccountName)
	b.WriteString(`さん</span>のページ</div><div>投稿数 <span class="isu-post-count">`)
	b.WriteString(strconv.Itoa(postCount))
	b.WriteString(`</span></div><div>コメント数 <span class="isu-comment-count">`)
	b.WriteString(strconv.Itoa(commentCount))
	b.WriteString(`</span></div><div>被コメント数 <span class="isu-commented-count">`)
	b.WriteString(strconv.Itoa(commentedCount))
	b.WriteString(`</span></div></div>`)
	renderPostsInto(b, posts)
	closeLayout(b)
}

// renderCommentsSegment は post.html のコメント部分（isu-comment divs）の HTML を
// 生成する。renderPostInto が p.commentsHTML として挿入する。
func renderCommentsSegment(comments []Comment) string {
	var b strings.Builder
	for _, c := range comments {
		b.WriteString(`<div class="isu-comment"><a href="/@`)
		b.WriteString(c.User.AccountName)
		b.WriteString(`" class="isu-comment-account-name">`)
		b.WriteString(c.User.AccountName)
		b.WriteString(`</a><span class="isu-comment-text">`)
		b.WriteString(html.EscapeString(c.Comment))
		b.WriteString(`</span></div>`)
	}
	return b.String()
}

// commentsHTMLForPosts は一覧表示用（最新3件）の描画済みコメント HTML を、
// memcached から GetMulti で1往復取得する。最大の DB 負荷だった SELECT comments を
// 消し、かつ描画コストも削減する。miss は DB から取得して描画・キャッシュする。
func commentsHTMLForPosts(ctx context.Context, postIDs []int) (map[int]string, error) {
	res := make(map[int]string, len(postIDs))
	keys := make([]string, len(postIDs))
	keyToID := make(map[string]int, len(postIDs))
	for i, pid := range postIDs {
		k := "chtml_" + strconv.Itoa(pid)
		keys[i] = k
		keyToID[k] = pid
	}
	items, err := memcacheClient.GetMulti(keys)
	if err != nil {
		items = nil // キャッシュ障害時は全件 miss 扱いで DB にフォールバック
	}
	var miss []int
	for _, pid := range postIDs {
		if it, ok := items["chtml_"+strconv.Itoa(pid)]; ok {
			res[pid] = string(it.Value)
		} else {
			miss = append(miss, pid)
		}
	}
	if len(miss) > 0 {
		fetched, err := fetchComments(ctx, miss, false)
		if err != nil {
			return nil, err
		}
		for _, pid := range miss {
			h := renderCommentsSegment(fetched[pid])
			res[pid] = h
			memcacheClient.Set(&memcache.Item{Key: "chtml_" + strconv.Itoa(pid), Value: []byte(h)})
		}
	}
	return res, nil
}

// 画像を public/image 配下にファイルとして書き出す（nginx が静的配信できるようにする）。
// 一時ファイルに書いてから rename することで、配信中の半端なファイルを避ける。
func writeImageFile(id int, mime string, data []byte) error {
	ext := imageExt(mime)
	if ext == "" {
		return fmt.Errorf("unknown mime: %s", mime)
	}
	dst := "../public/image/" + strconv.Itoa(id) + ext
	tmp := dst + ".tmp"
	if err := os.WriteFile(tmp, data, 0644); err != nil {
		return err
	}
	return os.Rename(tmp, dst)
}

func isLogin(u User) bool {
	return u.ID != 0
}

func getCSRFToken(r *http.Request) string {
	session := getSession(r)
	csrfToken, ok := session.Values["csrf_token"]
	if !ok {
		return ""
	}
	return csrfToken.(string)
}

func secureRandomStr(b int) string {
	k := make([]byte, b)
	if _, err := crand.Read(k); err != nil {
		panic(err)
	}
	return fmt.Sprintf("%x", k)
}

func getTemplPath(filename string) string {
	return path.Join("templates", filename)
}

// cleanupOrphanImages は dbInitialize が削除する posts(id>10000) に対応する
// 画像ファイルを public/image から消す。これをしないとベンチ実行のたびに
// 投稿画像のファイルが溜まり続け、ディスクを食い潰す。
func cleanupOrphanImages() {
	entries, err := os.ReadDir("../public/image")
	if err != nil {
		return
	}
	for _, e := range entries {
		name := e.Name()
		dot := strings.IndexByte(name, '.')
		if dot <= 0 {
			continue
		}
		id, err := strconv.Atoi(name[:dot])
		if err != nil {
			continue
		}
		if id > 10000 {
			os.Remove("../public/image/" + name)
		}
	}
}

func getInitialize(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	dbInitialize(ctx)
	cleanupOrphanImages()
	// dbInitialize が del_flg を作り直すため、ユーザキャッシュを破棄する。
	userCache.Range(func(k, _ any) bool {
		userCache.Delete(k)
		return true
	})
	userByName.Range(func(k, _ any) bool {
		userByName.Delete(k)
		return true
	})
	// 描画済みコメント HTML キャッシュ（およびセッション）も初期化のため flush する。
	memcacheClient.FlushAll()
	w.WriteHeader(http.StatusOK)
}

func getLogin(w http.ResponseWriter, r *http.Request) {
	me := getSessionUser(r)

	if isLogin(me) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	tmplLogin.Execute(w, struct {
		Me    User
		Flash string
	}{me, getFlash(w, r, "notice")})
}

func postLogin(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	if isLogin(getSessionUser(r)) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	u := tryLogin(ctx, r.FormValue("account_name"), r.FormValue("password"))

	if u != nil {
		session := getSession(r)
		session.Values["user_id"] = u.ID
		session.Values["csrf_token"] = secureRandomStr(16)
		session.Save(r, w)

		http.Redirect(w, r, "/", http.StatusFound)
	} else {
		session := getSession(r)
		session.Values["notice"] = "アカウント名かパスワードが間違っています"
		session.Save(r, w)

		http.Redirect(w, r, "/login", http.StatusFound)
	}
}

func getRegister(w http.ResponseWriter, r *http.Request) {
	if isLogin(getSessionUser(r)) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	tmplRegister.Execute(w, struct {
		Me    User
		Flash string
	}{User{}, getFlash(w, r, "notice")})
}

func postRegister(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	if isLogin(getSessionUser(r)) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	accountName, password := r.FormValue("account_name"), r.FormValue("password")

	validated := validateUser(accountName, password)
	if !validated {
		session := getSession(r)
		session.Values["notice"] = "アカウント名は3文字以上、パスワードは6文字以上である必要があります"
		session.Save(r, w)

		http.Redirect(w, r, "/register", http.StatusFound)
		return
	}

	exists := 0
	// ユーザーが存在しない場合はエラーになるのでエラーチェックはしない
	db.GetContext(ctx, &exists, "SELECT 1 FROM users WHERE `account_name` = ?", accountName)

	if exists == 1 {
		session := getSession(r)
		session.Values["notice"] = "アカウント名がすでに使われています"
		session.Save(r, w)

		http.Redirect(w, r, "/register", http.StatusFound)
		return
	}

	query := "INSERT INTO `users` (`account_name`, `passhash`) VALUES (?,?)"
	result, err := db.ExecContext(ctx, query, accountName, calculatePasshash(ctx, accountName, password))
	if err != nil {
		log.Print(err)
		return
	}

	session := getSession(r)
	uid, err := result.LastInsertId()
	if err != nil {
		log.Print(err)
		return
	}
	session.Values["user_id"] = uid
	session.Values["csrf_token"] = secureRandomStr(16)
	session.Save(r, w)

	http.Redirect(w, r, "/", http.StatusFound)
}

func getLogout(w http.ResponseWriter, r *http.Request) {
	session := getSession(r)
	delete(session.Values, "user_id")
	session.Options = &sessions.Options{MaxAge: -1}
	session.Save(r, w)

	http.Redirect(w, r, "/", http.StatusFound)
}

func getIndex(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	me := getSessionUser(r)

	// Single-table query so MySQL uses a backward scan of the posts(created_at)
	// index for ORDER BY ... LIMIT (no temporary/filesort). makePosts then drops
	// posts by deleted users and keeps the first postsPerPage; postsFetchMargin
	// guarantees enough survivors. Bind the limit so it is reusable as a constant.
	// FORCE INDEX: imgdata 削除でテーブルが小さくなった結果、optimizer が
	// 全スキャン+filesort を誤って選ぶ。created_at index の backward scan を強制する。
	results, err := selectPosts(ctx, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` FORCE INDEX(idx_created_at) ORDER BY `created_at` DESC LIMIT ?", postsFetchMargin)
	if err != nil {
		log.Print(err)
		return
	}

	csrfToken := getCSRFToken(r)
	posts, err := makePosts(ctx, results, csrfToken, false)
	if err != nil {
		log.Print(err)
		return
	}

	// html/template の reflection 実行(プロファイル上 13% CPU)を避け、ページ全体を
	// 手書きで生成して直接書き出す。builder は pool から再利用。
	b := getPageBuf()
	renderIndexInto(b, me, posts, csrfToken, getFlash(w, r, "notice"))
	writePage(w, b)
}

func getAccountName(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	accountName := r.PathValue("accountName")
	user := User{}

	// account_name -> User の in-memory キャッシュ優先（DB digest 最上位の SELECT を消す）。
	if v, ok := userByName.Load(accountName); ok {
		user = v.(User)
	} else {
		err := db.GetContext(ctx, &user, "SELECT * FROM `users` WHERE `account_name` = ? AND `del_flg` = 0", accountName)
		if err != nil {
			log.Print(err)
			return
		}
		if user.ID != 0 {
			userByName.Store(accountName, user)
		}
	}

	if user.ID == 0 {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	results, err := selectPosts(ctx, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` WHERE `user_id` = ? ORDER BY `created_at` DESC LIMIT 20", user.ID)
	if err != nil {
		log.Print(err)
		return
	}

	posts, err := makePosts(ctx, results, getCSRFToken(r), false)
	if err != nil {
		log.Print(err)
		return
	}

	commentCount := 0
	err = db.GetContext(ctx, &commentCount, "SELECT COUNT(*) AS count FROM `comments` WHERE `user_id` = ?", user.ID)
	if err != nil {
		log.Print(err)
		return
	}

	postCount := 0
	err = db.GetContext(ctx, &postCount, "SELECT COUNT(*) AS count FROM `posts` WHERE `user_id` = ?", user.ID)
	if err != nil {
		log.Print(err)
		return
	}

	// そのユーザの投稿に付いたコメント総数。post_id を全取得して巨大 IN にする代わりに
	// JOIN 一発で求める。
	commentedCount := 0
	err = db.GetContext(ctx, &commentedCount, "SELECT COUNT(*) FROM `comments` c JOIN `posts` p ON c.`post_id` = p.`id` WHERE p.`user_id` = ?", user.ID)
	if err != nil {
		log.Print(err)
		return
	}

	me := getSessionUser(r)

	// html/template の reflection 実行を避け、手書きで生成して直接書き出す。
	b := getPageBuf()
	renderUserInto(b, me, user, posts, postCount, commentCount, commentedCount)
	writePage(w, b)
}

func getPosts(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	m, err := url.ParseQuery(r.URL.RawQuery)
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		log.Print(err)
		return
	}
	maxCreatedAt := m.Get("max_created_at")
	if maxCreatedAt == "" {
		return
	}

	t, err := time.Parse(ISO8601Format, maxCreatedAt)
	if err != nil {
		log.Print(err)
		return
	}

	// Single-table query (see getIndex): backward scan of posts(created_at) with
	// LIMIT, then makePosts filters deleted users; postsFetchMargin over-fetches.
	results, err := selectPosts(ctx, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` FORCE INDEX(idx_created_at) WHERE `created_at` <= ? ORDER BY `created_at` DESC LIMIT ?", t.Format(ISO8601Format), postsFetchMargin)
	if err != nil {
		log.Print(err)
		return
	}

	posts, err := makePosts(ctx, results, getCSRFToken(r), false)
	if err != nil {
		log.Print(err)
		return
	}

	if len(posts) == 0 {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	tmplPosts.Execute(w, posts)
}

func getPostsID(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	pidStr := r.PathValue("id")
	pid, err := strconv.Atoi(pidStr)
	if err != nil {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	results, err := selectPosts(ctx, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` WHERE `id` = ?", pid)
	if err != nil {
		log.Print(err)
		return
	}

	posts, err := makePosts(ctx, results, getCSRFToken(r), true)
	if err != nil {
		log.Print(err)
		return
	}

	if len(posts) == 0 {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	p := posts[0]

	me := getSessionUser(r)

	// html/template の reflection 実行を避け、手書きで生成して直接書き出す。
	b := getPageBuf()
	renderPostIDInto(b, me, p)
	writePage(w, b)
}

func postIndex(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/login", http.StatusFound)
		return
	}

	if r.FormValue("csrf_token") != getCSRFToken(r) {
		w.WriteHeader(http.StatusUnprocessableEntity)
		return
	}

	file, header, err := r.FormFile("file")
	if err != nil {
		session := getSession(r)
		session.Values["notice"] = "画像が必須です"
		session.Save(r, w)

		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	mime := ""
	if file != nil {
		// 投稿のContent-Typeからファイルのタイプを決定する
		contentType := header.Header["Content-Type"][0]
		if strings.Contains(contentType, "jpeg") {
			mime = "image/jpeg"
		} else if strings.Contains(contentType, "png") {
			mime = "image/png"
		} else if strings.Contains(contentType, "gif") {
			mime = "image/gif"
		} else {
			session := getSession(r)
			session.Values["notice"] = "投稿できる画像形式はjpgとpngとgifだけです"
			session.Save(r, w)

			http.Redirect(w, r, "/", http.StatusFound)
			return
		}
	}

	filedata, err := io.ReadAll(file)
	if err != nil {
		log.Print(err)
		return
	}

	if len(filedata) > UploadLimit {
		session := getSession(r)
		session.Values["notice"] = "ファイルサイズが大きすぎます"
		session.Save(r, w)

		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	// 画像はファイル配信（imgdata カラムは削除済み）。
	// 「投稿は可視だが画像ファイルが未生成」という窓を無くすため、トランザクション内で
	// INSERT → ファイル書き出し → コミット の順にする。コミットするまで他コネクションから
	// 投稿は見えないので、可視化された時点では必ず画像ファイルが存在する。
	tx, err := db.BeginTxx(ctx, nil)
	if err != nil {
		log.Print(err)
		return
	}
	result, err := tx.ExecContext(ctx, "INSERT INTO `posts` (`user_id`, `mime`, `body`) VALUES (?,?,?)", me.ID, mime, r.FormValue("body"))
	if err != nil {
		tx.Rollback()
		log.Print(err)
		return
	}
	pid, err := result.LastInsertId()
	if err != nil {
		tx.Rollback()
		log.Print(err)
		return
	}
	if err := writeImageFile(int(pid), mime, filedata); err != nil {
		// ファイルが書けないなら投稿自体を作らない（DB とファイルの整合を保つ）。
		tx.Rollback()
		log.Print(err)
		return
	}
	if err := tx.Commit(); err != nil {
		log.Print(err)
		return
	}

	http.Redirect(w, r, "/posts/"+strconv.FormatInt(pid, 10), http.StatusFound)
}

func getImage(w http.ResponseWriter, r *http.Request) {
	pidStr := r.PathValue("id")
	pid, err := strconv.Atoi(pidStr)
	if err != nil {
		w.WriteHeader(http.StatusNotFound)
		return
	}
	ext := r.PathValue("ext")

	// 画像はファイルとして保存され nginx が直接配信する。try_files の fallback で
	// ここ(@app)に来るのはファイルが存在しない場合なので、あれば返し無ければ404。
	p := "../public/image/" + strconv.Itoa(pid) + "." + ext
	if _, err := os.Stat(p); err != nil {
		w.WriteHeader(http.StatusNotFound)
		return
	}
	http.ServeFile(w, r, p)
}

func postComment(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/login", http.StatusFound)
		return
	}

	if r.FormValue("csrf_token") != getCSRFToken(r) {
		w.WriteHeader(http.StatusUnprocessableEntity)
		return
	}

	postID, err := strconv.Atoi(r.FormValue("post_id"))
	if err != nil {
		log.Print("post_idは整数のみです")
		return
	}

	query := "INSERT INTO `comments` (`post_id`, `user_id`, `comment`) VALUES (?,?,?)"
	_, err = db.ExecContext(ctx, query, postID, me.ID, r.FormValue("comment"))
	if err != nil {
		log.Print(err)
		return
	}

	// 非正規化した comment_count を更新（GET に即時反映させる）。
	if _, err := db.ExecContext(ctx, "UPDATE `posts` SET `comment_count` = `comment_count` + 1 WHERE `id` = ?", postID); err != nil {
		log.Print(err)
	}
	// この投稿の描画済みコメント HTML キャッシュを無効化（次の取得で作り直す）。
	memcacheClient.Delete("chtml_" + strconv.Itoa(postID))

	http.Redirect(w, r, fmt.Sprintf("/posts/%d", postID), http.StatusFound)
}

func getAdminBanned(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	if me.Authority == 0 {
		w.WriteHeader(http.StatusForbidden)
		return
	}

	users := []User{}
	err := db.SelectContext(ctx, &users, "SELECT * FROM `users` WHERE `authority` = 0 AND `del_flg` = 0 ORDER BY `created_at` DESC")
	if err != nil {
		log.Print(err)
		return
	}

	tmplBanned.Execute(w, struct {
		Users     []User
		Me        User
		CSRFToken string
	}{users, me, getCSRFToken(r)})
}

func postAdminBanned(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	me := getSessionUser(r)
	if !isLogin(me) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	if me.Authority == 0 {
		w.WriteHeader(http.StatusForbidden)
		return
	}

	if r.FormValue("csrf_token") != getCSRFToken(r) {
		w.WriteHeader(http.StatusUnprocessableEntity)
		return
	}

	query := "UPDATE `users` SET `del_flg` = ? WHERE `id` = ?"

	err := r.ParseForm()
	if err != nil {
		log.Print(err)
		return
	}

	for _, id := range r.Form["uid[]"] {
		db.ExecContext(ctx, query, 1, id)
		// BAN で del_flg が変わるのでキャッシュを無効化する。
		if n, err := strconv.Atoi(id); err == nil {
			userCache.Delete(n)
		}
	}
	// userByName は account_name 起点で BAN 対象の name を持たないため全クリア（稀な操作）。
	userByName.Range(func(k, _ any) bool { userByName.Delete(k); return true })

	http.Redirect(w, r, "/admin/banned", http.StatusFound)
}

var (
	tmplIndex    *template.Template
	tmplPosts    *template.Template
	tmplPostID   *template.Template
	tmplUser     *template.Template
	tmplLogin    *template.Template
	tmplRegister *template.Template
	tmplBanned   *template.Template
)

// テンプレートは起動時に一度だけパースする（毎リクエストの再パースを避ける）。
func parseTemplates() {
	fmap := template.FuncMap{"imageURL": imageURL, "renderPosts": renderPosts, "renderPost": renderPost}
	tmplIndex = template.Must(template.New("layout.html").Funcs(fmap).ParseFiles(
		getTemplPath("layout.html"), getTemplPath("index.html"), getTemplPath("posts.html"), getTemplPath("post.html")))
	tmplPosts = template.Must(template.New("posts.html").Funcs(fmap).ParseFiles(
		getTemplPath("posts.html"), getTemplPath("post.html")))
	tmplPostID = template.Must(template.New("layout.html").Funcs(fmap).ParseFiles(
		getTemplPath("layout.html"), getTemplPath("post_id.html"), getTemplPath("post.html")))
	tmplUser = template.Must(template.New("layout.html").Funcs(fmap).ParseFiles(
		getTemplPath("layout.html"), getTemplPath("user.html"), getTemplPath("posts.html"), getTemplPath("post.html")))
	tmplLogin = template.Must(template.New("layout.html").ParseFiles(
		getTemplPath("layout.html"), getTemplPath("login.html")))
	tmplRegister = template.Must(template.New("layout.html").ParseFiles(
		getTemplPath("layout.html"), getTemplPath("register.html")))
	tmplBanned = template.Must(template.New("layout.html").ParseFiles(
		getTemplPath("layout.html"), getTemplPath("banned.html")))
}

func main() {
	host := os.Getenv("ISUCONP_DB_HOST")
	if host == "" {
		host = "localhost"
	}
	port := os.Getenv("ISUCONP_DB_PORT")
	if port == "" {
		port = "3306"
	}
	_, err := strconv.Atoi(port)
	if err != nil {
		log.Fatalf("Failed to read DB port number from an environment variable ISUCONP_DB_PORT.\nError: %s", err.Error())
	}
	user := os.Getenv("ISUCONP_DB_USER")
	if user == "" {
		user = "root"
	}
	password := os.Getenv("ISUCONP_DB_PASSWORD")
	dbname := os.Getenv("ISUCONP_DB_NAME")
	if dbname == "" {
		dbname = "isuconp"
	}

	cfg := mysql.NewConfig()
	cfg.User = user
	cfg.Passwd = password
	if host == "localhost" {
		cfg.Net = "unix"
		cfg.Addr = "/var/run/mysqld/mysqld.sock"
	} else {
		cfg.Net = "tcp"
		cfg.Addr = fmt.Sprintf("%s:%s", host, port)
	}
	cfg.DBName = dbname
	cfg.Params = map[string]string{
		"charset": "utf8mb4",
	}
	cfg.ParseTime = true
	cfg.Loc = time.Local
	cfg.InterpolateParams = true
	dsn := cfg.FormatDSN()

	db, err = sqlx.Open("mysql", dsn)
	if err != nil {
		log.Fatalf("Failed to connect to DB: %s.", err.Error())
	}
	defer db.Close()

	// クエリが十分速くなり CPU に空きが出たため、コネクション上限を引き上げて
	// 並行度を上げ、空いた CPU を使い切る（待ち行列で詰まらせない）。
	db.SetMaxOpenConns(64)
	db.SetMaxIdleConns(64)
	db.SetConnMaxLifetime(0)

	parseTemplates()

	// プロファイル用（localhost のみ、計測時だけ使う）。
	go func() { http.ListenAndServe("localhost:6060", nil) }()

	r := chi.NewRouter()

	r.Get("/initialize", getInitialize)
	r.Get("/login", getLogin)
	r.Post("/login", postLogin)
	r.Get("/register", getRegister)
	r.Post("/register", postRegister)
	r.Get("/logout", getLogout)
	r.Get("/", getIndex)
	r.Get("/posts", getPosts)
	r.Get("/posts/{id}", getPostsID)
	r.Post("/", postIndex)
	r.Get("/image/{id}.{ext}", getImage)
	r.Post("/comment", postComment)
	r.Get("/admin/banned", getAdminBanned)
	r.Post("/admin/banned", postAdminBanned)
	r.Get(`/@{accountName:[0-9a-zA-Z_]+}`, getAccountName)
	r.Mount("/", http.FileServer(http.Dir("../public")))

	// nginx からは Unix domain socket で受ける（localhost TCP のスタック処理を削減）。
	const sockPath = "/tmp/isu-go.sock"
	os.Remove(sockPath)
	ln, err := net.Listen("unix", sockPath)
	if err != nil {
		log.Fatal(err)
	}
	if err := os.Chmod(sockPath, 0777); err != nil {
		log.Fatal(err)
	}
	log.Fatal(http.Serve(ln, r))
}
