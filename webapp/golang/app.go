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
	"sync/atomic"
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

// pageVersion は投稿・コメント・BAN・initialize でインクリメントされ、
// 描画済み一覧 HTML のキャッシュキーに使う（書き込みで世代を上げて無効化）。
var pageVersion int64

// csrfPlaceholder はキャッシュした一覧 HTML 内の CSRF トークンの差し替え用プレースホルダ。
// 全ユーザ共通の一覧をキャッシュし、配信時にリクエスト毎の CSRF トークンへ置換する。
// コンテンツに偶然含まれないよう起動時にランダム生成する。
var csrfPlaceholder string

func bumpPageVersion() {
	atomic.AddInt64(&pageVersion, 1)
}

// 投稿一覧 HTML のインプロセスキャッシュ。読みは atomic ポインタでロックフリー、
// 再構築は singleflight 用の mutex で1回だけ行う（サンダリングハード回避）。
type idxCacheEntry struct {
	ver  int64
	html string
}

var (
	idxCachePtr       atomic.Pointer[idxCacheEntry]
	idxCacheRebuildMu sync.Mutex
)

// indexPostsHTML は投稿一覧 HTML（CSRF はプレースホルダ）をバージョンキャッシュから返す。
func indexPostsHTML(ctx context.Context) (string, error) {
	ver := atomic.LoadInt64(&pageVersion)
	if c := idxCachePtr.Load(); c != nil && c.ver == ver {
		return c.html, nil // ロックフリーの高速パス
	}
	idxCacheRebuildMu.Lock()
	defer idxCacheRebuildMu.Unlock()
	if c := idxCachePtr.Load(); c != nil && c.ver == ver { // 二重チェック
		return c.html, nil
	}
	results := []Post{}
	if err := db.SelectContext(ctx, &results, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` FORCE INDEX(idx_created_at) ORDER BY `created_at` DESC LIMIT ?", postsFetchMargin); err != nil {
		return "", err
	}
	posts, err := makePosts(ctx, results, csrfPlaceholder, false)
	if err != nil {
		return "", err
	}
	html := string(renderPosts(posts))
	idxCachePtr.Store(&idxCacheEntry{ver: ver, html: html})
	return html, nil
}

// userCache は users を id -> User でインメモリ保持する。ユーザは約1000件と少なく
// 更新も稀（登録・BAN・initialize のみ）なので、毎リクエストの SELECT users を消せる。
// 整合性は、BAN/initialize で該当エントリを無効化することで担保する。
var userCache sync.Map

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
	csrfPlaceholder = "__CSRF_" + secureRandomStr(16) + "__"
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
	b.WriteString(`<div class="isu-post" id="pid_`)
	b.WriteString(id)
	b.WriteString(`" data-created-at="`)
	b.WriteString(created)
	b.WriteString("\">\n  <div class=\"isu-post-header\">\n    <a href=\"/@")
	b.WriteString(acct)
	b.WriteString(` " class="isu-post-account-name">`)
	b.WriteString(acct)
	b.WriteString("</a>\n    <a href=\"/posts/")
	b.WriteString(id)
	b.WriteString("\" class=\"isu-post-permalink\">\n      <time class=\"timeago\" datetime=\"")
	b.WriteString(created)
	b.WriteString("\"></time>\n    </a>\n  </div>\n  <div class=\"isu-post-image\">\n    <img src=\"")
	b.WriteString(imageURL(p))
	b.WriteString("\" class=\"isu-image\">\n  </div>\n  <div class=\"isu-post-text\">\n    <a href=\"/@")
	b.WriteString(acct)
	b.WriteString(`" class="isu-post-account-name">`)
	b.WriteString(acct)
	b.WriteString("</a>\n    ")
	b.WriteString(html.EscapeString(p.Body))
	b.WriteString("\n  </div>\n  <div class=\"isu-post-comment\">\n    <div class=\"isu-post-comment-count\">\n      comments: <b>")
	b.WriteString(strconv.Itoa(p.CommentCount))
	b.WriteString("</b>\n    </div>\n\n    ")
	b.WriteString(p.commentsHTML)
	b.WriteString("\n    <div class=\"isu-comment-form\">\n      <form method=\"post\" action=\"/comment\">\n        <input type=\"text\" name=\"comment\">\n        <input type=\"hidden\" name=\"post_id\" value=\"")
	b.WriteString(id)
	b.WriteString("\">\n        <input type=\"hidden\" name=\"csrf_token\" value=\"")
	b.WriteString(p.CSRFToken)
	b.WriteString("\">\n        <input type=\"submit\" name=\"submit\" value=\"submit\">\n      </form>\n    </div>\n  </div>\n</div>")
}

// renderPosts は posts.html 相当（投稿一覧）の HTML を生成する。
func renderPosts(posts []Post) template.HTML {
	var b strings.Builder
	b.Grow(8192) // バッファ倍化の memmove を避けるため先に確保
	b.WriteString("<div class=\"isu-posts\">\n  ")
	for _, p := range posts {
		b.WriteString("\n  ")
		renderPostInto(&b, p)
		b.WriteString("\n  ")
	}
	b.WriteString("\n</div>")
	return template.HTML(b.String())
}

// renderPost は単一投稿（post_id.html 用）の HTML を生成する。
func renderPost(p Post) template.HTML {
	var b strings.Builder
	b.Grow(4096)
	renderPostInto(&b, p)
	return template.HTML(b.String())
}

// renderCommentsSegment は post.html のコメント部分（isu-comment divs）の HTML を
// 生成する。renderPostInto が p.commentsHTML として挿入する。
func renderCommentsSegment(comments []Comment) string {
	var b strings.Builder
	for _, c := range comments {
		b.WriteString("\n    <div class=\"isu-comment\">\n      <a href=\"/@")
		b.WriteString(c.User.AccountName)
		b.WriteString(`" class="isu-comment-account-name">`)
		b.WriteString(c.User.AccountName)
		b.WriteString("</a>\n      <span class=\"isu-comment-text\">")
		b.WriteString(html.EscapeString(c.Comment))
		b.WriteString("</span>\n    </div>\n    ")
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
	// 描画済みコメント HTML キャッシュ（およびセッション）も初期化のため flush する。
	memcacheClient.FlushAll()
	bumpPageVersion() // 一覧キャッシュも世代を上げて無効化する
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
	csrf := getCSRFToken(r)

	// 全ユーザ共通の投稿一覧 HTML をバージョン付きでキャッシュする。CSRF はプレース
	// ホルダで描画しておき、配信時にリクエストの CSRF トークンへ置換する。これで
	// 大半の GET / が DB/描画を行わず、キャッシュ済みバイト列の置換だけで応答できる。
	cached, err := indexPostsHTML(ctx)
	if err != nil {
		log.Print(err)
		return
	}
	// 配信時にリクエストの CSRF トークンへ置換する。
	postsHTML := strings.ReplaceAll(cached, csrfPlaceholder, csrf)

	tmplIndex.Execute(w, struct {
		PostsHTML template.HTML
		Me        User
		CSRFToken string
		Flash     string
	}{template.HTML(postsHTML), me, csrf, getFlash(w, r, "notice")})
}

func getAccountName(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	accountName := r.PathValue("accountName")
	user := User{}

	err := db.GetContext(ctx, &user, "SELECT * FROM `users` WHERE `account_name` = ? AND `del_flg` = 0", accountName)
	if err != nil {
		log.Print(err)
		return
	}

	if user.ID == 0 {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	results := []Post{}

	err = db.SelectContext(ctx, &results, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` WHERE `user_id` = ? ORDER BY `created_at` DESC LIMIT 20", user.ID)
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

	tmplUser.Execute(w, struct {
		Posts          []Post
		User           User
		PostCount      int
		CommentCount   int
		CommentedCount int
		Me             User
	}{posts, user, postCount, commentCount, commentedCount, me})
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

	results := []Post{}
	// Single-table query (see getIndex): backward scan of posts(created_at) with
	// LIMIT, then makePosts filters deleted users; postsFetchMargin over-fetches.
	err = db.SelectContext(ctx, &results, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` FORCE INDEX(idx_created_at) WHERE `created_at` <= ? ORDER BY `created_at` DESC LIMIT ?", t.Format(ISO8601Format), postsFetchMargin)
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

	results := []Post{}
	err = db.SelectContext(ctx, &results, "SELECT `id`, `user_id`, `body`, `mime`, `created_at`, `comment_count` FROM `posts` WHERE `id` = ?", pid)
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

	tmplPostID.Execute(w, struct {
		Post Post
		Me   User
	}{p, me})
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
	bumpPageVersion() // 新規投稿で一覧が変わるのでキャッシュ世代を上げる

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
	bumpPageVersion() // コメント追加で一覧の表示が変わるのでキャッシュ世代を上げる

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
	bumpPageVersion() // BAN で一覧から消える投稿があるのでキャッシュ世代を上げる

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
