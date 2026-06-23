-- コメント数を posts に非正規化（COUNT クエリを排除）
ALTER TABLE posts ADD COLUMN comment_count INT NOT NULL DEFAULT 0;
UPDATE posts p
  LEFT JOIN (SELECT post_id, COUNT(*) cnt FROM comments GROUP BY post_id) c
  ON p.id = c.post_id
  SET p.comment_count = COALESCE(c.cnt, 0);

-- 画像は filesystem + nginx 配信へ移行済みのため imgdata blob を削除。
-- 事前に全画像が public/image にファイルとして存在することが前提。
-- ALGORITHM=COPY で物理的にリビルドしてディスク/行サイズを回収する。
ALTER TABLE posts DROP COLUMN imgdata, ALGORITHM=COPY;
