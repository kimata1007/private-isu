-- 性能改善用インデックス（再起動後も維持される）
ALTER TABLE comments ADD INDEX idx_post_id_created (post_id, created_at);
ALTER TABLE comments ADD INDEX idx_user_id (user_id);
ALTER TABLE posts ADD INDEX idx_created_at (created_at);
ALTER TABLE posts ADD INDEX idx_user_id_created (user_id, created_at);
