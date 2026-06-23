# private-isu webapp

[catatsuy/private-isu](https://github.com/catatsuy/private-isu) のアプリケーション実装一式（performance tuning 用作業リポジトリ）。

## 構成

| ディレクトリ | 内容 |
|---|---|
| `webapp/golang` | Go 実装 |
| `webapp/ruby` | Ruby 実装（オリジナルの既定） |
| `webapp/php` | PHP 実装 |
| `webapp/python` | Python 実装 |
| `webapp/node` | Node.js 実装 |
| `webapp/sql` | スキーマ・初期データ |
| `webapp/public` | 静的ファイル |
| `webapp/etc/nginx` | nginx 設定 |

## DB 接続

環境変数で設定する（リポジトリには含めない）。

```
ISUCONP_DB_USER=...
ISUCONP_DB_PASSWORD=...
ISUCONP_DB_NAME=...
```
