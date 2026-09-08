# 開発

## セットアップ

```sh
cargo make hooks-install  # pre-commitフック導入
```

`cargo-make` / `cargo-nextest` が必要（バージョンは [`.github/actions/setup-rust/action.yml`](.github/actions/setup-rust/action.yml) 参照）。

## よく使うタスク

| コマンド | 内容 |
|---|---|
| `cargo make check` | ビルドチェック |
| `cargo make test` | テスト実行（nextest） |
| `cargo make test-doc` | doctest |
| `cargo make clippy` | lint |
| `cargo make doc` | ドキュメント生成 → `docs/` |
| `cargo make dev` | `docs/` をローカルサーブ（`localhost:8000`） |

pre-commitフックはコミット前に clippy / doctest / test / doc生成を実行（`.githooks/pre-commit`）。CI（[`.github/workflows/rust.yml`](.github/workflows/rust.yml)）も同じタスクを実行し、`main` 更新時に `docs/` を GitHub Pages へデプロイする。

## リポジトリ構成

| パス | 内容 |
|---|---|
| `libs/*` | 各アルゴリズム・データ構造のクレート（公開ライブラリ本体） |
| `bundler` | `acbundle` の実装。使い方は [bundler/README.md](bundler/README.md) |
| `snippetter` | `cargo_metadata` から `docs/dependencies.js`（カタログサイト用の依存関係・検索インデックス）を生成 |
| `benches` | criterionベンチマーク。実装標準は [`.claude/rules/benchmark-standards.md`](.claude/rules/benchmark-standards.md) |
| `stats/*` | ベンチマーク結果の統計処理 |
| `docs/` | GitHub Pagesの公開物（rustdoc + カスタムカタログサイト）。`cargo make doc` の生成先で、直接編集しない |
| `contents/` | `docs/` のソース（`index.html` / `styles.css` / `script.js` / `header.html` / `logo.png`）。`cargo make doc` が `docs/` へコピーする |

## ドキュメント生成の仕組み

`cargo make doc` は以下を順に行う:

1. `snippetter` が各クレートの `lib.rs` 冒頭の doc comment（`//!`）と `Cargo.toml` の依存関係を集め、`docs/dependencies.js` を生成
2. `contents/*` を `docs/` へコピー（カタログサイトの静的資産一式）
3. `cargo doc --workspace --no-deps` で rustdoc を生成し、`docs/rustdoc/` へ配置

doc commentの書き方は [`.claude/skills/write-doc-comments/SKILL.md`](.claude/skills/write-doc-comments/SKILL.md) 参照。旧テンプレートからの移行状況は [`DOC_MIGRATION.md`](DOC_MIGRATION.md)。
