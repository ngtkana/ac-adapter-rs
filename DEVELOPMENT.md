# 開発

```sh
cargo make hooks-install  # pre-commitフック（clippy/doctest/test/doc生成）
```

`cargo-make` / `cargo-nextest` が必要。バージョンは [`.github/actions/setup-rust/action.yml`](.github/actions/setup-rust/action.yml) 参照。

## タスク

| コマンド | 内容 |
|---|---|
| `cargo make check` | ビルドチェック |
| `cargo make test` | テスト（nextest） |
| `cargo make test-doc` | doctest |
| `cargo make clippy` | lint |
| `cargo make doc` | ドキュメント生成 → `docs/` |
| `cargo make dev` | `docs/` をローカルサーブ |

CIも同じタスクを実行し、`main` 更新時に `docs/` をGitHub Pagesへデプロイ。

## 構成

| パス | 内容 |
|---|---|
| `libs/*` | 各クレート本体 |
| `bundler` | acbundle実装。[bundler/README.md](bundler/README.md) |
| `snippetter` | `docs/dependencies.js`（カタログサイトの検索・依存情報）を生成 |
| `benches` | criterionベンチマーク。標準は [`.claude/rules/benchmark-standards.md`](.claude/rules/benchmark-standards.md) |
| `stats/*` | ベンチマーク結果の統計処理 |
| `docs/` | GitHub Pages公開物。`cargo make doc` の生成先（直接編集しない） |
| `contents/` | `docs/` のソース一式 |

## doc生成

`cargo make doc`: snippetterが`docs/dependencies.js`生成 → `contents/*`を`docs/`へコピー → `cargo doc`でrustdoc生成し`docs/rustdoc/`へ。

doc commentの書き方は [write-doc-comments](.claude/skills/write-doc-comments/SKILL.md)、移行状況は [DOC_MIGRATION.md](DOC_MIGRATION.md)。
