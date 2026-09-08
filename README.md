# AC Adapter

![AC Adapter Logo](contents/logo.png)

## API Document

https://ngtkana.github.io/ac-adapter-rs/

## Development

Install local pre-commit hooks:

```sh
cargo make hooks-install
```

Requires `cargo-make` and `cargo-nextest` (see `.github/actions/setup-rust/action.yml` for the versions CI uses). Runs `cargo fmt --check`, `clippy`, doctests, the full test suite, and doc generation before each commit — all confirmed lightweight (sub-second on an incrementally-built tree).

## 提出用バンドル

`libbundle` は指定したクレート（とその内部依存）を1つの AtCoder 提出用スニペットに展開します。

初回のみインストール:

```sh
cargo make install-libbundle
```

実行後、シェルの rc ファイルに追記すべき `export AC_ADAPTER_RS_ROOT=...` 行が実際のパス入りで表示されるので、それをコピーして `~/.zshrc` 等に追記してください。

追記後はどこからでも（例えば競プロ用の別リポジトリから）実行できます:

```sh
libbundle fp_fps dinic > bundled.rs   # 複数クレートを一度に、dedup付きで
```

既に別のファイルにバンドル済みのクレートがある場合（このツールが出力する `// <name> {{{` の fold マーカーで判別）、`--skip-from` で再展開を防げます:

```sh
libbundle fp_fps --skip-from src/main.rs > new_snippet.rs
```

クレート名のシェル補完（`bundler/completions/`）:

```sh
# zsh
mkdir -p ~/.zsh/completions
cp bundler/completions/_libbundle ~/.zsh/completions/
# ~/.zshrc に一度だけ追記: fpath=(~/.zsh/completions $fpath); autoload -Uz compinit && compinit

# bash（$AC_ADAPTER_RS_ROOT が先に export 済みである前提）
echo 'source "$AC_ADAPTER_RS_ROOT/bundler/completions/libbundle.bash"' >> ~/.bashrc
```


