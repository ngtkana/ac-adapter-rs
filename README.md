# AC Adapter

![AC Adapter Logo](contents/logo.png)

## 目次

- [API ドキュメント](#api-ドキュメント)
- [開発](#開発)
- [提出用バンドル (acbundle)](#提出用バンドル-acbundle)
  - [インストール](#インストール)
  - [使い方](#使い方)
  - [既存ファイルへの追記](#既存ファイルへの追記)
  - [シェル補完](#シェル補完)
  - [Neovim](#neovim)
  - [アンインストール](#アンインストール)

## API ドキュメント

https://ngtkana.github.io/ac-adapter-rs/

## 開発

```sh
cargo make hooks-install  # pre-commitフック導入
```

`cargo-make` / `cargo-nextest` が必要（バージョンは `.github/actions/setup-rust/action.yml` 参照）。コミット前に fmt / clippy / doctest / test / doc生成を実行。

## 提出用バンドル (acbundle)

指定クレート（と内部依存）を1つのAtCoder提出用スニペットに展開するツール。

### インストール

```sh
cargo make install-acbundle
```

`$SHELL` から判定した rc ファイルへ追記すべき `export AC_ADAPTER_RS_ROOT=...` 行が実パス入りで表示されるので、コピーして追記。

### 使い方

```sh
acbundle fp_fps dinic > bundled.rs   # 複数クレートを一度に、dedup付きで
```

### 既存ファイルへの追記

バンドル済みクレート（`// <name> {{{` fold マーカーで判別）は `--skip-from` で除外:

```sh
acbundle fp_fps --skip-from src/main.rs > new_snippet.rs
```

### シェル補完

`bundler/completions/` 以下、自分のシェルに合う方だけ設定（`echo $SHELL` で確認）:

```sh
# zsh
mkdir -p ~/.zsh/completions
cp bundler/completions/_acbundle ~/.zsh/completions/
# ~/.zshrc に一度だけ追記: fpath=(~/.zsh/completions $fpath); autoload -Uz compinit && compinit

# bash（$AC_ADAPTER_RS_ROOT が先に export 済みである前提）
echo 'source "$AC_ADAPTER_RS_ROOT/bundler/completions/acbundle.bash"' >> ~/.bashrc
```

### Neovim

`nvim/plugin/acbundle.lua` が `:AcBundle` を提供。クレートを選ぶと、現在のバッファ末尾に（`--skip-from` で重複回避しつつ）挿入する。

lazy.nvim:

```lua
{ "ngtkana/ac-adapter-rs" }
```

ネイティブpackage（vim8 packages）を使う場合は、リポジトリ本体をクローンし直さず `$AC_ADAPTER_RS_ROOT`（インストール時に export 済み）を実行時に読んでランタイムパスへ追加するだけの薄いローダーを置く。dotfilesをリポジトリで同期している場合でも絶対パスを一切書かないので、そのままコミットして良い:

```lua
-- ~/.config/nvim/pack/plugins/start/acbundle-loader/plugin/acbundle.lua
local root = os.getenv("AC_ADAPTER_RS_ROOT")
if not root or root == "" then
  return
end

local plugin_file = root .. "/nvim/plugin/acbundle.lua"
if vim.fn.filereadable(plugin_file) == 1 then
  vim.opt.rtp:append(root .. "/nvim")
  dofile(plugin_file)
end
```

### アンインストール

```sh
cargo make uninstall-acbundle
```

補完スクリプト・rcファイルへの追記は手動で削除。
