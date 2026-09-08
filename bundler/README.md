# acbundle

指定クレート（+内部依存）をAtCoder提出用に1ファイルへ展開するツール。

## 使い方

```sh
acbundle fp_fps dinic > bundled.rs         # 複数クレート、dedup付き
acbundle fp_fps --skip-from src/main.rs    # 既存ファイル（foldマーカーで判別）に追記
acbundle fp_fps --keep-docs --keep-tests   # doc/テストを保持（デフォルトは除去）
```

## インストール

```sh
cargo make install-acbundle
```

表示される `export AC_ADAPTER_RS_ROOT=...` をrcファイルに追記。

## シェル補完

`echo $SHELL` で確認し、該当する方だけ設定:

```sh
# zsh
mkdir -p ~/.zsh/completions
cp bundler/completions/_acbundle ~/.zsh/completions/
# ~/.zshrc に一度だけ: fpath=(~/.zsh/completions $fpath); autoload -Uz compinit && compinit

# bash（AC_ADAPTER_RS_ROOT export済み前提）
echo 'source "$AC_ADAPTER_RS_ROOT/bundler/completions/acbundle.bash"' >> ~/.bashrc
```

## Neovim

`:AcBundle` でクレートを選び、バッファ末尾に挿入（重複回避込み）。

```lua
-- lazy.nvim
{ "ngtkana/ac-adapter-rs" }
```

```lua
-- ネイティブpackage: ~/.config/nvim/pack/plugins/start/acbundle-loader/plugin/acbundle.lua
local root = os.getenv("AC_ADAPTER_RS_ROOT")
if root and root ~= "" then
  local f = root .. "/nvim/plugin/acbundle.lua"
  if vim.fn.filereadable(f) == 1 then
    vim.opt.rtp:append(root .. "/nvim")
    dofile(f)
  end
end
```

## アンインストール

```sh
cargo make uninstall-acbundle
```

rcファイル・補完スクリプトは手動削除。
