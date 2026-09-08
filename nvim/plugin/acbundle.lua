-- :AcBundle — クレートを選んでバンドル結果を現在のバッファ末尾に挿入する。
-- 要 acbundle（cargo make install-acbundle）と AC_ADAPTER_RS_ROOT。

local function bundle()
  local list = vim.fn.system({ "acbundle", "--list-crates" })
  if vim.v.shell_error ~= 0 then
    vim.notify(
      "acbundle: crate一覧の取得に失敗しました（インストール済みか、AC_ADAPTER_RS_ROOTの設定を確認してください）",
      vim.log.levels.ERROR
    )
    return
  end

  local crates = vim.split(vim.trim(list), "\n")
  vim.ui.select(crates, { prompt = "acbundle: crate名" }, function(choice)
    if not choice then
      return
    end

    local bufname = vim.api.nvim_buf_get_name(0)
    if bufname == "" then
      vim.notify("acbundle: 先にバッファをファイルへ保存してください", vim.log.levels.ERROR)
      return
    end
    if vim.bo.modified then
      vim.cmd.write()
    end

    local output = vim.fn.system({ "acbundle", choice, "--skip-from", bufname })
    if vim.v.shell_error ~= 0 then
      vim.notify("acbundle: " .. output, vim.log.levels.ERROR)
      return
    end

    local lines = vim.split(output, "\n", { trimempty = true })
    vim.api.nvim_buf_set_lines(0, -1, -1, false, lines)
  end)
end

vim.api.nvim_create_user_command("AcBundle", bundle, {
  desc = "acbundle でクレートをバンドルし、バッファ末尾に挿入する",
})
