#!/usr/bin/env bash
# gh pr create が成功した直後に、pr-workflow.md に従うよう本体へリマインドする。
set -euo pipefail

input=$(cat)

command=$(echo "$input" | jq -r '.tool_input.command // empty' 2>/dev/null || true)
stdout=$(echo "$input" | jq -r '.tool_response.stdout // empty' 2>/dev/null || true)

# gh pr create の他、PR本文にコードを含む場合の代替手段（gh api .../pulls）もカバーする
if ! echo "$command" | grep -qE '(^|[;&|[:space:]])gh[[:space:]]+(pr[[:space:]]+create|api[[:space:]]+[^ ]*pulls)'; then
  exit 0
fi

pr_url=$(echo "$stdout" | grep -oE 'https://github\.com/[^ ]+/pull/[0-9]+' | head -n1 || true)

if [[ -z "$pr_url" ]]; then
  # gh pr create を含むが成功したPR URLが出力に見当たらない（失敗・dry-run等）場合は何もしない
  exit 0
fi

context="PR ${pr_url} が作成されました。.claude/rules/pr-workflow.md に従い、(1) 独立したレビューsubagentを起動して変更内容をレビューし、(2) このセッション内でPRのステータス（コンフリクト・新規コメント・マージ/クローズ）を数回に分けて確認してください。"

jq -n --arg ctx "$context" '{
  hookSpecificOutput: {
    hookEventName: "PostToolUse",
    additionalContext: $ctx
  }
}'
