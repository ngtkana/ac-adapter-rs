# Git ワークフロー

**ルール**: リポジトリ内のファイル変更は、コード・ドキュメント・設定ファイルを問わず、必ず新しい branch + worktree + PR で行う

**適用範囲**: AI によるファイル変更全般（バグ修正、機能追加、リファクタリング、ドキュメント追記、`.claude/rules/` 等のルールファイル更新を含む）。1ファイルの軽微な追記であっても例外にしない

**手順**:
1. worktree作成（手動コマンドを使う。理由は下記Why参照）:
   ```
   REPO=$(basename "$(git rev-parse --show-toplevel)")
   git worktree add -b <branch-name> ~/worktrees/${REPO}/<branch-name> main
   ```
2. worktree 内で変更
3. `gh pr create` で PR 作成。マージ後は `git worktree remove ~/worktrees/${REPO}/<branch-name>` で cleanup
   （UI目視確認待ちの場合は [[ui-visual-verification]] 手順6が優先、cleanupを保留する）

**禁止**:
- `main` への直接コミット
- 既存の作業ブランチへの無断コミット（ユーザー指示がある場合を除く）
- リポジトリ内（`.worktrees/` 等）への worktree 作成

**Why**: 変更を隔離し、レビュー可能な単位で提出するため。`git-workflow:create-worktree` / `git-workflow:pr-and-cleanup` プラグインは `.worktrees/` 固定でリポジトリ内にしか作れない実装のため使わない（ユーザーのグローバル設定に準拠）

**How to apply**: ファイル変更を伴うタスクを始める前に、内容の大小によらず worktree 作成から開始する
