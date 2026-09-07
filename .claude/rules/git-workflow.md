# Git ワークフロー

**ルール**: コード変更は新しい branch + worktree + PR で行う

**適用範囲**: AI によるコード変更全般（バグ修正、機能追加、リファクタリング含む）

**手順**:
1. `git-workflow:create-worktree` で新しい branch の worktree を作成
2. worktree 内で変更
3. `git-workflow:pr-and-cleanup` で PR 作成 + worktree cleanup

**禁止**:
- `main` への直接コミット
- 既存の作業ブランチへの無断コミット（ユーザー指示がある場合を除く）

**Why**: 変更を隔離し、レビュー可能な単位で提出するため

**How to apply**: コード変更を伴うタスクを始める前に worktree 作成から開始する
