# PRオープン後の運用ルール

`gh pr create` でPRを作成したら、同一セッション内で以下を自動的に行う（ユーザーに指示されなくてもよい）。

## 1. レビューsubagentの起動

- 独立した視点を得るため、fork（コンテキスト継承）ではなく新規general-purpose agentでレビューさせる
- 変更内容に応じてレビュー観点を選ぶ（例: UI/デザイン変更ならUX・Webの慣習・アクセシビリティ、ロジック変更なら正確性・エッジケース）
- レビューで見つかった指摘は確認の上で反映する。スコープ外の指摘は [[issue-workflow]] に従いissue化する
- レビュー結果は `gh pr comment <番号> --body-file <ファイル>`（本文にコードを含む場合は[[pr_and_cleanup_backtick_bug]]と同様の理由でヒアドキュメント直書きを避けファイル経由にする）でPRにコメントする
  - 指摘の有無にかかわらずコメントする（「指摘なし」も結果として記録する）
  - 各指摘について、反映したか・見送ったか（理由付き）・issue化したか（issue番号）を明記する

## 2. PRステータスの監視（セッション内のみ）

- 監視はセッション内で完結させればよい。永続化（cron等）は不要——見張るのはオープン直後の短時間で十分という前提
- `gh pr view <番号> --json mergeable,mergeStateStatus,statusCheckRollup,comments,reviews,state` を数回（間隔を空けて）確認し、以下を検知したらユーザーに知らせる
  - コンフリクト発生（`mergeable` が `CONFLICTING`）
  - 新規コメント・レビューコメント
  - マージ/クローズなどの状態変化
- コンフリクトを検知しても自動で解消しない。ユーザーに状況を伝えて方針を確認する
- `mergeable` が `MERGEABLE` かつ `statusCheckRollup` の全項目の `conclusion` が `SUCCESS`/`SKIPPED`（`IN_PROGRESS` が残っていない）になったら、ユーザーにmerge指示を促す（自動でmergeしない）
  - ユーザーからmerge指示を受けたら `gh pr merge <番号> --squash --delete-branch` を実行する（このリポジトリはmerge/squash/rebaseを全て許可しているため、方式を明示する。過去の運用実績もsquash）
  - 続けてworktreeのcleanupを行う。`git-workflow:pr-and-cleanup` スキルは使わず、[[git-workflow]] と同様に手動の `git worktree remove ~/worktrees/<repo>/<branch>` で行う
