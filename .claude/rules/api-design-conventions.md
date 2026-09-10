# API設計規約

## panic と Option/Result の使い分け

**ルール**: 利用者のバグ（契約違反）は panic、正当な入力に対する結果なしは `Option`/`Result`。

| 状況 | 例 | 返し方 |
|---|---|---|
| 契約違反（範囲外アクセスなど） | `segtree.fold(10..20)` で `len() == 5` | panic |
| 正当な入力での結果なし | 空区間の fold で `Op::identity` が定義できない | `Option`/`Result` |
| `get` 系の checked accessor | `tree.get(i)` で `i >= len()` | `Option`（標準ライブラリ `slice::get` に倣う） |

**注意**: 同じ「範囲外インデックス」でもメソッドの性質で扱いが変わる。`get`/`get_mut` のような「安全に存在確認したい」用途の checked accessor は `Option` を返す。`insert`/`remove`/`fold`（range指定）のような通常の操作メソッドは、範囲外指定を契約違反として panic する。命名（`get` はNoneを許容、それ以外は契約違反）で意図を示す。

**Why**: 契約違反は呼び出し側のバグであり早期に気付かせるべき。結果なしは正常系の一部であり呼び出し側にハンドリングさせる。

**How to apply**: 新規API設計時、「この状況は入力データ次第で誰でも起こりうるか」を基準に判断する。起こりうるなら `Option`/`Result`、起こりえない（契約を守れば発生しない）なら panic。ただし `get` 系のメソッド名を選ぶ場合は、標準ライブラリの慣習に合わせて `Option` を返す。

## panic メッセージの書式

**ルール**: 範囲外アクセス等の panic は、標準ライブラリの slice index panic に倣い、専用のプライベート関数を用意して呼び出す。

**命名規則**: `<crate>_<state>_fail(..) -> !`（例: `dual_segtree_index_out_of_range_fail`, `dual_segtree_index_order_fail`）

**参考実装**: `libs/dual_segtree/src/lib.rs`, `libs/splay_tree/src/lib.rs`

**Why**: `assert!` 直書きだとメッセージがクレートごとにばらつく。専用関数に切り出すことで、メッセージの一貫性と可読性を保てる。

**How to apply**: 範囲外アクセスなど契約違反による panic を新規実装する際は、専用の `fn ..._fail(..) -> !` を用意する。単純な前提条件チェック（例: 型パラメータの制約）には `assert!` 直書きで構わない。
