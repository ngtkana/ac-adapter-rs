# libs/ の API 設計規約

`libs/` 配下の各クレートは独立だが、利用者が複数クレートを横断して読み書きするため、
同じ役割のAPIは同じ名前・同じ形にする。新規クレート追加・既存クレート変更時は以下に従う。

## 1. コンストラクタ

- `new(len: usize)`: 長さのみ指定し、単位元・デフォルト値で初期化する
- `from_slice(values: &[T])`: 借用スライスから構築する（内部でコピーが必要なら複製する）
- `from_vec(values: Vec<T>)`: 所有権を受け取り、コピーを避けて構築する
- `new` に初期値を渡す設計にしない（`new(len)` と `new(values)` が別クレートで衝突すると、
  シグネチャだけでは意味が判別できなくなる）

**根拠**: segtree crateの`from_len`/`new`、sparse_table crateの`new`/`clone_from_slice`は
それぞれ別の名前分けをしており、クレートをまたぐと`new`の意味が読めなくなっていた。

## 2. モノイド結合演算

- 2値を結合するメソッドは `op(lhs: &Value, rhs: &Value) -> Value` に統一する
- トレイト名は `Op`（単数形）
- 単位元は `identity() -> Value`
- 逆演算など`op`以外の別演算を追加する場合は、`op`との混同を避けられる具体名（例: `sub`）を使う

**根拠**: 同じ「2値を結合する」操作が `mul`（segtree, sparse_table, tree_fold, link_cut_tree）、
`add`（fenwick）、`op`（lazy_segtree, swag, dual_segtree）と割れていた。`mul`/`add`は特定の演算
（乗算・加算）を連想させ、任意モノイドの結合という意味と食い違う。

## 3. グラフの辺

- 辺の始点・終点を表す引数名・フィールド名は `from` / `to` に統一する
- `src`/`tar`、`u`/`v` など他の略記は使わない

**根拠**: dinic（`from`/`to`）、max_flow（`src`/`tar`）、mincost_flow（`u`/`v`）で3通りに割れていた。

## 4. 区間の受け取り方

- 区間を受け取るAPIは可能な限り `impl RangeBounds<usize>` で受ける
- `RangeTo<usize>` や `Range<usize>` 固定にしてよいのは、演算の意味論上それ以外の区間形状を
  サポートできない場合のみ（例: 減算のないモノイドの前置和は `RangeTo` しか意味を持たない）。
  その場合は doc コメントに理由を明記する

## 5. 疎な（動的確保・キー圧縮）構造の1点更新

- あらかじめ要素が存在するとは限らない構造（未確保ノードを持つ木、キー未登録の可能性がある
  構造など）への1点更新は、クロージャを渡す `apply(key, f: impl FnMut(&mut Value))` に統一する
- 要素の存在があらかじめ保証されている構造（固定長配列バックエンドなど）では、
  RAIIガードを返す `entry(index) -> Entry` を使う（`Deref`/`DerefMut`/`Drop`で経路再計算する形）

## 適用例

このルールに沿って以下のクレートを改修した（詳細は関連PR参照）:
segtree, sparse_segtree, sparse_table, tree_fold, link_cut_tree, fenwick, dual_segtree,
max_flow, mincost_flow

## 未整備の一貫性課題

このルールでカバーしていない一貫性課題はissueで管理する。新しい不統一に気づいたら、
その場で直さず、まずissue化してこのファイルへの追記を検討する。
