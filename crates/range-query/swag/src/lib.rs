//! Data structures by SWAG (sliding windown aggregation).
//!
//! 実装は 2 種類あります。用途に合わせて好きな方を選ぶと良いです。
//!
//!
//! # Fold 可能キューデータ構造 [`SwagQueue`]
//!
//! [`Vec`] を 2 つ持ちます。後半はそのままの形で持っていますが、前半は prefix aggregation の形で持っています。
//! そのため [`pop`](SwagQueue::pop) をしても要素を返すことができず、`Option<()>`
//! の形で返ってきます。[`fold`](SwagQueue::fold) を達成するために、後半の full aggregation を管理しています。
//!
//! ## インターフェース
//!
//! メソッドは（[`pop`](SwagQueue::pop) が要素を返さないことを除けば） foldable queue
//! データ構造らしいお名前にしてあります。
//!
//! - [`new`](SwagQueue::new)
//! - [`push`](SwagQueue::push)
//! - [`pop`](SwagQueue::pop)
//! - [`fold`](SwagQueue::fold)
//!
//!
//! # Range aggregation データ構造、[`SwagSpan`]
//!
//! オブジェクトが `&[T]` を所有し、今指している範囲を [`Range`](std::ops::Range) で管理します。前半の prefix
//! aggregation は [`SwagQueue`] 同様、[`Vec`] で管理しますが、後半についてはもとのスライスを見ればよいですから
//! full aggregation しか管理しません。
//!
//! ## インターフェース
//!
//! `push`, `pop` をするのではなく、[`fold`](SwagSpan::fold) をするたびに range
//! を指定し、可能ならばそこに到達するまで `push` と `pop`
//! を繰り返す、無理ならばパニックという方式を採っています。
//!
//! - [`new`](SwagSpan::new)
//! - [`fold`](SwagSpan::fold)
//!
mod swag_queue;
mod swag_span;

pub use swag_queue::SwagQueue;
pub use swag_span::SwagSpan;
