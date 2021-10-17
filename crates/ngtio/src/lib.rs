//! 標準入出力を支援します。
//!
//! TODO: `doctest!` マクロをバンドラで展開したいです。
//! # 基本的な使い方
//!
//! 必要なものは次の 2 つです。
//!
//! - [`BufRead`](std::io::BufRead) を実装した型
//! - [`Parser`] を実装した型の ([`Leaf`], [`VecLen`], [`Tuple`]) のオブジェクト
//!
//! TODO: `Vec` の代わりに [`FromIterator`] を実装した任意の型のオブジェクトにパースしたいです。
//!
//! 使い方は主に 2 とおりです。
//!
//! - [`Parser`] を実装した型を全力で構築して、[`Parser::parse`] を呼びます。
//! - [`Tokenizer`] に実装された便利なメソッド群を使います。
//!
//! 前者は冗長ですが、すべての機能を使えます。後者は短いですが、より限定的な機能しか使えません。
//!
//! 汎用性の観点から、最初の例ではすべて前者の方式で紹介していこうと思います。
//!
//! # Examples
//!
//! まずはプリミティブ型です。
//!
//! ```
//! use ngtio::prelude::*;
//!
//! assert_eq!(u8::leaf().parse(&mut ngtio::with_str("4\n")), 4);
//! ```
//!
//! タプルは [`<(T, U, ..)>::tuple()`](i/trait.ParserTuple.html#method.tuple) か
//! [`<(T, U, ..)>::leaf_tuple()`](i/trait.RawTuple.html#medhot.leaf_tuple) を使いましょう。
//!
//! ```
//! use ngtio::prelude::*;
//! assert_eq!(
//!     (u8::leaf(), char::leaf())
//!         .tuple()
//!         .parse(&mut ngtio::with_str("4 c\n")),
//!     (4, 'c')
//! );
//! assert_eq!(
//!     <(u8, char)>::leaf_tuple().parse(&mut ngtio::with_str("4 c\n")),
//!     (4, 'c')
//! );
//! ```
//!
//! ベクターは [`Parser::vec(len)`](i/trait.Parser.html#method.vec) を使うと良いです。
//!
//! ```
//! use ngtio::prelude::*;
//! assert_eq!(
//!     u8::leaf()
//!         .vec(3)
//!         .parse(&mut ngtio::with_str("0 1 2\n")),
//!     vec![0, 1, 2]
//! );
//! ```
//!
//! これらを組み合わせると、任意の順番でネストすることができます。
//!
//! ```
//! use ngtio::prelude::*;
//! assert_eq!(
//!     (
//!         (
//!             Usize1::leaf(),
//!             u8::leaf().vec(2),
//!             <()>::leaf_tuple(),
//!             (<()>::leaf_tuple(),).tuple().vec(2).vec(1),
//!         )
//!             .tuple()
//!             .vec(2),
//!         char::leaf(),
//!     )
//!         .tuple()
//!         .parse(&mut ngtio::with_str("10 20 30 40 50 60 c\n")),
//!     (
//!         vec![
//!             (9, vec![20, 30], (), vec![vec![((),), ((),)]],),
//!             (39, vec![50, 60], (), vec![vec![((),), ((),)]],),
//!         ],
//!         'c'
//!     )
//! );
//! ```
//!
//! # [`Tokenizer`] 型の便利なメソッド群
//!
//! もちろんプリミティブはパースできます。
//!
//! ```
//! use ngtio::prelude::*;
//! assert_eq!(ngtio::with_str("42\n").parse::<u8>(), 42);
//! ```
//!
//! 各種複合型はこうのように、パーサの構造ごとに専用のメソッドがあります。
//!
//! ```
//! use ngtio::prelude::*;
//!
//! // タプル
//! assert_eq!(ngtio::with_str("42 c\n").tuple::<(u8, char)>(), (42, 'c'));
//!
//! // ベクター
//! assert_eq!(ngtio::with_str("10 20\n").vec::<u8>(2), vec![10, 20]);
//!
//! // 複雑
//! assert_eq!(ngtio::with_str("42 c\n").vec_tuple::<(u8, char)>(1), vec![(42, 'c')]);
//! assert_eq!(
//!     ngtio::with_str("0 1 2 3\n").vec2::<u8>(2, 2),
//!     vec![vec![0, 1], vec![2, 3]]
//! );
//! assert_eq!(
//!     ngtio::with_str("0 1 2 3\n").vec2_tuple::<(u8,)>(2, 2),
//!     vec![vec![(0,), (1,)], vec![(2,), (3,)]]
//! );
//! ```
//!
//! [`FromIterator`]: http://doc.rust-lang.org/std/iter/trait.FromIterator.html
//!
//! [`Parser::parse`]: i/trait.Parser.html#method.parse
//!
//! [`Parser`]: i/trait.Parser.html
//! [`Leaf`]: i/struct.Leaf.html
//! [`VecLen`]: i/struct.VecLen.html
//! [`Tuple`]: i/struct.Tuple.html
//! [`Tokenizer`]: i/struct.Tokenizer.html
//! [`Usize1`]: i/struct.Usize1.html

/// 入力を司ります。
mod i;

pub use self::i::{with_stdin, with_str};

/// たいせつ〜な〜も〜の〜は〜〜〜 ぜんぶこ〜こ〜に〜あ〜る〜〜〜
pub mod prelude {
    pub use super::i::{Parser, ParserTuple, RawTuple, Token, Usize1};
}
