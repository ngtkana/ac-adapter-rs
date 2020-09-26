#![warn(missing_docs)]

//! 入出力を支援します。
//!
//! TODO: lazy_static への依存を排除します。（超重要）
//!
//! 入力については [`i`] モジュール、出力については [`o`] モジュール（comming
//! soon!）のドキュメントをご覧いただけるとです。
//!
//! [`i`]: i.html
//! [`o`]: o.html

/// 入力を司ります。
pub mod i;

#[macro_use]
extern crate doc_comment;

/// たいせつ〜な〜も〜の〜は〜〜〜 ぜんぶこ〜こ〜に〜あ〜る〜〜〜
pub mod prelude {
    pub use super::i::{reader, Parser, ParserTuple, RawTuple, Token, Usize1};
}
