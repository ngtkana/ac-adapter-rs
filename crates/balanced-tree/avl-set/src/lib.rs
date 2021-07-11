//! 中間節点にも要素を持つタイプの AVL 木で、集合系データ構造を実現するものです。
//!
//!
//! ---
//!
//! # TODO
//!
//! - マージ・スプリット（これができると O ( N ) 構築も簡単にかけますね。）
//! - （できれば）イテレータ（これ unsafe しないとかなり辛いんですよね。）
//!
mod avltree;
mod map;
mod set;

pub use self::{map::AvlMap, set::AvlSet};
