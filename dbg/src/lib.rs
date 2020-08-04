//! [`Debug`] トレイトを実装した便利なラッパーをたくさん提供して行きたい気持ちです。
//!
//! [`Debug`]: https://doc.rust-lang.org/std/fmt/trait.Debug.html

#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

use std::fmt::{Debug, Formatter};

/// `Vec<Vec<T>>` を、外側の区切りで改行しながら、
/// 列に添字をつけて出力できます。
#[derive(Clone)]
pub struct Tabular<'a, T: Debug>(pub &'a [Vec<T>]);

impl<'a, T: Debug> Debug for Tabular<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for i in 0..self.0.len() {
            writeln!(f, "{:2} | {:?}", i, &self.0[i])?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
