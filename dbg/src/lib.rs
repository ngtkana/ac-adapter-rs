//! [`Debug`] トレイトを実装した便利なラッパーをたくさん提供して行きたい気持ちです。
//!
//! [`Debug`]: https://doc.rust-lang.org/std/fmt/trait.Debug.html

#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

use std::fmt::{Debug, Formatter};

/// `&[<Vec<T>]` を、表形式で列に添字をつけて出力できます。
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

/// `&[<Vec<bool>]` を、`'.','#'` grid 形式で、列に添字をつけて出力できます。
#[derive(Clone)]
pub struct BooleanTable<'a>(pub &'a [Vec<bool>]);
impl<'a> Debug for BooleanTable<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for i in 0..self.0.len() {
            writeln!(f, "{:2} | {:?}", i, BooleanSlice(&self.0[i]))?;
        }
        Ok(())
    }
}

/// `&[bool]` を `'.','#'` の列で出力できます。末尾に改行はありません。
#[derive(Clone)]
pub struct BooleanSlice<'a>(pub &'a [bool]);
impl<'a> Debug for BooleanSlice<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|&b| if b { '#' } else { '.' })
                .collect::<String>()
        )?;
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
