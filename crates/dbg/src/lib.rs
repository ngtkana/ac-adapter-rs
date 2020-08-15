//! [`Debug`] トレイトを実装した便利なラッパーをたくさん提供して行きたい気持ちです。
//!
//! [`Debug`]: https://doc.rust-lang.org/std/fmt/trait.Debug.html

#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

/// 標準の `dbg` マクロとの唯一の違いは、フォーマット指定子 `#` がないことです。
#[macro_export]
macro_rules! lg {
    () => {
        $crate::eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
    };
    ($val:expr) => {
        match $val {
            tmp => {
                eprintln!("[{}:{}] {} = {:?}",
                    file!(), line!(), stringify!($val), &tmp);
                tmp
            }
        }
    };
    ($val:expr,) => { lg!($val) };
    ($($val:expr),+ $(,)?) => {
        ($(lg!($val)),+,)
    };
}

/// [`lg`]: macros.lg.html と似ているのですが、第一引数だけを特別扱いします。
#[macro_export]
macro_rules! msg {
        () => {
            compile_error!();
        };
        ($msg:expr) => {
            $crate::eprintln!("[{}:{}][{}]", $crate::file!(), $crate::line!(), $msg);
        };
        ($msg:expr, $val:expr) => {
            match $val {
                tmp => {
                    eprintln!("[{}:{}][{}] {} = {:?}",
                        file!(), line!(), $msg, stringify!($val), &tmp);
                    tmp
                }
            }
        };
        ($msg:expr, $val:expr,) => { msg!($msg, $val) };
        ($msg:expr, $($val:expr),+ $(,)?) => {
            ($(msg!($msg, $val)),+,)
        };
    }

/// [`Tabular`](struct.Tabular.html) を構築して `eprintlnをします。
#[macro_export]
macro_rules! tabular {
    ($val:expr) => {
        eprintln!(
            "[{}:{}] {}:\n{:?}",
            file!(),
            line!(),
            stringify!($val),
            crate::dbg::Tabular($val)
        );
    };
}

use std::fmt::{Debug, Formatter};

/// `&[<Vec<T>]` を、表形式で列に添字をつけて出力できます。
#[derive(Clone)]
pub struct Tabular<'a, T: Debug>(pub &'a [T]);
impl<'a, T: Debug> Debug for Tabular<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for i in 0..self.0.len() {
            writeln!(f, "{:2} | {:?}", i, &self.0[i])?;
        }
        Ok(())
    }
}

/// `&[<Vec<bool>]` を、`'0','1'` grid 形式で、列に添字をつけて出力できます。
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

/// `&[bool]` を `'0','1'` の列で出力できます。末尾に改行はありません。
#[derive(Clone)]
pub struct BooleanSlice<'a>(pub &'a [bool]);
impl<'a> Debug for BooleanSlice<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|&b| if b { "1 " } else { "0 " })
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
