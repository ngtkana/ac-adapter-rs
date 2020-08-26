#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! 標準入力を楽にします。
//!
//! # 特徴
//!
//! Rust 1.17.0 でコンパイルができます。（本質）

use ::std::collections::VecDeque;

/// 標準入力を仲介します。
///
/// # Examples
///
/// ```
/// use ngtio::Buffer;
/// let mut buffer = Buffer::new();
/// ```
pub struct Buffer {
    buf: VecDeque<String>,
}

impl Buffer {
    /// 新しく作ります。
    ///
    /// # Examples
    ///
    /// ```
    /// use ngtio::Buffer;
    /// let mut buffer = Buffer::new();
    /// ```
    pub fn new() -> Self {
        Self {
            buf: VecDeque::new(),
        }
    }

    fn load(&mut self) {
        while self.buf.is_empty() {
            let mut s = String::new();
            let length = ::std::io::stdin().read_line(&mut s).unwrap();
            if length == 0 {
                break;
            }
            self.buf.extend(s.split_whitespace().map(|s| s.to_owned()));
        }
    }

    /// トークンをポップします。
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use ngtio::Buffer;
    /// let mut buffer = Buffer::new();
    /// let x = buffer.string();
    /// ```
    pub fn string(&mut self) -> String {
        self.load();
        self.buf
            .pop_front()
            .unwrap_or_else(|| panic!("入力が終了したのですが。"))
    }

    /// トークンをポップして、char 型にパースです。
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use ngtio::Buffer;
    /// let mut buffer = Buffer::new();
    /// let x = buffer.char();
    /// ```
    pub fn char(&mut self) -> char {
        let string = self.string();
        let mut chars = string.chars();
        let res = chars.next().unwrap();
        assert!(
            chars.next().is_none(),
            "char で受け取りたいのも山々なのですが、さては 2 文字以上ありますね？"
        );
        res
    }

    /// トークンをパースします。
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use ngtio::Buffer;
    /// let mut buffer = Buffer::new();
    /// let x = buffer.read::<usize>();
    /// ```
    pub fn read<T: ::std::str::FromStr>(&mut self) -> T
    where
        <T as ::std::str::FromStr>::Err: ::std::fmt::Debug,
    {
        self.string()
            .parse::<T>()
            .expect("Failed to parse the input.")
    }

    /// トークンを `len` 回パースして、`Vec` に入れます。
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use ngtio::Buffer;
    /// let mut buffer = Buffer::new();
    /// let x = buffer.read_vec::<u32>();
    /// ```
    pub fn read_vec<T: ::std::str::FromStr>(&mut self, len: usize) -> Vec<T>
    where
        <T as ::std::str::FromStr>::Err: ::std::fmt::Debug,
    {
        (0..len).map(|_| self.read::<T>()).collect()
    }
}

macro_rules! define_primitive_reader {
    ($($ty:tt,)*) => {
        impl Buffer {
            $(
                /// トークンをパースします。
                ///
                #[inline]
                pub fn $ty(&mut self) -> $ty {
                    self.read::<$ty>()
                }
            )*
        }
    }
}

define_primitive_reader! {
    u8, u16, u32, u64, usize,
    i8, i16, i32, i64, isize,
}

impl Default for Buffer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
