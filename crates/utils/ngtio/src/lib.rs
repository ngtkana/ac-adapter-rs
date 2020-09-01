#![warn(missing_docs)]

//! 標準入力を楽にします。

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

    /// トークンをポップして `Vec<char>` に変換です。
    pub fn string_char_vec(&mut self) -> Vec<char> {
        let s = self.string();
        s.chars().collect::<Vec<_>>()
    }

    /// トークンをポップして `Vec<char>` に変換して長さを検査です。
    pub fn string_char_vec_trusted_len(&mut self, len: usize) -> Vec<char> {
        let s = self.string();
        let s = s.chars().collect::<Vec<_>>();
        assert_eq!(s.len(), len, "あら、思ったのと長さ違いますね……");
        s
    }

    /// トークンをポップして、char 型にパースです。
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
