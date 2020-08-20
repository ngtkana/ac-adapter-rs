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

    fn pop_token(&mut self) -> Option<String> {
        self.load();
        self.buf.pop_front()
    }

    /// パースします。
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
        self.pop_token()
            .expect("Reached the end of the input.")
            .parse::<T>()
            .expect("Failed to parse the input.")
    }
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
