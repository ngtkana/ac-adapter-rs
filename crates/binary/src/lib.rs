//! 二分法をします。

/// 指数部分に使うためのトレイトです。すべての符号なし整数型に実装されています。
pub trait Pow {
    /// `*x != 0`
    fn is_nonzero(&self) -> bool;
    /// `x & 1 == 1`
    fn is_odd(&self) -> bool;
    /// `self >>= 1`
    fn shr1(&mut self);
}

/// 二分法により、`a` を `b` 個 `f` したものを計算します。
///
/// # Requirements
///
/// * `f` が結合的で `init` がその単位元（もしくは `a` の非負冪の上で成り立っていればよいです。）
///
///
/// # Returns
///
/// * `a` を `b` 個 `f` したもの。
///
pub fn binary<T>(mut a: T, mut b: impl Pow, init: T, f: impl Fn(&T, &T) -> T) -> T {
    let mut ans = init;
    while b.is_nonzero() {
        if b.is_odd() {
            ans = f(&ans, &a);
        }
        a = f(&a, &a);
        b.shr1();
    }
    ans
}

macro_rules! impl_pow {
    ($($T:ty),* $(,)?) => {$(
        impl Pow for $T {
            fn is_nonzero(&self) -> bool {
                *self != 0
            }
            fn is_odd(&self) -> bool {
                self & 1 == 1
            }
            fn shr1(&mut self) {
                *self >>= 1;
            }
        }
    )*}
}

impl_pow! {
    u8, u16, u32, u64, u128, usize,
}

#[cfg(test)]
mod tests {
    use {super::binary, test_case::test_case};

    #[test_case(0 => "".to_owned())]
    #[test_case(1 => "abc".to_owned())]
    #[test_case(2 => "abcabc".to_owned())]
    #[test_case(3 => "abcabcabc".to_owned())]
    #[test_case(4 => "abcabcabcabc".to_owned())]
    #[test_case(5 => "abcabcabcabcabc".to_owned())]
    fn test_cat(n: u32) -> String {
        binary("abc".to_owned(), n, String::new(), |s, t| {
            s.chars().chain(t.chars()).collect::<String>()
        })
    }
}
