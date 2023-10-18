//! 二分法（ダブリング）をします。
//!
//! # このライブラリを使える問題
//!
//! - AtCoder 競プロ典型 90 問 058 - Original Calculator（★4）
//!   - 問題: <https://atcoder.jp/contests/typical90/tasks/typical90_bf>
//!   - 提出 (31 ms): <https://atcoder.jp/contests/typical90/submissions/28333297>
//!   - 出題日: 2021-06-05
//!   - 難易度: 易しめ。
//!   - コメント: 周期性でも解けます。
//!   - 使う関数: [`operator_binary`]

/// 指数部分に使うためのトレイトです。すべての符号なし整数型に実装されています。
pub trait Pow {
    /// `*x != 0`
    fn is_nonzero(&self) -> bool;
    /// `*x != 1`
    fn is_nonone(&self) -> bool;
    /// `x & 1 == 1`
    fn is_odd(&self) -> bool;
    /// `self >>= 1`
    fn shr1(&mut self);
}

/// aⁿ(x) を計算します。
///
/// # Requirements
///
/// - `T` が積と `U` への作用を持つ
/// - `square` が `T` における２乗
/// - `apply` が `T` の `U` への作用
///
///
/// # Examples
///
/// ```
/// use binary::operator_binary;
///
/// let a = 2;
/// let n = 5_u32; // `i32` はコンパイルエラー
/// let x = 42;
/// let result = operator_binary(a, n, x, |&i| i * i, |&i, j| i * j);
/// assert_eq!(result, 32 * x);
/// ```
pub fn operator_binary<T, U>(
    mut a: T,
    mut n: impl Pow,
    mut x: U,
    mut square: impl FnMut(&T) -> T,
    mut apply: impl FnMut(&T, U) -> U,
) -> U {
    if n.is_nonzero() {
        while n.is_nonone() {
            if n.is_odd() {
                x = apply(&a, x);
            }
            a = square(&a);
            n.shr1();
        }
        x = apply(&a, x);
    }
    x
}

/// aⁿを計算します。
///
/// # Requirements
///
/// - `T` が積と単位元を持つ
/// - `identity` が `T` の単位元
/// - `mul` が `T` の積
///
///
/// # Examples
///
/// ```
/// use binary::value_binary;
///
/// let a = 3;
/// let n = 5_u32; // `i32` はコンパイルエラー
/// let result = value_binary(a, n, 1, |&i, &j| i * j);
/// assert_eq!(result, 243);
/// ```
pub fn value_binary<T>(
    mut a: T,
    mut n: impl Pow,
    identity: T,
    mut mul: impl FnMut(&T, &T) -> T,
) -> T {
    let mut ans = identity;
    if n.is_nonzero() {
        while n.is_nonone() {
            if n.is_odd() {
                ans = mul(&a, &ans);
            }
            a = mul(&a, &a);
            n.shr1();
        }
        ans = mul(&a, &ans);
    }
    ans
}

macro_rules! impl_pow {
    ($($T:ty),* $(,)?) => {$(
        impl Pow for $T {
            fn is_nonzero(&self) -> bool {
                *self != 0
            }
            fn is_nonone(&self) -> bool {
                *self != 1
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
    use super::*;
    use test_case::test_case;

    fn cat(s: &str, t: &str) -> String { s.chars().chain(t.chars()).collect() }

    #[test_case(0 => "x".to_owned())]
    #[test_case(1 => "abx".to_owned())]
    #[test_case(2 => "ababx".to_owned())]
    #[test_case(3 => "abababx".to_owned())]
    #[test_case(4 => "ababababx".to_owned())]
    #[test_case(5 => "abababababx".to_owned())]
    fn test_operator_binary(n: u32) -> String {
        operator_binary(
            "ab".to_owned(),
            n,
            "x".to_string(),
            |a| cat(a, a),
            |a, x| cat(a, &x),
        )
    }

    #[test_case(0 => String::new())]
    #[test_case(1 => "ab".to_owned())]
    #[test_case(2 => "abab".to_owned())]
    #[test_case(3 => "ababab".to_owned())]
    #[test_case(4 => "abababab".to_owned())]
    #[test_case(5 => "ababababab".to_owned())]
    fn test_value_binary(n: u32) -> String {
        value_binary("ab".to_owned(), n, String::new(), |a, b| cat(a, b))
    }
}
