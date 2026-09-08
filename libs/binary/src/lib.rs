//! モノイドの作用・積を繰り返し二乗法で $O(\log n)$ 回の演算に落とす二分累乗法。
//!
//! 指数 $n$ を二進展開し、上位ビットから「二乗して、そのビットが $1$ なら合成する」
//! ことを繰り返すと、$n$ 回分の合成が $O(\log n)$ 回の二乗・合成で計算できる。
//! 型 `T` の演算（二乗 `square` / 積 `mul`）と型 `U` への作用 `apply` を
//! クロージャで渡すことで、行列累乗やモノイド作用など任意の演算に流用できる。
//!
//! # 仕様
//!
//! - [`Pow`]: 指数として使える型（符号なし整数）を表すトレイト
//! - [`operator_binary`]: $a$ を $n$ 回 $x$ に作用させた結果 $a^n(x)$ を返す
//! - [`value_binary`]: モノイドの積 $a^n$ を返す（単位元 `identity` 込み）
//!
//! # 例
//!
//! ```
//! use binary::value_binary;
//!
//! // 3^5 = 243 を素朴な乗算の繰り返し二乗法で計算する
//! let result = value_binary(3, 5_u32, 1, |&a, &b| a * b);
//! assert_eq!(result, 243);
//! ```
//!
//! # 計算量
//!
//! - [`operator_binary`], [`value_binary`]: `square`/`mul` の呼び出し $O(\log n)$ 回

/// 二分累乗法の指数として使える符号なし整数型を表すトレイト。
pub trait Pow {
    /// $x \neq 0$
    fn is_nonzero(&self) -> bool;
    /// $x \neq 1$
    fn is_nonone(&self) -> bool;
    /// $x$ が奇数か
    fn is_odd(&self) -> bool;
    /// $x \mathrel{{/}{=}} 2$（右シフト）
    fn shr1(&mut self);
}

/// $a$ を $x$ に $n$ 回作用させた結果 $a^n(x)$ を、$O(\log n)$ 回の `square`/`apply` で計算する。
///
/// `square` は $T$ 上の二乗、`apply` は $T$ の $U$ への作用（$a$ を $x$ に $1$ 回作用させる操作）。
///
/// # 例
///
/// ```
/// use binary::operator_binary;
///
/// let a = 2;
/// let n = 5_u32; // `i32` はコンパイルエラー
/// let x = 42;
/// let result = operator_binary(a, n, x, |&i| i * i, |&i, j| i * j);
/// assert_eq!(result, 32 * x); // 2^5 = 32 を x = 42 に作用（乗算）
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

/// モノイドの積 $a^n$ を、単位元 `identity` と積 `mul` から $O(\log n)$ 回の `mul` で計算する。
///
/// # 例
///
/// ```
/// use binary::value_binary;
///
/// let a = 3;
/// let n = 5_u32; // `i32` はコンパイルエラー
/// let result = value_binary(a, n, 1, |&i, &j| i * j);
/// assert_eq!(result, 243); // 3^5 = 243
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

    fn cat(s: &str, t: &str) -> String {
        s.chars().chain(t.chars()).collect()
    }

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
