//! 素数 $p$ を法とした平方根（modular square root）を、Cipolla のアルゴリズムで求める。
//!
//! $a$ が平方非剰余となるような $b$ を探し、2 次拡大体 $\mathbb{F}_p[\sqrt{b^2 - a}]$ を構成する。
//! この体上で $(b + \sqrt{b^2 - a})^{(p+1)/2}$ を計算すると、$b^2 - a$ が非剰余であることから
//! フロベニウス写像の性質により虚部が消え、実部として $\sqrt a$ が得られる。
//! Tonelli–Shanks 法と異なり $p - 1$ の 2-進付値を扱わない分、実装が単純。
//!
//! # 仕様
//!
//! [`cipolla_sqrt`]`(a, p)` は $p$ を素数として、$x^2 \equiv a \pmod p$ を満たす $x$ を返す。
//! 平方剰余が存在しなければ `None`。
//!
//! # 例
//!
//! ```
//! use cipolla::cipolla_sqrt;
//! let x = cipolla_sqrt(5u64, 41).unwrap();
//! assert_eq!(x * x % 41, 5);
//! assert_eq!(cipolla_sqrt(3u64, 5), None); // 3 は mod 5 の平方非剰余
//! ```
//!
//! # 計算量
//!
//! - [`cipolla_sqrt`][]: 期待 $O(\log p)$（非剰余の $b$ を見つける試行回数は期待 $O(1)$ 回）

use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
use std::ops::Sub;

/// $x^2 \equiv a \pmod p$ を満たす $x$ を Cipolla のアルゴリズムで求める。
///
/// `p` は素数を仮定する。$a$ が平方非剰余の場合は `None`。
///
/// # 例
///
/// ```
/// use cipolla::cipolla_sqrt;
/// let x = cipolla_sqrt(2u64, 7).unwrap();
/// assert_eq!(x * x % 7, 2);
/// ```
///
/// # 計算量
///
/// 期待 $O(\log p)$
pub fn cipolla_sqrt<T: Unsigned>(a: T, p: T) -> Option<T> {
    let a = a % p;
    if p == T::TWO {
        Some(a)
    } else if a == T::ZERO {
        Some(T::ZERO)
    } else if binary_exponentiation(a, p / T::TWO, T::ONE, |x, y| x * y % p) != T::ONE {
        None
    } else {
        let mut b = T::ZERO;
        loop {
            let sqgen = (b * b + p - a) % p;
            if binary_exponentiation(sqgen, p / T::TWO, T::ONE, |x, y| x * y % p) != T::ONE {
                return Some(
                    binary_exponentiation(
                        [b, T::ONE],
                        (p + T::ONE) / T::TWO,
                        [T::ONE, T::ZERO],
                        |x, y| {
                            [
                                (x[0] * y[0] + (x[1] * y[1]) % p * sqgen) % p,
                                (x[0] * y[1] + x[1] * y[0]) % p,
                            ]
                        },
                    )[0],
                );
            }
            b = b + T::ONE;
        }
    }
}

// 繰り返し二乗法により、モノイド演算 `f` に関する `a` の `n` 乗を $O(\log n)$ で計算する。
fn binary_exponentiation<T: Unsigned, U: Copy>(
    mut a: U,
    mut n: T,
    id: U,
    mut f: impl FnMut(U, U) -> U,
) -> U {
    let mut ans = id;
    while n != T::ZERO {
        if n % T::TWO == T::ONE {
            ans = f(ans, a);
        }
        a = f(a, a);
        n = n / T::TWO;
    }
    ans
}

/// [`cipolla_sqrt`] が要求する、`p` を法とした四則演算に必要な符号なし整数の性質。
///
/// # 例
///
/// ```
/// use cipolla::Unsigned;
/// assert_eq!(u64::ZERO, 0);
/// assert_eq!(u64::ONE, 1);
/// assert_eq!(u64::TWO, 2);
/// ```
pub trait Unsigned:
    Sized
    + Clone
    + Copy
    + PartialEq
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
{
    /// $0$
    const ZERO: Self;
    /// $1$
    const ONE: Self;
    /// $2$
    const TWO: Self;
}

macro_rules! impl_unsigned {
    ($($T:ty),+) => {$(
        impl Unsigned for $T {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const TWO: Self = 2;
        }
    )+}
}
impl_unsigned! {u8, u16, u32, u64, u128, usize}

#[cfg(test)]
mod tests {
    use super::cipolla_sqrt;

    #[test]
    fn test_sqrt_all() {
        let mut sieve = [false; 100];
        let sieve_len = sieve.len();
        for p in 2..sieve_len {
            if sieve[p] {
                continue;
            }
            // 素数 p を順にテストです。
            let mut count = 0;
            for y in 1..p {
                if let Some(x) = cipolla_sqrt(y, p) {
                    assert_eq!(x * x % p, y);
                    count += 1;
                }
            }
            // 平方剰余の個数は ceil(p / 2) 個
            assert_eq!(count, p / 2);
            (p * p..)
                .step_by(p)
                .take_while(|&q| q < sieve_len)
                .for_each(|q| sieve[q] = true);
        }
    }
}
