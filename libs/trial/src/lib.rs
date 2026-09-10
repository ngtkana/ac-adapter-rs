//! 整数の約数・素因数を試し割りで列挙する。
//!
//! 約数は $d^2 \le n$ の範囲で $d$ を $1$ から順に試し割りし、見つかった約数 $d$ と
//! その相方 $n / d$ を両側から積んでいくことで $O(\sqrt n)$ で求める。素因数分解も同様に、
//! 候補 $p$ を $p^2 > n$ になるまで増やしながら割り切れるかを試し、割り切れる限り
//! $n$ から取り除いていく。
//!
//! # 仕様
//!
//! - [`divisors`] 関数は約数を昇順に列挙した `Vec` を返す
//! - [`divisors_unordered`] 関数は約数を「小さい方・大きい方」交互の順で列挙するイテレータを返す
//! - [`prime_factors`] 関数は相異なる素因数を昇順に列挙するイテレータを返す
//! - [`prime_factors_rle`] 関数は素因数とその重複度の組 $(p, e)$ を昇順に列挙するイテレータを返す
//!
//! # 例
//!
//! ```
//! use trial::divisors;
//! use trial::prime_factors_rle;
//!
//! assert_eq!(divisors(12u32), vec![1, 2, 3, 4, 6, 12]);
//! assert_eq!(prime_factors_rle(12u32).collect::<Vec<_>>(), vec![(2, 2), (3, 1)]);
//! ```
//!
//! # 計算量
//!
//! - [`divisors`] と [`divisors_unordered`] は $O(\sqrt n)$
//! - [`prime_factors`] と [`prime_factors_rle`] は $O(\sqrt n)$

mod divisors;
mod prime_factors;

pub use divisors::divisors;
pub use divisors::divisors_unordered;
pub use divisors::Divisors;
pub use prime_factors::prime_factors;
pub use prime_factors::prime_factors_rle;
pub use prime_factors::PrimeFactors;
pub use prime_factors::PrimeFactorsRle;
use std::fmt::Debug;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Rem;
use std::ops::RemAssign;
use std::ops::Sub;
use std::ops::SubAssign;

/// 試し割りの対象となる符号なし整数が実装するトレイト。
pub trait Value:
    Debug
    + Copy
    + Ord
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + Rem<Output = Self>
    + RemAssign
{
    /// 加法の単位元 $0$。
    const ZERO: Self;
    /// 乗法の単位元 $1$。
    const ONE: Self;
    /// `self` を $1$ だけ増加させる。
    fn increment(&mut self);
    /// `self` が `n` の約数なら `true` を返す。
    fn divides(self, n: Self) -> bool {
        n % self == Self::ZERO
    }
}

macro_rules! impl_value {
    ($($t:ty),* $(,)?) => {$(
        impl Value for $t {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            fn increment(&mut self) {
                *self += 1;
            }
        }
    )*}
}
impl_value! {
    usize, u8, u16, u32, u64, u128,
}
