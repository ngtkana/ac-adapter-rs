//! 最大公約数・拡張ユークリッドの互除法・中国剰余定理。
//!
//! 整数型を [`Int`] トレイトで抽象化し、`usize` から `i128` までの標準整数型すべてに対して
//! [`gcd`], [`ext_gcd`], [`crt`] を共通コードで提供する。符号なし整数は [`Unsigned`]、符号付き
//! 整数は [`Signed`] としてさらに区別し、負数や減法を要する [`ext_gcd`], [`crt`] は
//! [`Signed`] にのみ実装する。
//!
//! # 仕様
//!
//! - [`gcd`][]: $\gcd(x, y)$（符号は無視）
//! - [`ext_gcd`][]: $ax + by = \gcd(x, y)$ を満たす $(a, b, \gcd(x, y))$
//! - [`crt`][]: 中国剰余定理。$2$ つの合同式を $1$ つにまとめる
//!
//! # 例
//!
//! ```
//! use euclid::ext_gcd;
//! use euclid::gcd;
//! assert_eq!(gcd(42, 48), 6);
//! let (a, b, g) = ext_gcd(42, 48);
//! assert_eq!(g, 6);
//! assert_eq!(a * 42 + b * 48, g);
//! ```
//!
//! # 計算量
//!
//! - [`gcd`], [`ext_gcd`][]: $O(\log \min(|x|, |y|))$
//! - [`crt`][]: $O(\log \min(\mathrm{mod0}, \mathrm{mod1}))$

mod crt;
mod ext_gcd;
mod gcd;

pub use crt::crt;
pub use ext_gcd::ext_gcd;
pub use gcd::gcd;
use std::fmt::Debug;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::RemAssign;
use std::ops::Sub;
use std::ops::SubAssign;

/// 整数型の共通演算を抽象化するトレイト。
///
/// 四則演算・剰余・比較に加え、ユークリッド除算（[`Int::div_euclid`], [`Int::rem_euclid`]）を要求する。
/// [`gcd`] はこのトレイトのみで実装でき、符号を要する [`ext_gcd`], [`crt`] はさらに [`Signed`] を要求する。
pub trait Int:
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
    /// 加法単位元 $0$。
    const ZERO: Self;
    /// 乗法単位元 $1$。
    const ONE: Self;
    /// `self` を $1$ だけ増やす。
    fn increment(&mut self);
    /// 絶対値 $|{\rm self}|$ を返す。
    fn abs(self) -> Self;
    /// ユークリッド除算の商を返す。
    fn div_euclid(self, rhs: Self) -> Self;
    /// ユークリッド除算の剰余（非負）を返す。
    fn rem_euclid(self, rhs: Self) -> Self;
    /// `self` が `n` の約数かどうかを判定する。
    ///
    /// # 例
    ///
    /// ```
    /// use euclid::Int;
    /// assert!(3_i32.divides(9));
    /// assert!(!3_i32.divides(10));
    /// ```
    fn divides(self, n: Self) -> bool {
        n.rem_euclid(self) == Self::ZERO
    }
}

/// 符号なし整数を表すマーカートレイト。
pub trait Unsigned: Int {}
/// 符号付き整数を表すマーカートレイト。[`ext_gcd`], [`crt`] はこのトレイトを要求する。
pub trait Signed: Int + Neg<Output = Self> {}

macro_rules! impl_unsigned {
    ($($t:ty),* $(,)?) => {$(
        impl Int for $t {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            fn increment(&mut self) {
                *self += 1;
            }
            fn abs(self) -> Self {
                self
            }
            fn div_euclid(self, rhs: Self) -> Self {
                self.div_euclid(rhs)
            }
            fn rem_euclid(self, rhs: Self) -> Self {
                self.rem_euclid(rhs)
            }
        }
        impl Unsigned for $t {}
    )*}
}
impl_unsigned! {
    usize, u8, u16, u32, u64, u128,
}
macro_rules! impl_signed {
    ($($t:ty),* $(,)?) => {$(
        impl Int for $t {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            fn increment(&mut self) {
                *self += 1;
            }
            fn abs(self) -> Self {
                self.abs()
            }
            fn div_euclid(self, rhs: Self) -> Self {
                self.div_euclid(rhs)
            }
            fn rem_euclid(self, rhs: Self) -> Self {
                self.rem_euclid(rhs)
            }
        }
        impl Signed for $t {}
    )*}
}
impl_signed! {
    isize, i8, i16, i32, i64, i128,
}
