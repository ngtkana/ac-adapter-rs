mod crt;
mod ext_gcd;
mod gcd;

pub use {crt::crt, ext_gcd::ext_gcd, gcd::gcd};

use std::{
    fmt::Debug,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
};

/// Abstraction of integers.
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
    /// Returns `0`.
    fn zero() -> Self;
    /// Returns `1`.
    fn one() -> Self;
    /// Increment `self`.
    fn increment(&mut self);
    /// Returns the absolute value.
    fn abs(self) -> Self;
    /// Calculates the quotient of Euclidean division of self by `rhs`.
    fn div_euclid(self, rhs: Self) -> Self;
    /// Calculates the least nonnegative remainder of `self (mod rhs)`.
    fn rem_euclid(self, rhs: Self) -> Self;
    /// Returns `true` if and only if `self` divides `n`.
    fn divides(self, n: Self) -> bool {
        n.rem_euclid(self) == Self::zero()
    }
}

/// Abstraction of unsigned integers.
pub trait Unsigned: Int {}
/// Abstraction of signed integers.
pub trait Signed: Int + Neg<Output = Self> {}

macro_rules! impl_unsigned {
    ($($t:ty),* $(,)?) => {$(
        impl Int for $t {
            fn zero() -> Self {
                0
            }
            fn one() -> Self {
                1
            }
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
            fn zero() -> Self {
                0
            }
            fn one() -> Self {
                1
            }
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
