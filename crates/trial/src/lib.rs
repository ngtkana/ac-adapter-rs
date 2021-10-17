//! Execute the trial-division algorithm.
//!
//! # Items
//!
//! - [`fn@divisors`]: enumerate all the divisor of an integer.
//! - [`fn@prime_factors`]: enumerate all the prime divisor of an integer and the multiplicity of it.

mod divisors;
mod prime_factors;

use std::{
    fmt::Debug,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign},
};
pub use {
    divisors::{divisors, divisors_unordered, Divisors},
    prime_factors::{prime_factors, prime_factors_rle, PrimeFactors, PrimeFactorsRle},
};

/// Abstraction of unsigned integers.
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
    /// Returns `0`.
    fn zero() -> Self;
    /// Returns `1`.
    fn one() -> Self;
    /// Increment `self`.
    fn increment(&mut self);
    /// Returns `true` if and only if `self` divides `n`.
    fn divides(self, n: Self) -> bool {
        n % self == Self::zero()
    }
}

macro_rules! impl_value {
    ($($t:ty),* $(,)?) => {$(
        impl Value for $t {
            fn zero() -> Self {
                0
            }
            fn one() -> Self {
                1
            }
            fn increment(&mut self) {
                *self += 1;
            }
        }
    )*}
}
impl_value! {
    usize, u8, u16, u32, u64, u128,
}
