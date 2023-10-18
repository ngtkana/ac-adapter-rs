//! Execute the trial-division algorithm.
//!
//! # Items
//!
//! - [`fn@divisors`]: enumerate all the divisor of an integer.
//! - [`fn@prime_factors`]: enumerate all the prime divisor of an integer and the multiplicity of it.

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
    fn divides(self, n: Self) -> bool { n % self == Self::zero() }
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
