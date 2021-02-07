mod is_prime;
mod least;

pub use is_prime::IsPrime;
pub use least::Least;

use std::fmt::Debug;

/// Abstraction of integers.
pub trait Int: Debug + Copy + Ord {
    /// Returns `0`.
    fn zero() -> Self;
    /// Converts into `usize`
    fn as_usize(self) -> usize;
    /// Converts an `usize` into `Self`
    fn from_usize(src: usize) -> Self;
}

macro_rules! impl_int {
    ($($t:ty),* $(,)?) => {$(
        impl Int for $t {
            fn zero() -> Self {
                0
            }
            fn as_usize(self) -> usize {
                self as usize
            }
            fn from_usize(src: usize) -> Self {
                src as Self
            }
        }
    )*}
}
impl_int! {
    usize, u8, u16, u32, u64, u128,
    isize, i8, i16, i32, i64, i128,
}
