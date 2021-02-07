use std::{
    fmt::Debug,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign},
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
    /// Returns `2`.
    fn two() -> Self;
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
            fn one() -> Self {
                1
            }
            fn two() -> Self {
                2
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
