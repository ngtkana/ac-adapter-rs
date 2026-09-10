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
    /// `0`
    const ZERO: Self;
    /// `1`
    const ONE: Self;
    /// `2`
    const TWO: Self;
    /// Converts into `usize`
    fn as_usize(self) -> usize;
    /// Converts an `usize` into `Self`
    fn from_usize(src: usize) -> Self;
}

macro_rules! impl_int {
    ($($t:ty),* $(,)?) => {$(
        impl Int for $t {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const TWO: Self = 2;
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
