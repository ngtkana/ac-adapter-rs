//! Provides iterator utilities of integer expression of sets.

mod combinations;
mod subsets;

pub use combinations::{combinations, Combinations};
pub use subsets::{subsets, Subsets};

use std::{
    fmt::Debug,
    mem::size_of,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

/// Adapter trait of this crate. Already implemented for all the unsigned integer types.
pub trait Unsigned:
    Sized
    + PartialEq
    + PartialOrd
    + Debug
    + Clone
    + Copy
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
    + Not<Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
    fn wrapping_neg(self) -> Self;
    fn bit_length() -> u32 {
        size_of::<Self>() as u32 * 8
    }
}

macro_rules! impl_unsigned {
    ($($T:ty),* $(,)?) => {$(
        impl Unsigned for $T {
            fn zero() -> Self { 0 }
            fn one() -> Self { 1 }
            fn wrapping_neg(self) -> Self { self.wrapping_neg() }
        }
    )*}
}

impl_unsigned! { usize, u8, u16, u32, u64, u128 }
