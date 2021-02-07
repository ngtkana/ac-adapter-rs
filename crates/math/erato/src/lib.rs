mod least;
mod sieve_base;
mod sieve_kind;

pub use least::Least;
pub use sieve_base::{Sieve, SieveBase, SieveUsize};

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

fn construct_least_table(n: usize) -> Vec<usize> {
    let mut least = vec![std::usize::MAX; n];
    for p in 2..n {
        if least[p] != std::usize::MAX {
            continue;
        }
        least[p] = p;
        let mut i = p * p;
        while i < n {
            if least[i] == std::usize::MAX {
                least[i] = p;
            }
            i += p;
        }
    }
    least
}

#[cfg(test)]
mod tests {
    use {super::construct_least_table, test_case::test_case};

    #[test_case(0 => Vec::<usize>::new())]
    #[test_case(1 => vec![std::usize::MAX])]
    #[test_case(2 => vec![std::usize::MAX, std::usize::MAX])]
    #[test_case(3 => vec![std::usize::MAX, std::usize::MAX, 2])]
    #[test_case(4 => vec![std::usize::MAX, std::usize::MAX, 2, 3])]
    #[test_case(5 => vec![std::usize::MAX, std::usize::MAX, 2, 3, 2])]
    #[test_case(6 => vec![std::usize::MAX, std::usize::MAX, 2, 3, 2, 5])]
    #[test_case(16 => vec![std::usize::MAX, std::usize::MAX, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3])]
    fn test_construct_least_table(n: usize) -> Vec<usize> {
        construct_least_table(n)
    }
}
