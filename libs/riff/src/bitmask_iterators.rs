use std::fmt::Debug;
use std::mem::size_of;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Not;
use std::ops::Shl;
use std::ops::ShlAssign;
use std::ops::Shr;
use std::ops::ShrAssign;
use std::ops::Sub;
use std::ops::SubAssign;

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

/// Returns an iterator over k-subsets of `(T::one() << n) - T::one()`.
///
/// # Examples
///
/// Basic usage:
/// ```
/// use bitutils::combinations;
///
/// assert_eq!(combinations::<u32>(3, 2).collect::<Vec<_>>(), vec![3, 5, 6],);
/// ```
pub fn bitmask_combinations<T: Unsigned>(n: u32, k: u32) -> BitmaskCombinations<T> {
    assert!(k < T::bit_length() && k < T::bit_length());
    BitmaskCombinations {
        n,
        bs: (T::one() << k) - T::one(),
    }
}

/// [See the document of `combinations`](combinations)
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct BitmaskCombinations<T> {
    n: u32,
    bs: T,
}
impl<T: Unsigned> Iterator for BitmaskCombinations<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if (T::one() << self.n) <= self.bs {
            return None;
        }
        let res = Some(self.bs);
        self.bs = if self.bs == T::zero() {
            T::one() << self.n
        } else {
            let x = self.bs & self.bs.wrapping_neg();
            let y = self.bs + x;
            (((self.bs & !y) / x) >> 1) | y
        };
        res
    }
}

/// Returns an iterator over subsets of `bs`.
///
/// # Examples
///
/// Basic usage:
/// ```
/// use bitutils::subsets;
///
/// assert_eq!(subsets(10u32).collect::<Vec<_>>(), vec![0, 2, 8, 10],);
/// ```
pub fn bitmask_subsets<T: Unsigned>(bs: T) -> BitmaskSubsets<T> {
    BitmaskSubsets {
        bs,
        full: bs,
        finished: false,
    }
}

/// [See the document of `subsets`](subsets)
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct BitmaskSubsets<T> {
    bs: T,
    full: T,
    finished: bool,
}
impl<T: Unsigned> Iterator for BitmaskSubsets<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let res = Some(self.bs ^ self.full);
        if self.bs == T::zero() {
            self.finished = true;
        } else {
            self.bs -= T::one();
            self.bs &= self.full;
        }
        res
    }
}
