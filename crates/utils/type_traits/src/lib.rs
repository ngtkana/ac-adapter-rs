#![warn(missing_docs)]
//! トレイト定義のクレートです。

use std::{cmp, ops};

mod primitive;

/// `ops::{Add, Mul}` を用いて [`Assoc`], [`Identity`] を定義するラッパーを定義しています。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
pub mod wrappers;

/// 結合的な演算を持つトレイトです。
pub trait Assoc: Sized {
    /// 結合的な演算です。
    fn op(self, rhs: Self) -> Self;
}

/// 単位元を持つ [`Assoc`] です。
///
/// [`Assoc`]: trait.Assoc.html
pub trait Identity: Assoc {
    /// 単位元です。
    fn identity() -> Self;
}

/// `ops::Add` の単位元（零元）を持つトレイトです。
pub trait Zero: Sized + ops::Add<Output = Self> + ops::AddAssign {
    /// `ops::Add` の単位元（零元）を返します。
    fn zero() -> Self;

    /// 単位元（零元）であるかどうか判定します。
    fn is_zero(&self) -> bool
    where
        Self: cmp::PartialEq,
    {
        self == &Self::zero()
    }
}

/// `ops::Mul` の単位元を持つトレイトです。
pub trait One: Sized + ops::Mul<Output = Self> + ops::MulAssign {
    /// `ops::Mul` の単位元を返します。
    fn one() -> Self;

    /// 単位元であるかどうか判定します。
    fn is_one(&self) -> bool
    where
        Self: cmp::PartialEq,
    {
        self == &Self::one()
    }
}

/// [`Constant`] トレイトを簡単に定義できます。
///
/// # Examples
///
/// ```
/// use type_traits::*;
/// define_constant!{ type A: i16 = 42; }
/// assert_eq!(A::VALUE, 42);
/// ```
///
/// [`Constant`]: traits.Constant.html
#[macro_export]
macro_rules! define_constant {
    ($(#[$attr:meta])? $vis:vis type $wrapper_type:ident: $value_type:ty = $value:expr;) => {
        $(#[$attr])?
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        $vis struct $wrapper_type {}

        impl Constant for $wrapper_type {
            type Output = $value_type;
            const VALUE: Self::Output = $value;
        }
    };
}

/// [`Output`] 型の関連定数 [`VALUE`] を持つトレイトです。[`Output`] には `Copy` トレイトを実装した任意の型が使えます。
///
/// [`Output`]: trait.Constant.html#associatedtype.Output
/// [`VALUE`]: trait.Constant.html#asssociatedconstant.VALUE
pub trait Constant: Copy {
    /// [`VALUE`] の型です。
    ///
    /// TODO: `Value` に改名します。
    ///
    /// [`VALUE`]: trait.Constant.html#asssociatedconstant.VALUE
    type Output: Copy;

    /// 主役です。
    const VALUE: Self::Output;
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_impl::assert_impl;

    #[test]
    fn test_impl_assoc() {
        assert_impl! {Assoc: wrappers::Add<u32>,  wrappers::Mul<u32>}
        assert_impl! {!Assoc: u32, wrappers::Add<()>}
    }

    #[test]
    fn test_impl_identity() {
        assert_impl! {Identity: wrappers::Add<u32>,  wrappers::Mul<u32>}
        assert_impl! {!Identity: u32, wrappers::Add<()>}
    }

    #[test]
    fn test_impl_zero() {
        assert_impl! {Zero: u32, i32 }
        assert_impl! {!Zero: wrappers::Add<u32>, wrappers::Mul<u32> }
    }

    #[test]
    fn test_impl_one() {
        assert_impl! {Zero: u32, i32 }
        assert_impl! {!Zero: wrappers::Add<u32>, wrappers::Mul<u32> }
    }

    #[test]
    fn test_zero() {
        assert_eq!(<u32 as Zero>::zero(), 0);
        assert_eq!(<i32 as Zero>::zero(), 0);
    }

    #[test]
    fn test_one() {
        assert_eq!(<u32 as One>::one(), 1);
        assert_eq!(<i32 as One>::one(), 1);
    }
}
