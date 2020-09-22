#![warn(missing_docs)]
//! 基本的なトレイトを定義します。
//!
//! TODO: 代数関連を分離します。
//!
//! # 代数関連
//!
//! すべて基本トレイト [`Element`] を継承しています。
//!
//! ## 二項演算
//!
//! 結合的な演算 [`op`] を備えた [`Assoc`] を継承します。
//!
//! - [`Identity`] : 単位元を返す写像 [`identity`] を備えています。
//! - [`Commut`] : 可換性を表すマーカートレイトです。
//! - [`Deg`] : 次数を返す写像 [`deg`] を備えています。
//! - [`OpN`] : N 乗を高速に計算する写像 [`op_n`] を備えています。
//! - [`OpN`] : N 乗を高速に計算する写像 [`op_n`] を備えています。
//!
//!
//! ## 作用
//!
//! [`Action`] は [`Assoc`] に [`op`] と可換になるように作用します。
//!
//! [`op`]: traits.Assoc.html#method.op
//! [`identity`]: traits.Assoc.html#method.identity
//! [`deg`]: traits.Assoc.html#method.deg
//! [`op_n`]: traits.Assoc.html#method.op_n
//! [`Element`]: traits.Element.html
//! [`Assoc`]: traits.Assoc.html
//! [`Identity`]: traits.Identity.html
//! [`Commut`]: traits.Commut.html
//! [`Deg`]: traits.Deg.html
//! [`OpN`]: traits.OpN.html

use std::{cmp, fmt, ops};

mod primitive;

/// `ops::{Add, Mul}` を用いて [`Assoc`], [`Identity`] を定義するラッパーを定義しています。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
pub mod binary;

/// [`Sized`] + [`Clone`] + [`PartialEq`] です。
///
/// [`Sized`]: https://doc.rust-lang.org/std/marker/traits.Sized.html
/// [`Clone`]: https://doc.rust-lang.org/std/marker/traits.Clone.html
/// [`PartialEq`]: https://doc.rust-lang.org/std/cmp/traits.PartialEq.html
pub trait Element: Sized + Clone + PartialEq + fmt::Debug {}
impl<T: Sized + Clone + PartialEq + fmt::Debug> Element for T {}

/// 結合的な演算を持つトレイトです。
///
/// # 要件
///
/// `x.op(y.op(z)) == x.op(y).op(z)`
pub trait Assoc: Element {
    /// 結合的な演算です。
    fn op(self, rhs: Self) -> Self;

    /// 左から掛け算をします。
    fn op_from_left(&mut self, left: &Self) {
        *self = Self::op(left.clone(), self.clone());
    }

    /// 左から掛け算をします。
    fn op_from_right(&mut self, right: &Self) {
        *self = Self::op(self.clone(), right.clone());
    }
}

/// 単位元を持つ [`Assoc`](trait.Assoc.html) です。
///
/// # 要件
///
/// `T::identity().op(x) == x && x.op(T::identity() == x`
pub trait Identity: Assoc {
    /// 単位元です。
    fn identity() -> Self;
}

/// [`Assoc`](trait.Assoc.html) が可換なことを表すマーカートレイトです。
///
/// # 要件
///
/// `x.op(y) == y.op(x)`
pub trait Commut: Assoc {}

/// [`Assoc`](trait.Assoc.html) の n 乗が高速に計算できるときに使います。
pub trait OpN: Assoc {
    /// n 乗です。
    fn op_n(self) -> Self;
}

/// 自然数で字数付けられた [`Assoc`](trait.Assoc.html) です。
///
/// # 要件
///
/// `x.op(y).deg() == x.deg() + y.deg()`
pub trait Deg: Assoc {
    /// 字数を返します。
    fn deg(&self) -> usize;
}

/// 同質的に字数付けをします。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Grade<T> {
    /// 中身です。
    pub base: T,
    /// 次数です。
    pub deg: usize,
}
impl<T: Assoc> Assoc for Grade<T> {
    fn op(self, rhs: Self) -> Self {
        Grade {
            deg: self.deg + rhs.deg,
            base: self.base.op(rhs.base),
        }
    }
}

/// 作用をします。
///
/// # 要件
///
/// `A: Action`, `a: A`, `x, y: Action::Space` に対して、次が成り立つことです。
///
/// `a.acted(x.op(y)) == a.acted(x).op(a.acted(y))`
///
pub trait Action {
    /// 作用される空間です。
    type Space: Assoc;
    /// 作用関数です。
    fn acted(self, x: Self::Space) -> Self::Space;
}

/// `ops::Add` の単位元（零元）を持つトレイトです。
pub trait Zero: ops::Add<Output = Self> + ops::AddAssign + Element {
    /// `ops::Add` の単位元（零元）を返します。
    fn zero() -> Self;

    /// 単位元（零元）であるかどうか判定します。
    fn is_zero(&self) -> bool
    where
        Self: cmp::PartialEq,
    {
        self == &Self::zero()
    }

    /// 自然数倍です。
    fn times(self, n: u64) -> Self;

    /// [`times`](trait.Zero.html#method.times) の複合代入版です。
    fn times_assign(&mut self, n: u64);

    /// 自然数の埋め込みです。
    fn from_u64(x: u64) -> Self;
}

/// `ops::Mul` の単位元を持つトレイトです。
pub trait One: ops::Mul<Output = Self> + ops::MulAssign + Element {
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

/// 単位元を持つ結合的な積を持つ環です。
pub trait Ring: Zero + One + ops::Neg + ops::Sub<Output = Self> + ops::SubAssign {}
impl<T: Zero + One + ops::Neg + ops::Sub<Output = Self> + ops::SubAssign> Ring for T {}

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

/// 大きくなりがちなラッパー型のデバッグ出力を小さくするために本質パートを抽出するためのトレイトです。
///
/// # 目的
///
/// 外部クレートでがデバッグ用ユーティルを作るための便利なトレイトです。
///
/// # 注意
///
/// 参照型でなく値型で帰ってきます。典型的には、ただのラッパーの場合は中身をクローンして、そうでない場合には頑張って構成します。
///
/// デバッグ目的ですから、[`Inner`](trait.Peek.html#associatedtype.Inner) に仮定しているのは
/// [`Sized`] と [`Debug`] のみです。
///
/// [`Sized`]: http://doc.rust-lang.org/std/marker/trait.Sized.html
/// [`Debug`]: http://doc.rust-lang.org/std/fmt/trait.Debug.html
pub trait Peek {
    /// 本質パートの型です。
    type Inner: fmt::Debug;

    /// 本質パート抽出関数です。
    fn peek(&self) -> Self::Inner;
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
        assert_impl! {Assoc: binary::Add<u32>,  binary::Mul<u32>}
        assert_impl! {!Assoc: u32, binary::Add<()>}
    }

    #[test]
    fn test_impl_identity() {
        assert_impl! {Identity: binary::Add<u32>,  binary::Mul<u32>}
        assert_impl! {!Identity: u32, binary::Add<()>}
    }

    #[test]
    fn test_impl_zero() {
        assert_impl! {Zero: u32, i32 }
        assert_impl! {!Zero: binary::Add<u32>, binary::Mul<u32> }
    }

    #[test]
    fn test_impl_one() {
        assert_impl! {Zero: u32, i32 }
        assert_impl! {!Zero: binary::Add<u32>, binary::Mul<u32> }
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
