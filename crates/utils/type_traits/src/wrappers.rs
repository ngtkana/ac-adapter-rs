use super::{Assoc, Element, Identity, One, Zero};
use std::ops;

/// `ops::Add` を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Add<T>(pub T);
impl<T> Assoc for Add<T>
where
    T: ops::Add<Output = T> + Element,
{
    fn op(self, rhs: Self) -> Self {
        Add(self.0 + rhs.0)
    }
}
impl<T> Identity for Add<T>
where
    T: Zero,
{
    fn identity() -> Self {
        Add(T::zero())
    }
}

/// `ops::Mul` を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Mul<T>(pub T);

impl<T> Assoc for Mul<T>
where
    T: ops::Mul<Output = T> + Element,
{
    fn op(self, rhs: Self) -> Self {
        Mul(self.0 * rhs.0)
    }
}
impl<T> Identity for Mul<T>
where
    T: One,
{
    fn identity() -> Self {
        Mul(T::one())
    }
}

/// [`ops::Add`], [`ops::Mul`] によるアフィン変換の合成で [`Assoc`], [`Ideneity`]
/// を実装するラッパーです。
///
/// [`ops::Add`]: http://doc.rust-lang.org/std/ops/trait.Add.html
/// [`ops::Mul`]: http://doc.rust-lang.org/std/ops/trait.Mul.html
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Affine<T> {
    pub a: T,
    pub b: T,
}

impl<T> Assoc for Affine<T>
where
    T: ops::Add<Output = T> + Element,
    T: ops::Mul<Output = T> + Element,
{
    fn op(self, rhs: Self) -> Self {
        Self {
            a: self.a.clone() * rhs.a,
            b: self.b + self.a * rhs.b,
        }
    }
}
impl<T> Identity for Affine<T>
where
    T: Zero + One,
{
    fn identity() -> Self {
        Self {
            a: T::one(),
            b: T::zero(),
        }
    }
}

/// 文字列結合を演算として [`String`] に [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`String`]: http://doc.rust-lang.org/std/str/struct.String.html
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cat(pub String);

impl Assoc for Cat {
    fn op(self, rhs: Self) -> Self {
        Cat(self.0.chars().chain(rhs.0.chars()).collect())
    }
}
impl Identity for Cat {
    fn identity() -> Self {
        Cat(String::new())
    }
}
