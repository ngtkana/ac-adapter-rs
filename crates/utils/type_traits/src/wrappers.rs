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
    #[inline]
    fn op(self, rhs: Self) -> Self {
        Add(self.0 + rhs.0)
    }
}
impl<T> Identity for Add<T>
where
    T: Zero,
{
    #[inline]
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
    #[inline]
    fn op(self, rhs: Self) -> Self {
        Mul(self.0 * rhs.0)
    }
}
impl<T> Identity for Mul<T>
where
    T: One,
{
    #[inline]
    fn identity() -> Self {
        Mul(T::one())
    }
}
