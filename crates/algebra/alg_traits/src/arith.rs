use super::{Assoc, Element, Identity};
use std::{marker::PhantomData, ops};

pub trait Zero: Element + ops::Add<Output = Self> + ops::AddAssign {
    fn zero() -> Self;
}

pub trait One: Element + ops::Mul<Output = Self> + ops::MulAssign {
    fn one() -> Self;
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Add<T>(PhantomData<T>);
impl<T: Element + ops::Add<Output = T> + ops::AddAssign> Assoc for Add<T> {
    type Value = T;
    fn op(lhs: T, rhs: T) -> T {
        lhs + rhs
    }
    fn op_left(lhs: &mut T, rhs: T) {
        *lhs += rhs;
    }
}
impl<T: Zero> Identity for Add<T> {
    fn identity() -> T {
        T::zero()
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Mul<T>(PhantomData<T>);
impl<T: Element + ops::Mul<Output = T> + ops::MulAssign> Assoc for Mul<T> {
    type Value = T;
    fn op(lhs: T, rhs: T) -> T {
        lhs * rhs
    }
    fn op_left(lhs: &mut T, rhs: T) {
        *lhs *= rhs;
    }
}
impl<T: One> Identity for Mul<T> {
    fn identity() -> T {
        T::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(Add::<u32>::op(2, 4), 6);
        assert_eq!(Add::<u32>::identity(), 0);
        assert_eq!(Add::<f32>::op(2., 4.), 6.);
        assert_eq!(Add::<f32>::identity(), 0.);
    }

    #[test]
    fn test_mul() {
        assert_eq!(Mul::<u32>::op(2, 4), 8);
        assert_eq!(Mul::<u32>::identity(), 1);
        assert_eq!(Mul::<f32>::op(2., 4.), 8.);
        assert_eq!(Mul::<f32>::identity(), 1.);
    }
}
