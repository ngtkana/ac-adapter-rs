use super::{Assoc, Element, Identity};
use std::{cmp, marker::PhantomData};

pub trait MinValue: Element + cmp::Ord {
    fn min_value() -> Self;
}

pub trait MaxValue: Element + cmp::Ord {
    fn max_value() -> Self;
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct Min<T>(PhantomData<T>);
impl<T: Element + cmp::Ord> Assoc for Min<T> {
    type Value = T;
    fn op(lhs: T, rhs: T) -> T {
        lhs.min(rhs)
    }
}
impl<T: MaxValue> Identity for Min<T> {
    fn identity() -> T {
        T::max_value()
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct Max<T>(PhantomData<T>);
impl<T: Element + cmp::Ord> Assoc for Max<T> {
    type Value = T;
    fn op(lhs: T, rhs: T) -> T {
        lhs.max(rhs)
    }
}
impl<T: MinValue> Identity for Max<T> {
    fn identity() -> T {
        T::min_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_impl::assert_impl;

    #[test]
    fn test_min() {
        assert_eq!(Min::<u32>::op(2, 4), 2);
        assert_eq!(Min::<u32>::identity(), std::u32::MAX);
        assert_impl!(!Assoc: Min::<f32>);
        assert_impl!(!Identity: Min::<f32>);
    }

    #[test]
    fn test_max() {
        assert_eq!(Max::<u32>::op(2, 4), 4);
        assert_eq!(Max::<u32>::identity(), std::u32::MIN);
        assert_impl!(!Assoc: Max::<f32>);
        assert_impl!(!Identity: Max::<f32>);
    }
}
