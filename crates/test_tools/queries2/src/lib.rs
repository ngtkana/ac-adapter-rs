use alg_traits::{Action, Assoc, Identity};
use query_test::Query;
use std::{marker::PhantomData, ops::Range};

#[query_test::query(fn(usize) -> T)]
pub struct Get<T>(PhantomData<T>);

#[query_test::query(fn(usize, T))]
pub struct Set<T>(PhantomData<T>);

#[query_test::query(fn(Range<usize>) -> T::Value)]
pub struct Fold<T: Identity>(PhantomData<T>);

#[query_test::query(fn(Range<usize>, U) -> usize)]
pub struct SearchForward<T: Identity, U, P: Map<T::Value, U>>(PhantomData<(T, U, P)>);

#[query_test::query(fn(Range<usize>, U) -> usize)]
pub struct SearchBackward<T: Identity, U, P: Map<T::Value, U>>(PhantomData<(T, U, P)>);

#[query_test::query(fn(Range<usize>, <A as Assoc>::Value))]
pub struct RangeApply<A: Action>(PhantomData<A>);

pub trait Map<T, U> {
    fn map(t: &T, u: &U) -> bool;
}

#[cfg(test)]
mod test {
    use super::{Fold, Set};
    use assert_impl::assert_impl;
    use query_test::Query;
    use std::ops::Range;

    #[test]
    fn test_impl() {
        assert_impl!(Query<Param = (usize, u32), Output = ()>: Set<u32>);
        assert_impl!(!Query<Param = ((usize, u32),), Output = ()>: Set<u32>);

        assert_impl!(Query<Param = Range<usize>, Output = u32>: Fold<u32>);
        assert_impl!(!Query<Param = (Range<usize>,), Output = u32>: Fold<u32>);
    }
}
