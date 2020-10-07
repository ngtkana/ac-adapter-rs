use query_test::Query;
use std::{marker::PhantomData, ops::Range};

#[query_test::query(fn(usize, T))]
pub struct Set<T>(PhantomData<T>);

#[query_test::query(fn(Range<usize>) -> T)]
pub struct Fold<T>(PhantomData<T>);

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
