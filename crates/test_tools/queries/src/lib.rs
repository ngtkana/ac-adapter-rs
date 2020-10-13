use alg_traits::{Action, Assoc, Identity};
use query_test::Query;
use std::{marker::PhantomData, ops::Range};

#[query_test::query(fn(usize) -> T)]
pub struct Get<T>(PhantomData<T>);

#[query_test::query(fn(usize, T))]
pub struct Set<T>(PhantomData<T>);

#[query_test::query(fn(Range<usize>) -> T::Value)]
pub struct Fold<T: Identity>(PhantomData<T>);

#[query_test::query(fn(Range<usize>, P::Key) -> usize)]
pub struct SearchForward<T: Identity, P: Pred<Value = T::Value>>(PhantomData<(T, P)>);

#[query_test::query(fn(Range<usize>, P::Key) -> usize)]
pub struct SearchBackward<T: Identity, P: Pred<Value = T::Value>>(PhantomData<(T, P)>);

#[query_test::query(fn(Range<usize>, <A as Assoc>::Value))]
pub struct RangeApply<A: Action>(PhantomData<A>);

pub trait Proj {
    type From;
    type To;
    fn proj(from: &Self::From) -> Self::To;
}

pub trait Pred {
    type Value;
    type Key;
    fn pred(value: &Self::Value, key: &Self::Key) -> bool;
}

pub mod projs {
    use super::Proj;
    use std::marker::PhantomData;

    pub struct Copy<T>(PhantomData<T>);
    impl<T: std::marker::Copy> Proj for Copy<T> {
        type From = T;
        type To = T;
        fn proj(x: &T) -> T {
            *x
        }
    }

    pub struct Clone<T>(PhantomData<T>);
    impl<T: std::clone::Clone> Proj for Clone<T> {
        type From = T;
        type To = T;
        fn proj(x: &T) -> T {
            x.clone()
        }
    }
}

pub mod preds {
    use super::Pred;
    use super::Proj;
    use std::marker::PhantomData;

    pub struct Lt<P: Proj>(PhantomData<P>);
    impl<P: Proj> Pred for Lt<P>
    where
        P::To: Ord,
    {
        type Value = P::From;
        type Key = P::To;
        fn pred(value: &P::From, key: &P::To) -> bool {
            &P::proj(value) < key
        }
    }

    pub struct Le<P: Proj>(PhantomData<P>);
    impl<P: Proj> Pred for Le<P>
    where
        P::To: Ord,
    {
        type Value = P::From;
        type Key = P::To;
        fn pred(value: &P::From, key: &P::To) -> bool {
            &P::proj(value) <= key
        }
    }
}

#[cfg(test)]
mod test {
    use super::Set;
    use assert_impl::assert_impl;
    use query_test::Query;

    #[test]
    fn test_impl() {
        assert_impl!(Query<Param = (usize, u32), Output = ()>: Set<u32>);
        assert_impl!(!Query<Param = ((usize, u32),), Output = ()>: Set<u32>);
    }
}
