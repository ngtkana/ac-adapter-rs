use crate::LazySegtree;
use alg_traits::{Action, Identity};
use query_test::{solve, FromBrute};
use std::ops::Range;
use test_vector2::{queries, Vector};

impl<A, T> FromBrute for LazySegtree<A, T>
where
    A: Action<Point = T::Value>,
    T: Identity,
{
    type Brute = Vector<T>;
    fn from_brute(brute: &Vector<T>) -> Self {
        Self::from_slice(&brute.0)
    }
}

impl<A, T> solve::Mutate<queries::Set<T::Value>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value>,
    T: Identity,
{
    fn mutate(&mut self, (i, x): (usize, T::Value)) {
        self.set(i, x);
    }
}

impl<A, T> solve::Solve<queries::Fold<T::Value>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value>,
    T: Identity,
{
    fn solve(&self, range: Range<usize>) -> T::Value {
        self.fold(range)
    }
}

impl<A, T, U, P> solve::Solve<queries::SearchForward<T::Value, U, P>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value>,
    T: Identity,
    P: queries::Pred<T::Value, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_forward(range, |t| P::pred(t, &key))
    }
}

impl<A, T, U, P> solve::Solve<queries::SearchBackward<T::Value, U, P>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value>,
    T: Identity,
    P: queries::Pred<T::Value, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_backward(range, |t| P::pred(t, &key))
    }
}
