use crate::LazySegtree;
use alg_traits::{Action, Identity};
use query_test::{solve, FromBrute};
use std::ops::Range;
use test_vector2::{queries, Vector};

impl<A, T> FromBrute for LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
{
    type Brute = Vector<T::Value>;
    fn from_brute(brute: &Vector<T::Value>) -> Self {
        Self::from_slice(&brute.0)
    }
}

impl<A, T> solve::Solve<queries::Get<T::Value>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
{
    fn solve(&self, i: usize) -> T::Value {
        self.get(i)
    }
}
impl<A, T> solve::Mutate<queries::Set<T::Value>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
{
    fn mutate(&mut self, (i, x): (usize, T::Value)) {
        self.set(i, x);
    }
}

impl<A, T> solve::Solve<queries::Fold<T>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
{
    fn solve(&self, range: Range<usize>) -> T::Value {
        self.fold(range)
    }
}

impl<A, T, U, P> solve::Solve<queries::SearchForward<T, U, P>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
    P: queries::Map<T::Value, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_forward(range, |t| P::map(t, &key))
    }
}

impl<A, T, U, P> solve::Solve<queries::SearchBackward<T, U, P>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
    P: queries::Map<T::Value, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_backward(range, |t| P::map(t, &key))
    }
}

impl<A, T> solve::Mutate<queries::RangeApply<A>> for LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
{
    fn mutate(&mut self, (range, a): (Range<usize>, A::Value)) {
        self.apply(range, a);
    }
}
