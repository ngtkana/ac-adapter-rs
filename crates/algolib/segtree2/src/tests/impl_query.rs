use crate::Segtree;
use alg_traits::Identity;
use query_test::{solve, FromBrute};
use std::ops::Range;
use test_vector2::{queries, Vector};

impl<T: Identity> FromBrute for Segtree<T> {
    type Brute = Vector<T>;
    fn from_brute(brute: &Vector<T>) -> Self {
        Self::from_slice(&brute.0)
    }
}

impl<T: Identity> solve::Mutate<queries::Set<T::Value>> for Segtree<T> {
    fn mutate(&mut self, (i, x): (usize, T::Value)) {
        self.set(i, x);
    }
}

impl<T: Identity> solve::Solve<queries::Fold<T::Value>> for Segtree<T> {
    fn solve(&self, range: Range<usize>) -> T::Value {
        self.fold(range)
    }
}

impl<T, U, P> solve::Solve<queries::SearchForward<T::Value, U, P>> for Segtree<T>
where
    T: Identity,
    P: queries::Pred<T::Value, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_forward(range, |t| P::pred(t, &key))
    }
}

impl<T, U, P> solve::Solve<queries::SearchBackward<T::Value, U, P>> for Segtree<T>
where
    T: Identity,
    P: queries::Pred<T::Value, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_backward(range, |t| P::pred(t, &key))
    }
}
