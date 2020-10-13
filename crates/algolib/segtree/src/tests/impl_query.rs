use crate::Segtree;
use alg_traits::Identity;
use queries::{Fold, Pred, SearchBackward, SearchForward, Set};
use query_test::{solve, FromBrute};
use std::ops::Range;
use test_vector::{queries, Vector};

impl<T: Identity> FromBrute for Segtree<T> {
    type Brute = Vector<T::Value>;
    fn from_brute(brute: &Vector<T::Value>) -> Self {
        Self::from_slice(&brute.0)
    }
}

impl<T: Identity> solve::Mutate<Set<T::Value>> for Segtree<T> {
    fn mutate(&mut self, (i, x): (usize, T::Value)) {
        self.set(i, x);
    }
}

impl<T: Identity> solve::Solve<Fold<T>> for Segtree<T> {
    fn solve(&self, range: Range<usize>) -> T::Value {
        self.fold(range)
    }
}

impl<T, P> solve::Solve<SearchForward<T, P>> for Segtree<T>
where
    T: Identity,
    P: Pred<Value = T::Value>,
    P::Key: PartialEq,
{
    fn solve(&self, (range, key): (Range<usize>, P::Key)) -> usize {
        self.search_forward(range, |t| P::pred(t, &key))
    }
}

impl<T, P> solve::Solve<SearchBackward<T, P>> for Segtree<T>
where
    T: Identity,
    P: Pred<Value = T::Value>,
    P::Key: PartialEq,
{
    fn solve(&self, (range, key): (Range<usize>, P::Key)) -> usize {
        self.search_backward(range, |t| P::pred(t, &key))
    }
}
