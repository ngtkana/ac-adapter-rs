use crate::{queries, traits::Identity, vector::Vector, Segtree};
use query_test::{solve, FromBrute};
use std::ops::Range;

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
