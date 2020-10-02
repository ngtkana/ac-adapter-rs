use crate::DualSegtree;
use query_test_2::{query, solve, FromBrute, Vector};
use std::ops::Range;
use type_traits::{actions::Adj, Identity};

impl<T: Identity> FromBrute for DualSegtree<T> {
    type Brute = Vector<T>;
    fn from_brute(brute: &Self::Brute) -> Self {
        Self::from_slice(&brute.0)
    }
}
impl<T: Identity> solve::SolveMut<query::Get<T>> for DualSegtree<T> {
    fn solve_mut(&mut self, i: usize) -> T {
        self.get(i).clone()
    }
}
impl<T: Identity> solve::Mutate<query::RangeApply<Adj<T>>> for DualSegtree<T> {
    fn mutate(&mut self, (range, action): (Range<usize>, Adj<T>)) {
        self.apply(range, action.0)
    }
}
