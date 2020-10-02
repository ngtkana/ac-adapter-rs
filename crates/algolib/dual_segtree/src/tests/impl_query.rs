use crate::{DualSegtree, DualSegtreeWith};
use query_test_2::{query, solve, FromBrute, Vector};
use std::ops::Range;
use type_traits::{actions::Adj, Action, Identity};

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

impl<T: Action + Identity> FromBrute for DualSegtreeWith<T> {
    type Brute = Vector<T::Space>;
    fn from_brute(_brute: &Self::Brute) -> Self {
        todo!()
    }
}
impl<T: Action + Identity> solve::SolveMut<query::Get<T::Space>> for DualSegtreeWith<T> {
    fn solve_mut(&mut self, _i: usize) -> T::Space {
        todo!()
    }
}
impl<T: Action + Identity> solve::Mutate<query::RangeApply<T>> for DualSegtreeWith<T> {
    fn mutate(&mut self, (_range, _action): (Range<usize>, T)) {
        todo!()
    }
}
