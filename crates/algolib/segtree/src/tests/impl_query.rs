use crate::Segtree;
use query_test::{query, solve, utils, FromBrute};
use std::ops::Range;
use test_vector::Vector;
use type_traits::{Assoc, Identity};

impl<T: Assoc> FromBrute for Segtree<T> {
    type Brute = Vector<T>;
    fn from_brute(brute: &Self::Brute) -> Self {
        Segtree::from_slice(&brute.0)
    }
}
impl<T: Assoc> solve::Solve<query::Get<T>> for Segtree<T> {
    fn solve(&self, i: usize) -> T {
        self.get(i).clone()
    }
}
impl<T: Assoc> solve::Mutate<query::Set<T>> for Segtree<T> {
    fn mutate(&mut self, (i, x): (usize, T)) {
        self.set(i, x);
    }
}
impl<T: Identity> solve::Solve<query::Fold<T>> for Segtree<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.fold(range)
    }
}
impl<T, U, P> solve::Solve<query::ForwardUpperBoundByKey<T, U, P>> for Segtree<T>
where
    T: Identity,
    U: Ord,
    P: utils::Project<T, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_forward(range, |x| P::project(x.clone()) <= key)
    }
}
impl<T, U, P> solve::Solve<query::BackwardUpperBoundByKey<T, U, P>> for Segtree<T>
where
    T: Identity,
    U: Ord,
    P: utils::Project<T, U>,
{
    fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
        self.search_backward(range, |x| P::project(x.clone()) <= key)
    }
}
