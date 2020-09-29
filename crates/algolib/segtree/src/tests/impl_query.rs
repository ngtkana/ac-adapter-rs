use crate::Segtree;
use query_test_2::{
    query::{Fold, ForwardUpperBoundByKey, Get, Project, Set},
    FromBrute, Solve, SolveGet, SolveMut, Vector,
};
use type_traits::{Assoc, Identity};

impl<T: Assoc> FromBrute for Segtree<T> {
    type Brute = Vector<T>;
    fn from_brute(brute: &Self::Brute) -> Self {
        Segtree::from_slice(&brute.0)
    }
}
impl<T: Assoc> SolveGet<Get<T>> for Segtree<T> {
    fn solve_get(&self, i: usize) -> &T {
        self.get(i)
    }
}
impl<T: Assoc> SolveMut<Set<T>> for Segtree<T> {
    fn solve_mut(&mut self, (i, x): (usize, T)) {
        self.set(i, x);
    }
}
impl<T: Identity> Solve<Fold<T>> for Segtree<T> {
    fn solve(&self, range: std::ops::Range<usize>) -> T {
        self.fold(range)
    }
}
impl<T, U, P> Solve<ForwardUpperBoundByKey<T, U, P>> for Segtree<T>
where
    T: Identity,
    U: Ord,
    P: Project<T, U>,
{
    fn solve(&self, (start, value): (usize, U)) -> usize {
        self.forward_upper_bound_by_key(start, &value, |x| P::project(x.clone()))
    }
}
