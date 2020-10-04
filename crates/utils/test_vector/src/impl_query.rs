use super::Vector;
use queries::utils;
use query_test::solve;
use std::ops::Range;
use type_traits::{Action, Identity};

impl<T> solve::Mutate<queries::Set<T>> for Vector<T> {
    fn mutate(&mut self, (i, x): (usize, T)) {
        self.0[i] = x;
    }
}
impl<T: Identity> solve::Solve<queries::Fold<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range].iter().cloned().fold(T::identity(), T::op)
    }
}
impl<T, U, P> solve::Judge<queries::ForwardUpperBoundByKey<T, U, P>> for Vector<T>
where
    T: Identity,
    U: Ord,
    P: utils::Project<T, U>,
{
    fn judge(&self, (range, value): (Range<usize>, U), i: usize) -> bool {
        let fold = |range| P::project(<Self as solve::Solve<queries::Fold<T>>>::solve(self, range));
        let Range { start, end } = range;
        i == end || range.contains(&i) && (fold(start..i)..fold(start..i + 1)).contains(&value)
    }
}
impl<T, U, P> solve::Judge<queries::BackwardUpperBoundByKey<T, U, P>> for Vector<T>
where
    T: Identity,
    U: Ord,
    P: utils::Project<T, U>,
{
    fn judge(&self, (range, value): (Range<usize>, U), i: usize) -> bool {
        let fold = |range| P::project(<Self as solve::Solve<queries::Fold<T>>>::solve(self, range));
        let Range { start, end } = range;
        i == start || range.contains(&(i - 1)) && (fold(i..end)..fold(i - 1..end)).contains(&value)
    }
}
impl<T: Action> solve::Mutate<queries::RangeApply<T>> for Vector<T::Space> {
    fn mutate(&mut self, (range, action): (Range<usize>, T)) {
        self.0[range]
            .iter_mut()
            .for_each(|x| action.clone().act_mut(x));
    }
}
