use super::{
    queries::{ChangeMax, ChangeMin, QueryMax, QueryMin, QuerySum, RangeAdd},
    vector::Vector,
};
use crate::{Segbeats, Value};
use query_test::{
    solve::{Mutate, Solve},
    FromBrute,
};
use std::ops::Range;

// -- solve
impl<T: Value> Mutate<ChangeMin<T>> for Segbeats<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.change_min(range, x);
    }
}
impl<T: Value> Mutate<ChangeMax<T>> for Segbeats<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.change_max(range, x);
    }
}
impl<T: Value> Mutate<RangeAdd<T>> for Segbeats<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.range_add(range, x);
    }
}
impl<T: Value> Solve<QueryMin<T>> for Segbeats<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.query_min(range)
    }
}
impl<T: Value> Solve<QueryMax<T>> for Segbeats<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.query_max(range)
    }
}
impl<T: Value> Solve<QuerySum<T>> for Segbeats<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.query_sum(range)
    }
}

// -- from brute
impl<T: Value> FromBrute for Segbeats<T> {
    type Brute = Vector<T>;
    fn from_brute(src: &Vector<T>) -> Self {
        Self::new(&src.0)
    }
}
