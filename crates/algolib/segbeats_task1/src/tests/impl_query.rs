use super::{
    queries::{ChangeMax, ChangeMin, QueryMax, QuerySum},
    vector::Vector,
};
use crate::{Elm, SegbeatsTask1};
use query_test::{
    solve::{Mutate, Solve},
    FromBrute,
};
use std::ops::Range;

// -- solve
impl<T: Elm> Mutate<ChangeMin<T>> for SegbeatsTask1<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.change_min(range, x);
    }
}
impl<T: Elm> Mutate<ChangeMax<T>> for SegbeatsTask1<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.change_max(range, x);
    }
}
impl<T: Elm> Solve<QueryMax<T>> for SegbeatsTask1<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.query_max(range)
    }
}
impl<T: Elm> Solve<QuerySum<T>> for SegbeatsTask1<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.query_sum(range)
    }
}

// -- from brute
impl<T: Elm> FromBrute for SegbeatsTask1<T> {
    type Brute = Vector<T>;
    fn from_brute(src: &Vector<T>) -> Self {
        Self::new(&src.0)
    }
}
