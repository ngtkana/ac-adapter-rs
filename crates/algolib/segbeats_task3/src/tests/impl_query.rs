use super::{
    queries::{ChangeMax, ChangeMin, CountChanges, QueryMax, QueryMin},
    vector::Vector,
};
use crate::{Elm, Segbeats};
use query_test::{
    solve::{Mutate, Solve},
    FromBrute,
};
use std::ops::Range;

// -- solve
impl<T: Elm> Mutate<ChangeMin<T>> for Segbeats<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.change_min(range, x);
    }
}
impl<T: Elm> Mutate<ChangeMax<T>> for Segbeats<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.change_max(range, x);
    }
}
impl<T: Elm> Solve<QueryMin<T>> for Segbeats<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.query_min(range)
    }
}
impl<T: Elm> Solve<QueryMax<T>> for Segbeats<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.query_max(range)
    }
}
impl<T: Elm> Solve<CountChanges> for Segbeats<T> {
    fn solve(&self, range: Range<usize>) -> u64 {
        self.count_changes(range)
    }
}

// -- from brute
impl<T: Elm> FromBrute for Segbeats<T> {
    type Brute = Vector<(T, u64)>;
    fn from_brute(src: &Vector<(T, u64)>) -> Self {
        let src = src.0.iter().map(|&(x, _)| x).collect::<Vec<_>>();
        Self::new(&src)
    }
}
