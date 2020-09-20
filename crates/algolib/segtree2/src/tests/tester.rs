use super::*;
use std::fmt;

pub(super) fn gen_instance<'a, Q, T, R>(
    range: ops::Range<usize>,
    rng: &'a mut R,
    _marker: PhantomData<Q>,
) -> query_test::Instance<Q, Brute<T>, Segtree<T>>
where
    T: Sized + Assoc + fmt::Debug,
    R: Sized + Rng,
    Q: Sized + SegQuery<'a, Value = T, Rng = R>,
{
    let len = rng.gen_range(range.start, range.end);
    let mut query = Q::new(len, rng);
    let a = query.construct();
    println!("Generated an instance: {:?}", &a);
    query_test::Instance {
        query,
        brute: Brute::from_slice(&a),
        fast: Segtree::from_slice(&a),
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct Brute<T>(Vec<T>);
impl<T: Assoc> Brute<T> {
    pub fn from_slice(src: &[T]) -> Self {
        Self(src.to_vec())
    }

    pub fn set(&mut self, i: usize, x: T) {
        self.0[i] = x;
    }

    pub fn get(&mut self, i: usize) -> &T {
        &self.0[i]
    }

    #[allow(dead_code)]
    pub fn modify(&mut self, i: usize, f: impl Fn(&mut T)) {
        f(&mut self.0[i])
    }

    pub fn fold(&self, range: impl ops::RangeBounds<usize>) -> Option<T> {
        let (start, end) = open(self.0.len(), range);
        if start == end {
            None
        } else {
            let init = self.0[start].clone();
            Some(
                self.0[start + 1..end]
                    .iter()
                    .fold(init, |x, y| x.op(y.clone())),
            )
        }
    }
    pub fn forward_partition_point(&self, start: usize, mut pred: impl FnMut(&T) -> bool) -> usize {
        if !pred(&self.0[start]) {
            start
        } else {
            let mut current = self.0[start].clone();
            (start + 1..)
                .find(|&i| {
                    i == self.0.len() || {
                        current = current.clone().op(self.0[i].clone());
                        !pred(&current)
                    }
                })
                .unwrap()
        }
    }
    pub fn backward_partition_point(&self, end: usize, mut pred: impl FnMut(&T) -> bool) -> usize {
        if !pred(&self.0[end - 1]) {
            end
        } else {
            let mut current = self.0[end - 1].clone();
            (0..end)
                .rev()
                .find(|&i| {
                    i == 0 || {
                        current = self.0[i - 1].clone().op(current.clone());
                        !pred(&current)
                    }
                })
                .unwrap_or(0)
        }
    }
}

impl<T: Assoc + Ord> Brute<T> {
    pub fn forward_lower_bound(&self, start: usize, value: &T) -> usize {
        self.forward_partition_point(start, |x| x < value)
    }
    pub fn forward_upper_bound(&self, start: usize, value: &T) -> usize {
        self.forward_partition_point(start, |x| x <= value)
    }
    pub fn backward_lower_bound(&self, end: usize, value: &T) -> usize {
        self.backward_partition_point(end, |x| x < value)
    }
    pub fn backward_upper_bound(&self, end: usize, value: &T) -> usize {
        self.backward_partition_point(end, |x| x <= value)
    }
}

pub(super) trait SegQuery<'a> {
    type Value: Assoc;
    type Rng: Rng;

    // Required methods
    fn new(len: usize, rng: &'a mut Self::Rng) -> Self;
    fn rng(&mut self) -> &mut Self::Rng;
    fn len(&self) -> usize;
    fn gen_value(&mut self) -> Self::Value;

    // Helper methods
    fn gen_index(&mut self) -> usize {
        let len = self.len();
        self.rng().gen_range(0, len)
    }
    fn gen_range(&mut self) -> ops::Range<usize> {
        let u = self.gen_index();
        let v = self.gen_index();
        u.min(v)..u.max(v)
    }

    // Useful methods
    fn construct(&mut self) -> Vec<Self::Value> {
        let len = self.len();
        iter::repeat_with(|| self.gen_value()).take(len).collect()
    }
    fn set(&mut self) -> (usize, Self::Value) {
        let i = self.gen_index();
        let x = self.gen_value();
        (i, x)
    }
    fn get(&mut self) -> usize {
        self.gen_index()
    }
    fn fold(&mut self) -> ops::Range<usize> {
        self.gen_range()
    }
}

pub(super) trait SegBinSearchQuery<'a>: SegQuery<'a> {
    // Required methods
    fn gen_ge_nonempty_folded_value(&mut self) -> Self::Value;
    fn gen_gt_nonempty_folded_value(&mut self) -> Self::Value;

    // Useful methods
    fn forward_lower_bound(&mut self) -> (usize, Self::Value) {
        (self.gen_index(), self.gen_gt_nonempty_folded_value())
    }
    fn forward_upper_bound(&mut self) -> (usize, Self::Value) {
        (self.gen_index(), self.gen_ge_nonempty_folded_value())
    }
    fn backward_lower_bound(&mut self) -> (usize, Self::Value) {
        (self.gen_index() + 1, self.gen_gt_nonempty_folded_value())
    }
    fn backward_upper_bound(&mut self) -> (usize, Self::Value) {
        (self.gen_index() + 1, self.gen_ge_nonempty_folded_value())
    }
}
