use std::{cmp, ops};

impl<T> Span<T> for [T] {
    fn __span_internal_len(&self) -> usize {
        self.len()
    }

    fn __span_internal_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn __span_internal_sort(&mut self)
    where
        T: cmp::Ord,
    {
        self.sort()
    }

    fn __span_internal_sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&T, &T) -> cmp::Ordering,
    {
        self.sort_by(compare)
    }

    fn __span_internal_sort_by_key<K, F>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: cmp::Ord,
    {
        self.sort_by_key(f)
    }
}

pub trait Span<T>: ops::Index<usize, Output = T> {
    fn __span_internal_len(&self) -> usize;

    fn __span_internal_is_empty(&self) -> bool {
        self.__span_internal_len() == 0
    }

    fn __span_internal_sort(&mut self)
    where
        T: cmp::Ord;

    fn __span_internal_sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&T, &T) -> cmp::Ordering;

    fn __span_internal_sort_by_key<K, F>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: cmp::Ord;

    fn sort_reverse(&mut self)
    where
        T: cmp::Ord,
    {
        self.__span_internal_sort_by(|a, b| a.cmp(b).reverse())
    }

    fn sort_reverse_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> cmp::Ordering,
    {
        self.__span_internal_sort_by(|a, b| compare(a, b).reverse())
    }

    fn sort_reverse_by_key<K, F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> K,
        K: cmp::Ord,
    {
        self.__span_internal_sort_by_key(|x| cmp::Reverse(f(x)))
    }

    fn lower_bound(&self, x: &Self::Output) -> usize
    where
        T: Ord,
    {
        self.lower_bound_by(|p| p.cmp(x))
    }

    fn lower_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
    where
        F: FnMut(&T) -> B,
        B: Ord,
    {
        self.lower_bound_by(|x| f(x).cmp(b))
    }

    fn lower_bound_by<F>(&self, mut f: F) -> usize
    where
        F: FnMut(&T) -> cmp::Ordering,
    {
        self.partition_point(|x| f(x) == cmp::Ordering::Less)
    }

    fn upper_bound(&self, x: &Self::Output) -> usize
    where
        Self::Output: Ord,
    {
        self.upper_bound_by(|p| p.cmp(x))
    }

    fn upper_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
    where
        F: FnMut(&T) -> B,
        B: Ord,
    {
        self.upper_bound_by(|x| f(x).cmp(b))
    }

    fn upper_bound_by<F>(&self, mut f: F) -> usize
    where
        F: FnMut(&T) -> cmp::Ordering,
    {
        self.partition_point(|x| f(x) != cmp::Ordering::Greater)
    }

    fn partition_point<F>(&self, mut pred: F) -> usize
    where
        F: FnMut(&T) -> bool,
    {
        let mut left = 0;
        let mut right = self.__span_internal_len();
        while left != right {
            let mid = left + (right - left) / 2;
            let value = &self[mid];
            if pred(value) {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        left
    }
}
