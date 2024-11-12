//! Future and otherworldly Rust features.

use std::cmp::Ordering;
use std::cmp::Ordering::Equal;
use std::cmp::Ordering::Greater;
use std::cmp::Ordering::Less;
use std::collections::BinaryHeap;

/// Removes and returns the "top" element in a vector if the predicate
/// returns `true`, or [`None`] if the predicate returns false or the container
/// is empty.
///
/// # Examples
///
/// ```
/// use riff::PopIf;
///
/// let mut vec = vec![1, 2, 3, 4];
/// let pred = |x: &mut i32| *x % 2 == 0;
///
/// assert_eq!(vec.pop_if(pred), Some(4));
/// assert_eq!(vec, [1, 2, 3]);
/// assert_eq!(vec.pop_if(pred), None);
/// ```
pub trait PopIf {
    type Value;

    fn pop_if<F>(&mut self, f: F) -> Option<Self::Value>
    where
        F: FnOnce(&mut Self::Value) -> bool;
}

impl<T> PopIf for Vec<T> {
    type Value = T;

    fn pop_if<F>(&mut self, f: F) -> Option<Self::Value>
    where
        F: FnOnce(&mut Self::Value) -> bool,
    {
        if f(self.last_mut()?) {
            self.pop()
        } else {
            None
        }
    }
}

impl<T: Ord> PopIf for BinaryHeap<T> {
    type Value = T;

    fn pop_if<F>(&mut self, f: F) -> Option<Self::Value>
    where
        F: FnOnce(&mut Self::Value) -> bool,
    {
        if f(&mut *self.peek_mut()?) {
            self.pop()
        } else {
            None
        }
    }
}

/// Method versions of functions.
pub trait BinarySearch<T> {
    fn partition_point<F: FnMut(&T) -> bool>(&self, pred: F) -> usize;
    fn lower_bound_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> usize {
        self.partition_point(|x| f(x) < Equal)
    }
    fn upper_bound_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> usize {
        self.partition_point(|x| f(x) <= Equal)
    }
    fn lower_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> usize {
        self.lower_bound_by(|x| f(x).cmp(b))
    }
    fn upper_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> usize {
        self.upper_bound_by(|x| f(x).cmp(b))
    }
    fn lower_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        self.lower_bound_by(|p| p.cmp(x))
    }
    fn upper_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        self.upper_bound_by(|p| p.cmp(x))
    }
}

impl<T> BinarySearch<T> for [T] {
    fn partition_point<F: FnMut(&T) -> bool>(&self, mut pred: F) -> usize {
        self.binary_search_by(|x| if pred(x) { Less } else { Greater })
            .unwrap_err()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec_pop_if() {
        fn is_even(x: &mut u32) -> bool {
            *x % 2 == 0
        }
        fn run(mut vec: Vec<u32>) -> (Vec<u32>, Option<u32>) {
            let result = vec.pop_if(is_even);
            (vec, result)
        }
        assert_eq!(run(vec![]), (vec![], None));
        assert_eq!(run(vec![0]), (vec![], Some(0)));
        assert_eq!(run(vec![1]), (vec![1], None));
        assert_eq!(run(vec![0, 2]), (vec![0], Some(2)));
        assert_eq!(run(vec![0, 3]), (vec![0, 3], None));
        assert_eq!(run(vec![1, 2]), (vec![1], Some(2)));
        assert_eq!(run(vec![1, 3]), (vec![1, 3], None));
    }

    #[test]
    fn test_heap_pop_if() {
        fn is_even(x: &mut u32) -> bool {
            *x % 2 == 0
        }
        fn run(vec: Vec<u32>) -> (Vec<u32>, Option<u32>) {
            let mut heap = vec.into_iter().collect::<BinaryHeap<_>>();
            let result = heap.pop_if(is_even);
            let mut vec = heap.into_vec();
            vec.sort_unstable();
            (vec, result)
        }
        assert_eq!(run(vec![]), (vec![], None));
        assert_eq!(run(vec![0]), (vec![], Some(0)));
        assert_eq!(run(vec![1]), (vec![1], None));
        assert_eq!(run(vec![0, 2]), (vec![0], Some(2)));
        assert_eq!(run(vec![0, 3]), (vec![0, 3], None));
        assert_eq!(run(vec![1, 2]), (vec![1], Some(2)));
        assert_eq!(run(vec![1, 3]), (vec![1, 3], None));
    }

    #[test]
    fn test_vec_binary_search() {
        let vec = vec![10, 12];
        assert_eq!(vec.lower_bound(&9), 0);
        assert_eq!(vec.lower_bound(&10), 0);
        assert_eq!(vec.lower_bound(&11), 1);
        assert_eq!(vec.lower_bound(&12), 1);
        assert_eq!(vec.lower_bound(&13), 2);
        assert_eq!(vec.upper_bound(&9), 0);
        assert_eq!(vec.upper_bound(&10), 1);
        assert_eq!(vec.upper_bound(&11), 1);
        assert_eq!(vec.upper_bound(&12), 2);
        assert_eq!(vec.upper_bound(&13), 2);
    }
}
