use std::cmp::Ordering;
use std::cmp::Ordering::Equal;
use std::cmp::Ordering::Greater;
use std::cmp::Ordering::Less;

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
