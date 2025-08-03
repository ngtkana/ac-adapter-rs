use std::cmp::Ordering;
use std::cmp::Ordering::Equal;
use std::cmp::Ordering::Greater;
use std::cmp::Ordering::Less;

/// `{lower,upper}_bound`, etc
pub trait SliceBinarySearch<T> {
    fn partition_point<F: FnMut(&T) -> bool>(&self, pred: F) -> usize;
    fn partition_point_value<F: FnMut(&T) -> bool>(&self, pred: F) -> Option<&T>;
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
    fn lower_bound_value_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> Option<&T> {
        self.partition_point_value(|x| f(x) < Equal)
    }
    fn upper_bound_value_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> Option<&T> {
        self.partition_point_value(|x| f(x) <= Equal)
    }
    fn lower_bound_value_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> Option<&T> {
        self.lower_bound_value_by(|x| f(x).cmp(b))
    }
    fn upper_bound_value_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> Option<&T> {
        self.upper_bound_value_by(|x| f(x).cmp(b))
    }
    fn lower_bound_value(&self, x: &T) -> Option<&T>
    where
        T: Ord,
    {
        self.lower_bound_value_by(|p| p.cmp(x))
    }
    fn upper_bound_value(&self, x: &T) -> Option<&T>
    where
        T: Ord,
    {
        self.upper_bound_value_by(|p| p.cmp(x))
    }
}

impl<T> SliceBinarySearch<T> for [T] {
    fn partition_point<F: FnMut(&T) -> bool>(&self, mut pred: F) -> usize {
        self.binary_search_by(|x| if pred(x) { Less } else { Greater })
            .unwrap_err()
    }

    fn partition_point_value<F: FnMut(&T) -> bool>(&self, pred: F) -> Option<&T> {
        self.get(self.partition_point(pred))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_binary_search() {
        let array = [10, 12];

        assert_eq!(array.lower_bound(&9), 0);
        assert_eq!(array.lower_bound(&10), 0);
        assert_eq!(array.lower_bound(&11), 1);
        assert_eq!(array.lower_bound(&12), 1);
        assert_eq!(array.lower_bound(&13), 2);

        assert_eq!(array.upper_bound(&9), 0);
        assert_eq!(array.upper_bound(&10), 1);
        assert_eq!(array.upper_bound(&11), 1);
        assert_eq!(array.upper_bound(&12), 2);
        assert_eq!(array.upper_bound(&13), 2);

        assert_eq!(array.lower_bound_value(&9), Some(&10));
        assert_eq!(array.lower_bound_value(&10), Some(&10));
        assert_eq!(array.lower_bound_value(&11), Some(&12));
        assert_eq!(array.lower_bound_value(&12), Some(&12));
        assert_eq!(array.lower_bound_value(&13), None);

        assert_eq!(array.upper_bound_value(&9), Some(&10));
        assert_eq!(array.upper_bound_value(&10), Some(&12));
        assert_eq!(array.upper_bound_value(&11), Some(&12));
        assert_eq!(array.upper_bound_value(&12), None);
        assert_eq!(array.upper_bound_value(&13), None);
    }
}
