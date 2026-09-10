use std::cmp::Ordering;
use std::cmp::Ordering::Equal;
use std::cmp::Ordering::Greater;
use std::cmp::Ordering::Less;

/// ソート済みスライスに対する `lower_bound` / `upper_bound` 系の二分探索をまとめたトレイト。
///
/// 述語 `pred` が `self` 上で単調（`true` が続いた後 `false` が続く）であることを前提に、
/// その境界位置を二分探索で求める（`std::slice::binary_search_by` を利用）。
///
/// # 例
///
/// ```
/// use jolt::SliceBinarySearch;
/// let a = [10, 12];
/// assert_eq!(a.lower_bound(&11), 1); // 11 以上が現れる最初の位置
/// assert_eq!(a.upper_bound(&10), 1); // 10 より大きい値が現れる最初の位置
/// ```
pub trait SliceBinarySearch<T> {
    /// 述語 $\mathrm{pred}$ が `true` から `false` に変わる境界位置（`true` の個数）を返す。
    fn partition_point<F: FnMut(&T) -> bool>(&self, pred: F) -> usize;
    /// [`partition_point`](Self::partition_point) の境界位置にある要素を返す。範囲外なら `None`。
    fn partition_point_value<F: FnMut(&T) -> bool>(&self, pred: F) -> Option<&T>;
    /// $f(x) < \mathrm{Equal}$ が成り立つ最初の位置（下限）を返す。
    fn lower_bound_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> usize {
        self.partition_point(|x| f(x) < Equal)
    }
    /// $f(x) \le \mathrm{Equal}$ が成り立つ最初の位置（上限）を返す。
    fn upper_bound_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> usize {
        self.partition_point(|x| f(x) <= Equal)
    }
    /// キー $f(x)$ が `b` 以上になる最初の位置を返す。
    fn lower_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> usize {
        self.lower_bound_by(|x| f(x).cmp(b))
    }
    /// キー $f(x)$ が `b` より大きくなる最初の位置を返す。
    fn upper_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> usize {
        self.upper_bound_by(|x| f(x).cmp(b))
    }
    /// $x$ 以上の値が現れる最初の位置を返す。
    fn lower_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        self.lower_bound_by(|p| p.cmp(x))
    }
    /// $x$ より大きい値が現れる最初の位置を返す。
    fn upper_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        self.upper_bound_by(|p| p.cmp(x))
    }
    /// [`lower_bound_by`](Self::lower_bound_by) の位置にある要素を返す。範囲外なら `None`。
    fn lower_bound_value_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> Option<&T> {
        self.partition_point_value(|x| f(x) < Equal)
    }
    /// [`upper_bound_by`](Self::upper_bound_by) の位置にある要素を返す。範囲外なら `None`。
    fn upper_bound_value_by<F: FnMut(&T) -> Ordering>(&self, mut f: F) -> Option<&T> {
        self.partition_point_value(|x| f(x) <= Equal)
    }
    /// [`lower_bound_by_key`](Self::lower_bound_by_key) の位置にある要素を返す。範囲外なら `None`。
    fn lower_bound_value_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> Option<&T> {
        self.lower_bound_value_by(|x| f(x).cmp(b))
    }
    /// [`upper_bound_by_key`](Self::upper_bound_by_key) の位置にある要素を返す。範囲外なら `None`。
    fn upper_bound_value_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, mut f: F) -> Option<&T> {
        self.upper_bound_value_by(|x| f(x).cmp(b))
    }
    /// $x$ 以上の値が現れる最初の要素を返す。範囲外なら `None`。
    fn lower_bound_value(&self, x: &T) -> Option<&T>
    where
        T: Ord,
    {
        self.lower_bound_value_by(|p| p.cmp(x))
    }
    /// $x$ より大きい値が現れる最初の要素を返す。範囲外なら `None`。
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
