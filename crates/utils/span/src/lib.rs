#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! slice の機能を増やします。
//! 詳しくは [`Span`] をご覧ください。
//!
//! [`Span`]: trait.Span.html

use std::{cmp, ops};

impl<T> Span<T> for [T] {
    #[inline]
    fn span_len(&self) -> usize {
        self.len()
    }

    #[inline]
    fn span_is_empty(&self) -> bool {
        self.is_empty()
    }

    #[inline]
    fn span_sort(&mut self)
    where
        T: cmp::Ord,
    {
        self.sort()
    }

    #[inline]
    fn span_sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&T, &T) -> cmp::Ordering,
    {
        self.sort_by(compare)
    }

    #[inline]
    fn span_sort_by_key<K, F>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: cmp::Ord,
    {
        self.sort_by_key(f)
    }
}

/// slice の機能を増やします。
pub trait Span<T>: ops::Index<usize, Output = T> {
    /// 長さです。
    fn span_len(&self) -> usize;

    /// 空であるです。
    fn span_is_empty(&self) -> bool {
        self.span_len() == 0
    }

    /// 要素の sort をします。
    fn span_sort(&mut self)
    where
        T: cmp::Ord;

    /// 比較関数を用いて要素の sort をします。
    fn span_sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&T, &T) -> cmp::Ordering;

    /// キー抽出関数を用いて要素の sort をします。
    fn span_sort_by_key<K, F>(&mut self, f: F)
    where
        F: FnMut(&T) -> K,
        K: cmp::Ord;

    /// 逆順でソートします。
    fn sort_reverse(&mut self)
    where
        T: cmp::Ord,
    {
        self.span_sort_by(|a, b| a.cmp(b).reverse())
    }

    /// 比較関数を用いて逆順でソートします。
    fn sort_reverse_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> cmp::Ordering,
    {
        self.span_sort_by(|a, b| compare(a, b).reverse())
    }

    /// キー抽出関数を用いて逆順でソートします。
    fn sort_reverse_by_key<K, F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> K,
        K: cmp::Ord,
    {
        self.span_sort_by_key(|x| cmp::Reverse(f(x)))
    }

    /// 二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use span::Span;
    ///
    /// let s = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = 13;
    /// assert_eq!(s.lower_bound(&seek), 9);
    /// let seek = 4;
    /// assert_eq!(s.lower_bound(&seek), 7);
    /// let seek = 100;
    /// assert_eq!(s.lower_bound(&seek), 13);
    /// let seek = 1;
    /// assert_eq!(s.lower_bound(&seek), 1);
    /// ```
    #[inline]
    fn lower_bound<'a>(&'a self, x: &Self::Output) -> usize
    where
        T: Ord,
    {
        self.lower_bound_by(|p| p.cmp(x))
    }

    /// キー抽出関数を用いて二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use span::Span;
    /// use std::clone::Clone;
    ///
    /// let s = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = 13;
    /// assert_eq!(s.lower_bound_by_key(&seek, Clone::clone), 9);
    /// let seek = 4;
    /// assert_eq!(s.lower_bound_by_key(&seek, Clone::clone), 7);
    /// let seek = 100;
    /// assert_eq!(s.lower_bound_by_key(&seek, Clone::clone), 13);
    /// let seek = 1;
    /// assert_eq!(s.lower_bound_by_key(&seek, Clone::clone), 1);
    /// ```
    #[inline]
    fn lower_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
    where
        F: FnMut(&T) -> B,
        B: Ord,
    {
        self.lower_bound_by(|x| f(x).cmp(b))
    }

    /// 比較関数を用いて二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use span::Span;
    ///
    /// let s = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = 13;
    /// assert_eq!(s.lower_bound_by(|probe| probe.cmp(&seek)), 9);
    /// let seek = 4;
    /// assert_eq!(s.lower_bound_by(|probe| probe.cmp(&seek)), 7);
    /// let seek = 100;
    /// assert_eq!(s.lower_bound_by(|probe| probe.cmp(&seek)), 13);
    /// let seek = 1;
    /// assert_eq!(s.lower_bound_by(|probe| probe.cmp(&seek)), 1);
    /// ```
    #[inline]
    fn lower_bound_by<F>(&self, mut f: F) -> usize
    where
        F: FnMut(&T) -> cmp::Ordering,
    {
        self.span_partition_point(|x| f(x) == cmp::Ordering::Less)
    }

    /// 二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use span::Span;
    ///
    /// let s = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = 13;
    /// assert_eq!(s.upper_bound(&seek), 10);
    /// let seek = 4;
    /// assert_eq!(s.upper_bound(&seek), 7);
    /// let seek = 100;
    /// assert_eq!(s.upper_bound(&seek), 13);
    /// let seek = 1;
    /// assert_eq!(s.upper_bound(&seek), 5);
    /// ```
    #[inline]
    fn upper_bound<'a>(&'a self, x: &Self::Output) -> usize
    where
        Self::Output: Ord,
    {
        self.upper_bound_by(|p| p.cmp(x))
    }

    /// キー抽出関数を用いて二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use span::Span;
    /// use std::clone::Clone;
    ///
    /// let s = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = 13;
    /// assert_eq!(s.upper_bound_by_key(&seek, Clone::clone), 10);
    /// let seek = 4;
    /// assert_eq!(s.upper_bound_by_key(&seek, Clone::clone), 7);
    /// let seek = 100;
    /// assert_eq!(s.upper_bound_by_key(&seek, Clone::clone), 13);
    /// let seek = 1;
    /// assert_eq!(s.upper_bound_by_key(&seek, Clone::clone), 5);
    /// ```
    #[inline]
    fn upper_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
    where
        F: FnMut(&T) -> B,
        B: Ord,
    {
        self.upper_bound_by(|x| f(x).cmp(b))
    }

    /// 比較関数を用いて二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use span::Span;
    ///
    /// let s = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = 13;
    /// assert_eq!(s.upper_bound_by(|probe| probe.cmp(&seek)), 10);
    /// let seek = 4;
    /// assert_eq!(s.upper_bound_by(|probe| probe.cmp(&seek)), 7);
    /// let seek = 100;
    /// assert_eq!(s.upper_bound_by(|probe| probe.cmp(&seek)), 13);
    /// let seek = 1;
    /// assert_eq!(s.upper_bound_by(|probe| probe.cmp(&seek)), 5);
    /// ```
    #[inline]
    fn upper_bound_by<F>(&self, mut f: F) -> usize
    where
        F: FnMut(&T) -> cmp::Ordering,
    {
        self.span_partition_point(|x| f(x) != cmp::Ordering::Greater)
    }

    /// [`slice::partition_point`] と同じです。
    ///
    /// # Examples
    ///
    /// ```
    /// use span::Span;
    ///
    /// let v = [1, 2, 3, 3, 5, 6, 7];
    /// let i = v.span_partition_point(|&x| x < 5);
    ///
    /// assert_eq!(i, 4);
    /// assert!(v[..i].iter().all(|&x| x < 5));
    /// assert!(v[i..].iter().all(|&x| !(x < 5)));
    /// ```
    /// [`slice::partition_point`]: https://doc.rust-lang.org/std/primitive.slice.html#method.partition_point
    fn span_partition_point<F>(&self, mut pred: F) -> usize
    where
        F: FnMut(&T) -> bool,
    {
        let mut left = 0;
        let mut right = self.span_len();
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
