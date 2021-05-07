//! Union-find を用いて、「一度処理したところを処理しない」区間クエリを線形で処理します。
//!
//! # Usage
//!
//! [`RangeCheck`] を使いましょう。
//!
//! [`new`](RangeCheck::new) で構築して、[`check`](RangeCheck::check) でクエリ処理です。
//!
//!
//! # Example
//!
//! 例えば、配列と組み合わせることでno-update range-set query を処理できます。
//!
//! ```
//! use range_check::RangeCheck;
//!
//! struct NoUpdateRangeSet {
//!     seq: Vec<Option<usize>>,
//!     rc: RangeCheck,
//! }
//! impl NoUpdateRangeSet {
//!     fn set(&mut self, l: usize, r: usize, x: usize) {
//!         for i in self.rc.check(l..r) {
//!             assert!(self.seq[i].is_none());
//!             self.seq[i] = Some(x);
//!         }
//!     }
//! }
//!
//! let mut range_set = NoUpdateRangeSet {
//!     seq: vec![None; 5],
//!     rc: RangeCheck::new(5),
//! };
//!
//! range_set.set(1, 3, 0);
//! assert_eq!(range_set.seq, vec![None, Some(0), Some(0), None, None]);
//!
//! range_set.set(2, 4, 1);
//! assert_eq!(range_set.seq, vec![None, Some(0), Some(0), Some(1), None]);
//!
//! range_set.set(0, 5, 2);
//! assert_eq!(range_set.seq, vec![Some(2), Some(0), Some(0), Some(1), Some(2)]);
//! ```

use {
    std::ops::{Bound, Range, RangeBounds},
    union_find::UnionFind,
};

/// 「一度処理したところを処理しない」区間クエリを線形で処理するデータ構造です。
#[derive(Clone, Debug)]
pub struct RangeCheck {
    uf: UnionFind,
    rightmost: Vec<usize>,
}
impl RangeCheck {
    /// 区間 [0, n[ に対応するデータ構造を構築します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use range_check::RangeCheck;
    /// let rc = RangeCheck::new(10);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            uf: UnionFind::new(n + 1),
            rightmost: (0..=n).collect::<Vec<_>>(),
        }
    }
    /// 区間 `range` をチェックして、未チェックだった場所をすべて返すイテレータを作ります。
    ///
    /// # 計算量
    ///
    /// 出力 1 つにつき、償却 Θ ( α ( n ) )
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use range_check::RangeCheck;
    ///
    /// let mut rc = RangeCheck::new(10);
    /// assert_eq!(rc.check(3..5).collect::<Vec<_>>(), vec![3, 4]);
    /// assert_eq!(rc.check(4..6).collect::<Vec<_>>(), vec![5]);
    /// ```
    ///
    pub fn check(&mut self, range: impl RangeBounds<usize>) -> Iter<'_> {
        let n = self.rightmost.len() - 1;
        let Range { mut start, end } = open(range, n);
        start = self.rightmost[self.uf.find(start)];
        Iter {
            range_check: self,
            start,
            end,
        }
    }
}

/// [`RangeCheck::check`] が返すイテレータです。
#[derive(Debug)]
pub struct Iter<'a> {
    range_check: &'a mut RangeCheck,
    start: usize,
    end: usize,
}
impl Iterator for Iter<'_> {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            range_check,
            start,
            end,
        } = self;
        if *start < *end {
            let ans = *start;
            let next = range_check.rightmost[range_check.uf.find(*start + 1)];
            range_check.uf.union(*start, next);
            range_check.rightmost[range_check.uf.find(next)] = next;
            *start = next;
            Some(ans)
        } else {
            None
        }
    }
}

fn open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
    (match range.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    })..match range.end_bound() {
        Bound::Excluded(&x) => x,
        Bound::Included(&x) => x + 1,
        Bound::Unbounded => len,
    }
}

#[cfg(test)]
mod tests {
    use {
        super::RangeCheck,
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::SubRange,
        std::mem::replace,
    };

    #[test]
    fn test_range_check() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..30);
            let mut range_check = RangeCheck::new(n);
            let mut a = vec![false; n];
            for _ in 0..2 * n {
                let range = rng.sample(SubRange(0..n));
                let result = range_check.check(range.clone()).collect::<Vec<_>>();
                let mut expected = Vec::new();
                for i in range {
                    if !replace(&mut a[i], true) {
                        expected.push(i);
                    }
                }
                assert_eq!(result, expected);
            }
        }
    }
}
