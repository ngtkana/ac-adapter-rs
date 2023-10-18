//! Union-find を用いて、「一度処理したところを処理しない」区間クエリを線形で処理します。
//!
//! # データ構造の定義
//!
//! ブーリアン配列に対応しており、指定した位置の `false` -> `true`
//! の変更（これをチェックと呼びます。→ [`check`](UfChecklist::check)）
//! 指定した位置と同じかもっと右にある `false` の場所を答えるのを高速に処理できます。（→
//! [`lower_bound`](UfChecklist::lower_bound)）
//!
//! これを利用すると、指定した範囲をすべて `true` にするというのも高速になります。（→
//! [`range_check`](UfChecklist::range_check)）
//!
//!
//! # Usage
//!
//! [`UfChecklist`] を使いましょう。
//!
//!
//! ## 構築
//!
//! * [`new`](UfChecklist::new): 新しいデータ構造を構築します。
//!
//!
//! ## 更新
//!
//! * [`check`](UfChecklist::check): 指定した位置をチェックします。
//! * [`range_check`](UfChecklist::range_check): 指定した範囲をチェックします。
//!
//!
//! ## クエリ
//!
//! * [`lower_bound`](UfChecklist::lower_bound):
//! 指定した場所と同じかもっと右にある未チェックな項
//! を探します。
//! * [`is_checked`](UfChecklist::is_checked): 指定した位置がチェック済みかどうかを判定します。
//!
//!
//! # Example
//!
//! 例えば、配列と組み合わせることでno-update range-set query を処理できます。
//!
//! ```
//! use uf_checklist::UfChecklist;
//!
//! struct NoUpdateRangeSet {
//!     seq: Vec<Option<usize>>,
//!     rc: UfChecklist,
//! }
//! impl NoUpdateRangeSet {
//!     fn set(&mut self, l: usize, r: usize, x: usize) {
//!         for i in self.rc.range_check(l..r) {
//!             assert!(self.seq[i].is_none());
//!             self.seq[i] = Some(x);
//!         }
//!     }
//! }
//!
//! let mut range_set = NoUpdateRangeSet {
//!     seq: vec![None; 5],
//!     rc: UfChecklist::new(5),
//! };
//!
//! range_set.set(1, 3, 0);
//! assert_eq!(range_set.seq, vec![None, Some(0), Some(0), None, None]);
//!
//! range_set.set(2, 4, 1);
//! assert_eq!(range_set.seq, vec![None, Some(0), Some(0), Some(1), None]);
//!
//! range_set.set(0, 5, 2);
//! assert_eq!(range_set.seq, vec![
//!     Some(2),
//!     Some(0),
//!     Some(0),
//!     Some(1),
//!     Some(2)
//! ]);
//! ```

use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;
use union_find::UnionFind;

/// 「一度処理したところを処理しない」区間クエリを線形で処理するデータ構造です。
#[derive(Clone, Debug)]
pub struct UfChecklist {
    uf: UnionFind,
    rightmost: Vec<usize>,
}
impl UfChecklist {
    /// 区間 [0, n[ に対応するデータ構造を構築します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use uf_checklist::UfChecklist;
    /// let rc = UfChecklist::new(10);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            uf: UnionFind::new(n + 1),
            rightmost: (0..=n).collect::<Vec<_>>(),
        }
    }

    /// 区間 `range` をチェックして、未チェックだった場所をすべて返すイテレータを作ります。
    ///
    /// # Panics
    ///
    /// 範囲外
    ///
    ///
    /// # 計算量
    ///
    /// 出力 1 つにつき、償却 Θ ( α ( n ) )
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use uf_checklist::UfChecklist;
    ///
    /// let mut rc = UfChecklist::new(10);
    /// assert_eq!(rc.range_check(3..5).collect::<Vec<_>>(), vec![3, 4]);
    /// assert_eq!(rc.range_check(4..6).collect::<Vec<_>>(), vec![5]);
    /// ```
    pub fn range_check(&mut self, range: impl RangeBounds<usize>) -> Iter<'_> {
        let n = self.rightmost.len() - 1;
        let Range { mut start, end } = open(range, n);
        assert!(
            start <= end && end <= n,
            "範囲外です。start = {}, end = {}, n = {}",
            start,
            end,
            n
        );
        start = __next_unckecked_cell(self, start);
        Iter {
            range_check: self,
            start,
            end,
        }
    }

    /// 指定した場所かそれより右の未チェックな位置が、存在すれば返し、なければ [`None`]
    /// を返します。
    ///
    /// # Panics
    ///
    /// 範囲外
    ///
    ///
    /// # 計算量
    ///
    /// 償却 Θ ( α ( n ) )
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use uf_checklist::UfChecklist;
    ///
    /// let mut rc = UfChecklist::new(10);
    /// rc.check(3);
    /// rc.check(4);
    /// rc.check(8);
    /// rc.check(9);
    ///
    /// assert_eq!(rc.lower_bound(3), Some(5));
    /// assert_eq!(rc.lower_bound(6), Some(6));
    /// assert_eq!(rc.lower_bound(8), None);
    /// ```
    pub fn lower_bound(&self, i: usize) -> Option<usize> {
        let n = self.rightmost.len() - 1;
        assert!(i < n, "範囲外です。 i = {}, n = {}", i, n);
        let i = __next_unckecked_cell(self, i);
        if i == self.rightmost.len() - 1 {
            None
        } else {
            Some(i)
        }
    }

    /// 指定した場所がチェック済みならば `true` を、さもなくば `false` を返します。
    ///
    ///
    /// # Panics
    ///
    /// 範囲外
    ///
    ///
    /// # 計算量
    ///
    /// 償却 Θ ( α ( n ) )
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use uf_checklist::UfChecklist;
    ///
    /// let mut rc = UfChecklist::new(10);
    /// rc.check(3);
    /// rc.check(4);
    /// rc.check(8);
    /// rc.check(9);
    ///
    /// assert_eq!(rc.is_checked(3), true);
    /// assert_eq!(rc.is_checked(6), false);
    /// ```
    pub fn is_checked(&self, i: usize) -> bool {
        let n = self.rightmost.len() - 1;
        assert!(i < n, "範囲外です。 i = {}, n = {}", i, n);
        self.rightmost[self.uf.find(i)] != i
    }

    /// 指定した場所をチェックします。
    ///
    /// # Panics
    ///
    /// 範囲外
    ///
    ///
    /// # Returns
    ///
    /// * すでにチェックした箇所の場合 -> `true`
    /// * さもなくば -> `false`
    ///
    /// です。[`replace`](std::mem::replace)
    /// とは逆ですが、[`HashSet::insert`](std::collections::HashSet::insert) とは同じです。
    ///
    ///
    /// # 計算量
    ///
    /// 償却 Θ ( α ( n ) )
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use uf_checklist::UfChecklist;
    ///
    /// let mut rc = UfChecklist::new(10);
    /// assert_eq!(rc.check(3), true);
    /// assert_eq!(rc.check(4), true);
    ///
    /// assert_eq!(rc.check(3), false);
    /// assert_eq!(rc.check(5), true);
    /// ```
    pub fn check(&mut self, i: usize) -> bool {
        let n = self.rightmost.len() - 1;
        assert!(i < n, "範囲外です。 i = {}, n = {}", i, n);
        if self.rightmost[self.uf.find(i)] == i {
            let next = __next_unckecked_cell(self, i + 1);
            self.uf.union(i, next);
            self.rightmost[self.uf.find(next)] = next;
            true
        } else {
            false
        }
    }
}

fn __next_unckecked_cell(range_check: &UfChecklist, i: usize) -> usize {
    range_check.rightmost[range_check.uf.find(i)]
}

/// [`UfChecklist::range_check`] が返すイテレータです。
#[derive(Debug)]
pub struct Iter<'a> {
    range_check: &'a mut UfChecklist,
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
            let check_result = range_check.check(*start);
            assert!(check_result);
            let next = __next_unckecked_cell(range_check, *start);
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
    use super::UfChecklist;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use randtools::SubRange;
    use std::mem::replace;

    #[test]
    fn test_range_check() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..30);
            let mut range_check = UfChecklist::new(n);
            let mut a = vec![false; n];
            for _ in 0..2 * n {
                match rng.gen_range(0..3) {
                    // range_check
                    0 => {
                        let range = rng.sample(SubRange(0..n));
                        let result = range_check.range_check(range.clone()).collect::<Vec<_>>();
                        let mut expected = Vec::new();
                        for i in range {
                            if !replace(&mut a[i], true) {
                                expected.push(i);
                            }
                        }
                        assert_eq!(result, expected);
                    }
                    // is_checked
                    1 => {
                        let i = rng.gen_range(0..n);
                        let result = range_check.is_checked(i);
                        let expected = a[i];
                        assert_eq!(result, expected);
                    }
                    // check
                    2 => {
                        let i = rng.gen_range(0..n);
                        if !a[i] {
                            a[i] = true;
                            range_check.check(i);
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
