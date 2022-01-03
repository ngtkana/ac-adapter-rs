//! ウェーブレット行列
//!
//! 本体は [`WaveletMatrix`] です。
//!
//!
//! # パフォーマンスについての実験結果
//!
//! 実はちゃんとした対照実験にはなっていませんが、気になったらそのとき
//! 頑張るということで……（あの？）
//!
//!
//! ## 実験 1: `sort_by_key` の代わりに `stable_partition_by_key` を自作
//!
//! 僅差ですが、自作のほうが若干速いようなので、そちらを採用しています。
//!
//! - [`std`] の `sort_by_key` (26 ms): <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6169045>
//! - 自作 `stable_partition_by_key` (22 ms): <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6169045>
//!
//!
//! ## 実験 2: 再帰の代わりにスタックを管理するイテレータを自作
//!
//! 僅差で自作の方が早かったですが、これはどちらにしてもないと [`spans`](WaveletMatrix::spans) の
//! 実装がつらそうですから、致命的に遅くなければ使うつもりでした。
//!
//! - AOJ 2674 - Disordered Data Detection
//!   - 再帰 (44 ms): <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6168530>
//!   - スタック (40 ms): <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6169694>
//!
//!
//! # このライブラリを使える問題
//!
//! - ECR 22 E - Army Creation
//!   - 問題: <http://codeforces.com/contest/813/problem/E>
//!   - 提出 (1117 ms): <http://codeforces.com/contest/813/submission/141316921>
//!   - 出題日: 2017-06-06
//!   - 難易度: そこそこ。
//!   - 制約: N, Q ≤ 100,000
//!   - 使用するメソッド: [`range_freq`](WaveletMatrix::range_freq)
//!   - コメント: 様々な解法があるよう。
//!   [こちらのブログ](https://blog.hamayanhamayan.com/entry/2017/06/13/103254)
//!   に各種手法お名前だけ言及ありです。
//! - yukicoder No.738 - 平らな農地
//!   - 問題: <https://yukicoder.me/problems/no/738>
//!   - 提出 (895 ms): <https://yukicoder.me/submissions/727730>
//!   - 出題日: 2018-09-28
//!   - 難易度: そこそこ。
//!   - 制約: N, Q ≤ 100,000
//!   - 使用するメソッド: [`range_freq`](WaveletMatrix::range_freq),
//!   [`spans`](WaveletMatrix::spans)
//!   - コメント: ヒープ４本でも解けてそちらのほうが一般的？
//!   ウェーブレット行列を使うなら累積和が必要で、ちょっと面倒です。
//!   （[自由度の高いメソッド `spans` が活躍します。](WaveletMatrix::spans)）
//! - yukicoder No.919 - You Are A Project Manager
//!   - 問題: <https://yukicoder.me/problems/no/919>
//!   - 提出 (256 ms): <https://yukicoder.me/submissions/727758>
//!   - 出題日: 2019-10-25
//!   - 難易度: そこそこ。
//!   - 制約: N, Q ≤ 100,000
//!   - 使用するメソッド: [`range_freq`](WaveletMatrix::range_freq),
//!   [`spans`](WaveletMatrix::spans)
//!   - コメント: Mo でもできて、それもそれできれいです。
//! - Library Checker - Range Kth Smallest
//!   - 問題: <https://judge.yosupo.jp/problem/range_kth_smallest>
//!   - 提出 (640 ms): <https://judge.yosupo.jp/submission/72220>
//!   - 出題日: 2020-02-08
//!   - 難易度: 易しめ。
//!   - 制約: N, Q ≤ 200,000
//!   - 使用するメソッド: [`quantile`](WaveletMatrix::quantile)
//! - OUPC 2020 D - 仲良しスライム
//!   - 問題: <https://onlinejudge.u-aizu.ac.jp/beta/room.html#OUPC2020/problems/D>
//!   - 提出 (440 ms): <https://onlinejudge.u-aizu.ac.jp/beta/review.html#OUPC2020/6171281>
//!   - 出題日: 2020-12-12
//!   - 難易度: 簡単。
//!   - 制約: N ≤ 100,000
//!   - 使う構造体: [`DoubleHeap`]
//!   - 他の解法:
//!     - ヒープ４本 (90 ms): <https://onlinejudge.u-aizu.ac.jp/beta/review.html#OUPC2020/6171242>
//!   - コメント: ヒープ４本のほうが楽です。
//! - AOJ 2674 - Disordered Data Detection
//!   - 問題: <https://judge.u-aizu.ac.jp/onlinejudge/description.jsp?id=2674>
//!   - 提出: <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6168530>
//!   - 出題日: 不明
//!   - 難易度: 易しめ。
//!   - 制約: N, Q ≤ 100,000
//!   - 使用するメソッド: [`range_freq`](WaveletMatrix::range_freq)
//! - AOJ 1549 - Hard Beans
//!   - 問題: <https://judge.u-aizu.ac.jp/onlinejudge/description.jsp?id=1549>
//!   - 提出: <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6168616>
//!   - 出題日: 不明
//!   - 難易度: 貼るだけ
//!   - 制約: N, Q ≤ 100,000
//!   - 使用するメソッド: [`next_value`](WaveletMatrix::next_value), [`prev_value`](WaveletMatrix::prev_value)
//! - AtCoder 競プロ典型 90 問 017 - Crossing Segments（★7）
//!   - 問題: <https://atcoder.jp/contests/typical90/tasks/typical90_q>
//!   - 提出 (549 ms): <https://atcoder.jp/contests/typical90/submissions/28306990>
//!   - 出題日: 2021-04-20
//!   - 難易度: 易しめ
//!   - 制約: N, Q ≤ 100,000
//!   - 使用するメソッド: [`range_freq`](WaveletMatrix::range_freq)
//!   - コメント: 想定は余事象を考えて RSQ
//!
#![allow(clippy::len_zero)]

use std::{
    fmt::Debug,
    iter::FromIterator,
    mem::size_of,
    ops::{Bound, Range, RangeBounds},
};

const UNIT: usize = size_of::<usize>();

/// ウェーブレット行列
///
/// [問題例などは `wavelet_matrix` クレートのドキュメントにあります。](crate)
///
#[derive(Clone, Default, Hash, PartialEq)]
pub struct WaveletMatrix {
    table: Vec<StaticBitVec>,
}
impl Debug for WaveletMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries((0..self.len()).map(|i| self.access(i)))
            .finish()
    }
}
impl FromIterator<usize> for WaveletMatrix {
    fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
        let mut slice = iter.into_iter().map(Into::into).collect::<Vec<_>>();
        Self::from_slice_of_usize_mut(&mut slice, |_| ())
    }
}
impl WaveletMatrix {
    /// 配列が空であれば `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let wm = WaveletMatrix::default();
    /// assert!(wm.is_empty());
    ///
    /// let wm = WaveletMatrix::from_iter(vec![0]);
    /// assert!(!wm.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }
    /// 配列の長さを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let wm = WaveletMatrix::default();
    /// assert_eq!(wm.len(), 0);
    ///
    /// assert_eq!(WaveletMatrix::from_iter(vec![42]).len(), 1);
    /// assert_eq!(WaveletMatrix::from_iter(vec![42, 45]).len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.table.first().map_or(0, |row| row.len())
    }
    /// 新しく構築するとともに、途中経過の配列をすべてベクターに詰めて返します。
    ///
    /// [用途は `spans` をご覧ください。](WaveletMatrix::spans)
    ///
    /// ある範囲の和を計算したいときなど、累積和やセグツリーなどと組み合わせて
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let (_wm, table) = WaveletMatrix::from_iter_collect_vec2(vec![2, 1, 3, 0]);
    /// let expected = vec![
    ///     vec![2, 1, 3, 0],
    ///     vec![1, 0, 2, 3],
    ///     vec![0, 2, 1, 3],
    /// ];
    /// assert_eq!(table, expected);
    /// ```
    pub fn from_iter_collect_vec2(
        iter: impl IntoIterator<Item = usize>,
    ) -> (Self, Vec<Vec<usize>>) {
        let mut slice = iter.into_iter().map(Into::into).collect::<Vec<_>>();
        let mut table = Vec::new();
        let wm = Self::from_slice_of_usize_mut(&mut slice, |row| table.push(row.to_vec()));
        (wm, table)
    }
    /// [特に高速化の意図がなければ、`FromIterator`
    /// を代わりにお使いください。](WaveletMatrix::from_iter)
    pub fn from_slice_of_usize_mut(
        slice: &mut [usize],
        mut callback: impl FnMut(&[usize]),
    ) -> Self {
        let ht = slice.iter().copied().max().map_or(0, |value| {
            // 要素がすべて 0 のときにも構築してほしいので、
            // 最低でも 1 の高さを持つようにします。
            ((value + 1).next_power_of_two().trailing_zeros() as usize).max(1)
        });
        let table = (0..ht)
            .rev()
            .map(|p| {
                callback(slice);
                let res = slice.iter().map(|&value| value >> p & 1 == 1).collect();
                stable_partition_by_key(slice, |value| value >> p & 1 == 1);
                res
            })
            .collect();
        callback(slice);
        Self { table }
    }
    /// `i` 番目の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let wm = WaveletMatrix::from_iter(vec![2, 1, 3, 0]);
    /// assert_eq!(wm.access(2), 3);
    /// ```
    pub fn access(&self, mut i: usize) -> usize {
        assert!(i < self.table[0].len());
        let mut ans = 0;
        for row in &self.table {
            let here = row.access(i);
            i = next_position(row, i, row.access(i));
            ans <<= 1;
            ans |= here as usize;
        }
        ans
    }
    /// `index` により指定された部分列のうち、
    /// `value` により指定された範囲に入っている要素の個数を返します。
    ///
    /// # Examples
    ///
    /// `i` 番目の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let wm = WaveletMatrix::from_iter(vec![2, 1, 3, 0]);
    /// assert_eq!(wm.range_freq(1.., 0..2), 2);
    /// ```
    pub fn range_freq(
        &self,
        index: impl RangeBounds<usize>,
        value: impl RangeBounds<usize>,
    ) -> usize {
        self.spans(index, value).map(|span| span.index.len()).sum()
    }
    /// `index` により指定された部分列のうち、
    /// `value` により指定された範囲に入っている最小の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let wm = WaveletMatrix::from_iter(vec![2, 1, 3, 0]);
    /// assert_eq!(wm.next_value(1.., ..2), Some(0));
    /// assert_eq!(wm.next_value(1.., 2..3), None);
    /// ```
    pub fn next_value(
        &self,
        index: impl RangeBounds<usize>,
        value: impl RangeBounds<usize>,
    ) -> Option<usize> {
        self.root(open(index, self.len()))
            .next_value(&open(value, self.lim()))
    }
    /// `index` により指定された部分列のうち、
    /// `value` により指定された範囲に入っている最小の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let wm = WaveletMatrix::from_iter(vec![2, 1, 3, 0]);
    /// assert_eq!(wm.prev_value(1.., ..2), Some(1));
    /// assert_eq!(wm.prev_value(1.., 2..3), None);
    /// ```
    pub fn prev_value(
        &self,
        index: impl RangeBounds<usize>,
        value: impl RangeBounds<usize>,
    ) -> Option<usize> {
        self.root(open(index, self.len()))
            .prev_value(&open(value, self.lim()))
    }
    /// `index` により指定された部分列のうち、
    /// `value` により指定された範囲に入っている中で、
    /// 0-based index で `k` 番目に小さい要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let wm = WaveletMatrix::from_iter(vec![2, 1, 3, 0]);
    /// assert_eq!(wm.quantile(0, .., ..), Some(0));
    /// assert_eq!(wm.quantile(1, .., ..), Some(1));
    /// ```
    pub fn quantile(
        &self,
        k: usize,
        index: impl RangeBounds<usize>,
        value: impl RangeBounds<usize>,
    ) -> Option<usize> {
        self.root(open(index, self.len()))
            .quantile(k, &open(value, self.lim()))
            .ok()
    }
    /// 対応する部分を、`(depth, index_range, value_range)` の形のものに分解します。
    ///
    /// [`Spans`] は [`SpanInNode`] を返すイテレータです。
    /// [`SpanInNode`] のフィールドはパブリックなのでそこから情報を
    /// 得てください。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use wavelet_matrix::WaveletMatrix;
    /// let a = vec![5, 4, 5, 5, 2, 1, 5, 6, 1, 3, 5, 0];
    /// let (wm, table) = WaveletMatrix::from_iter_collect_vec2(a.clone());
    ///
    /// assert_eq!(&a[3..10], &[5, 2, 1, 5, 6, 1, 3]);
    /// let spans = wm.spans(3..9, 3..6);
    /// let mut sorted = wm
    ///     .spans(3..10, 3..6)
    ///     .flat_map(|span| table[span.depth][span.index.clone()].iter().copied())
    ///     .collect::<Vec<_>>();
    /// sorted.sort();
    /// assert_eq!(&sorted, &[3, 5, 5]);
    /// ```
    ///
    pub fn spans(
        &self,
        index: impl RangeBounds<usize>,
        value: impl RangeBounds<usize>,
    ) -> Spans<'_> {
        let index = open(index, self.len());
        let target = open(value, self.lim());
        if target.len() == 0 {
            return Spans {
                stack: Vec::new(),
                target,
            };
        }
        let mut current = self.root(index);
        let mut stack = Vec::new();
        while !is_subrange_of(&current.value, &target) {
            let left = current.left_down();
            if is_disjoint_with(&left.value, &target) {
                current = current.right_down();
            } else {
                stack.push(current);
                current = left;
            }
        }
        stack.push(current);
        Spans { stack, target }
    }
    fn lim(&self) -> usize {
        1 << self.table.len()
    }
    fn root(&self, index: Range<usize>) -> SpanInNode<'_> {
        SpanInNode {
            wm: self,
            depth: 0,
            index,
            value: 0..self.lim(),
        }
    }
}

fn stable_partition_by_key(slice: &mut [usize], is_upper: impl Fn(usize) -> bool) -> usize {
    let mut upper = Vec::new();
    let mut i = 0;
    for j in 0..slice.len() {
        if is_upper(slice[j]) {
            upper.push(slice[j]);
        } else {
            slice[i] = slice[j];
            i += 1;
        }
    }
    slice[i..].copy_from_slice(&upper);
    i
}

fn next_position(row: &StaticBitVec, i: usize, which: bool) -> usize {
    match which {
        false => i - row.rank(i),
        true => row.len() - row.rank(row.len()) + row.rank(i),
    }
}
fn next_position_range(row: &StaticBitVec, range: &Range<usize>, which: bool) -> Range<usize> {
    next_position(row, range.start, which)..next_position(row, range.end, which)
}

/// 累積和のできる静的なビットベクター
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct StaticBitVec {
    len: usize,
    rank: Vec<usize>,
    pattern: Vec<usize>,
}
impl FromIterator<bool> for StaticBitVec {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        let mut rank = Vec::new();
        let mut pattern = Vec::new();
        let mut rank_c = 0;
        let mut pattern_c = 0;
        let mut len = 0;
        'OUTER: loop {
            rank.push(rank_c);
            for i in 0..UNIT {
                match iter.next() {
                    None => {
                        pattern.push(pattern_c);
                        break 'OUTER;
                    }
                    Some(false) => (),
                    Some(true) => {
                        pattern_c |= 1 << i;
                        rank_c += 1;
                    }
                }
                len += 1;
            }
            pattern.push(pattern_c);
            pattern_c = 0;
        }
        Self { len, rank, pattern }
    }
}
impl StaticBitVec {
    /// `a.is_empty()`
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// `a.len()`
    pub fn len(&self) -> usize {
        self.len
    }
    /// `a[i]`
    pub fn access(&self, i: usize) -> bool {
        assert!(i < self.len);
        let (q, r) = divrem(i, UNIT);
        self.pattern[q] >> r & 1 == 1
    }
    /// `sum(a[..end])`
    pub fn rank(&self, end: usize) -> usize {
        assert!(end <= self.len);
        let (q, r) = divrem(end, UNIT);
        self.rank[q] + (self.pattern[q] & ((1 << r) - 1)).count_ones() as usize
    }
    /// min i s.t. `target <= sum(a[..i])`
    pub fn select(&self, target: usize) -> usize {
        if target == 0 {
            return 0;
        }
        let mut lr = 0..self.rank.len();
        while 1 < lr.len() {
            let c = midpoint(&lr);
            *if self.rank[c] < target {
                &mut lr.start
            } else {
                &mut lr.end
            } = c;
        }
        let q = lr.start;
        let mut lr = 0..UNIT;
        while 1 < lr.len() {
            let c = midpoint(&lr);
            *if (self.rank[q] + (self.pattern[q] & ((1 << c) - 1)).count_ones() as usize) < target {
                &mut lr.start
            } else {
                &mut lr.end
            } = c;
        }
        q * UNIT + lr.end
    }
}

/// イテレータです [詳しくは `WaveletMatrix::spans` をご覧ください。](WaveletMatrix::spans)
#[derive(Clone, Debug, Hash, PartialEq)]
pub struct Spans<'a> {
    stack: Vec<SpanInNode<'a>>,
    target: Range<usize>,
}
impl<'a> Iterator for Spans<'a> {
    type Item = SpanInNode<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let ans = self.stack.pop()?;
        if ans.value.end == self.target.end {
            self.stack.clear();
        } else {
            let prev = self.stack.pop().unwrap();
            let mut next = prev.right_down();
            self.stack.push(next.clone());
            while !is_subrange_of(&next.value, &self.target) {
                next = next.left_down();
                self.stack.push(next.clone());
            }
        }
        Some(ans)
    }
}

/// [`Spans`] のアイテム型です。[詳しくは `WaveletMatrix::spans` をご覧ください。](WaveletMatrix::spans)
#[derive(Clone, Debug, Hash, PartialEq)]
pub struct SpanInNode<'a> {
    wm: &'a WaveletMatrix,
    /// ウェーブレット行列内の `i` 座標
    pub depth: usize,
    /// ウェーブレット行列内の `j` 座標の範囲
    pub index: Range<usize>,
    /// 現在のノードの担当する値の範囲
    pub value: Range<usize>,
}
impl<'a> SpanInNode<'a> {
    fn left_down(&self) -> Self {
        Self {
            wm: self.wm,
            depth: self.depth + 1,
            index: next_position_range(&self.wm.table[self.depth], &self.index, false),
            value: self.value.start..midpoint(&self.value),
        }
    }
    fn right_down(&self) -> Self {
        Self {
            wm: self.wm,
            depth: self.depth + 1,
            index: next_position_range(&self.wm.table[self.depth], &self.index, true),
            value: midpoint(&self.value)..self.value.end,
        }
    }
    fn next_value(&self, target: &Range<usize>) -> Option<usize> {
        if is_disjoint_with(&self.value, target) || self.index.len() == 0 {
            None
        } else if self.value.len() == 1 {
            Some(self.value.start)
        } else {
            self.left_down()
                .next_value(target)
                .or_else(|| self.right_down().next_value(target))
        }
    }
    fn prev_value(&self, target: &Range<usize>) -> Option<usize> {
        if is_disjoint_with(&self.value, target) || self.index.len() == 0 {
            None
        } else if self.value.len() == 1 {
            Some(self.value.start)
        } else {
            self.right_down()
                .prev_value(target)
                .or_else(|| self.left_down().prev_value(target))
        }
    }
    fn quantile(&self, k: usize, target: &Range<usize>) -> Result<usize, usize> {
        let ans = if is_disjoint_with(&self.value, target) {
            Err(0)
        } else if is_subrange_of(&self.value, target) && self.index.len() <= k {
            Err(self.index.len())
        } else if self.value.len() == 1 {
            Ok(self.value.start)
        } else {
            self.left_down().quantile(k, target).or_else(|len| {
                self.right_down()
                    .quantile(k - len, target)
                    .map_err(|e| e + len)
            })
        };
        ans
    }
}

fn midpoint(range: &Range<usize>) -> usize {
    range.start + (range.end - range.start) / 2
}

fn is_disjoint_with(lhs: &Range<usize>, rhs: &Range<usize>) -> bool {
    lhs.end <= rhs.start || rhs.end <= lhs.start
}

fn is_subrange_of(lhs: &Range<usize>, rhs: &Range<usize>) -> bool {
    rhs.start <= lhs.start && lhs.end <= rhs.end
}

fn divrem(num: usize, den: usize) -> (usize, usize) {
    let q = num / den;
    (q, num - q * den)
}
fn open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
    (match range.start_bound() {
        Bound::Included(&l) => l.min(len),
        Bound::Excluded(&l) => (l + 1).min(len),
        Bound::Unbounded => 0,
    })..(match range.end_bound() {
        Bound::Included(&r) => (r + 1).min(len),
        Bound::Excluded(&r) => r.min(len),
        Bound::Unbounded => len,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::{iproduct, Itertools};
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use std::iter::repeat_with;

    const H: usize = 3;
    const W: usize = 12;
    const SAMPLE_ROWS: [[usize; W]; H + 1] = [
        [5, 4, 5, 5, 2, 1, 5, 6, 1, 3, 5, 0],
        [2, 1, 1, 3, 0, 5, 4, 5, 5, 5, 6, 5],
        [1, 1, 0, 5, 4, 5, 5, 5, 5, 2, 3, 6],
        [0, 4, 2, 6, 1, 1, 5, 5, 5, 5, 5, 3],
    ];
    const SAMPLE: [usize; W] = SAMPLE_ROWS[0];

    #[test]
    fn test_stable_partition_by_key() {
        let mut rng = StdRng::seed_from_u64(42);
        let n = 12;
        let mut a = (0..n)
            .map(|i| i * 2 + rng.gen_bool(0.5) as usize)
            .collect_vec();
        let mut b = a.clone();
        a.sort_by_key(|&x| x & 1);
        stable_partition_by_key(&mut b, |x| x & 1 == 1);
        assert_eq!(a, b);
    }

    #[test]
    fn test_static_bitvec_small() {
        for n in 0..=8_usize {
            for bs in 0..1_u32 << n {
                let bitvec = (0..n).map(|i| bs >> i & 1 == 1).collect::<StaticBitVec>();

                // access
                for i in 0..n {
                    let expected = bs >> i & 1 == 1;
                    assert_eq!(bitvec.access(i), expected);
                }

                // rank
                for i in 0..=n {
                    let expected = (bs & ((1 << i) - 1)).count_ones() as usize;
                    assert_eq!(bitvec.rank(i), expected);
                }

                // select
                for j in 0..=bs.count_ones() as usize {
                    let expected = (0..).find(|&i| j <= bitvec.rank(i)).unwrap();
                    assert_eq!(bitvec.select(j), expected);
                }
            }
        }
    }

    #[test]
    fn test_static_bitvec_large() {
        let mut rng = StdRng::seed_from_u64(42);
        for &(n, p) in &[(9, 0.5), (15, 0.5), (300, 0.5), (300, 0.1), (300, 0.9)] {
            for _ in 0..20 {
                let vec = repeat_with(|| rng.gen_bool(p)).take(n).collect_vec();
                let bitvec = vec.iter().copied().collect::<StaticBitVec>();

                // access
                for (i, &expected) in vec.iter().enumerate() {
                    assert_eq!(bitvec.access(i), expected);
                }

                // rank
                for i in 0..=n {
                    let expected = vec[..i].iter().filter(|&&b| b).count();
                    assert_eq!(bitvec.rank(i), expected);
                }

                // select
                let count = vec.iter().filter(|&&b| b).count();
                for j in 0..=count {
                    let expected = (0..).find(|&i| j <= bitvec.rank(i)).unwrap();
                    assert_eq!(bitvec.select(j), expected);
                }
            }
        }
    }

    #[test]
    fn test_wavelet_matrix_construction() {
        #[rustfmt::skip]
        let expected = vec![
            "111100110010",
            "100100000010",
            "110101111010",
        ];
        let expected = expected
            .iter()
            .map(|row| row.chars().map(|c| c == '1').collect_vec())
            .collect_vec();
        let (wm, table) = WaveletMatrix::from_iter_collect_vec2(SAMPLE.iter().copied());
        assert_eq!(table, SAMPLE_ROWS);

        assert_eq!(wm.table.len(), H);
        for (i, row) in wm.table.iter().enumerate() {
            assert_eq!(row.len(), W);
            for j in 0..W {
                assert_eq!(row.access(j), expected[i][j]);
            }
        }
    }

    #[test]
    fn test_spans() {
        let wm = SAMPLE.iter().copied().collect::<WaveletMatrix>();
        for (index, value) in iproduct!(
            (0..=W + 1).tuple_combinations().map(|(l, r)| l..r - 1),
            (0..=1 << H).tuple_combinations().map(|(l, r)| l..r - 1)
        ) {
            let expected = SAMPLE[index.clone()]
                .iter()
                .copied()
                .filter(|&x| value.contains(&x))
                .sorted()
                .collect_vec();
            let spans = wm.spans(index.clone(), value.clone()).collect::<Vec<_>>();
            let result = spans
                .iter()
                .flat_map(|span| {
                    SAMPLE_ROWS[span.depth][span.index.clone()]
                        .iter()
                        .copied()
                        .sorted()
                })
                .collect_vec();
            assert_eq!(result, expected);
            if value.is_empty() {
                assert!(spans.is_empty());
            } else {
                assert_eq!(spans.first().unwrap().value.start, value.start);
                assert_eq!(spans.last().unwrap().value.end, value.end);
                for v in spans.windows(2) {
                    assert_eq!(v[0].value.end, v[1].value.start);
                }
            }
        }
    }

    #[test]
    fn test_wavelet_matrix() {
        let wm = SAMPLE.iter().copied().collect::<WaveletMatrix>();
        let n = SAMPLE.len();
        let m = 8;

        // access
        for (i, &expected) in SAMPLE.iter().enumerate() {
            assert_eq!(wm.access(i), expected);
        }

        // ソートした部分列に対するクエリ
        for (index, value) in iproduct!(
            (0..=n + 1).tuple_combinations().map(|(l, r)| l..r - 1),
            (0..=m + 1).tuple_combinations().map(|(l, r)| l..r - 1)
        ) {
            let sorted = SAMPLE[index.clone()]
                .iter()
                .copied()
                .filter(|&x| value.contains(&x))
                .sorted()
                .collect_vec();

            // range_freq
            let expected = sorted.len();
            assert_eq!(wm.range_freq(index.clone(), value.clone()), expected);

            // next_value
            let expected = sorted.first().copied();
            assert_eq!(wm.next_value(index.clone(), value.clone()), expected);

            // prev_value
            let expected = sorted.last().copied();
            assert_eq!(wm.prev_value(index.clone(), value.clone()), expected);

            // quantile
            for k in 0..=index.len() {
                let expected = sorted.get(k).copied();
                assert_eq!(wm.quantile(k, index.clone(), value.clone()), expected);
            }
        }
    }
}
