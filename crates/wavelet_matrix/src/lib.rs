//! ウェーブレット行列
//!
//! 本体は [`WaveletMatrix`] です。
//!
//!
//! # このライブラリを使える問題
//!
//! - AOJ 2674: Disordered Data Detection
//!   - 問題: <https://judge.u-aizu.ac.jp/onlinejudge/description.jsp?id=2674>
//!   - 提出: <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6168530>
//!   - 難易度: 貼るだけ
//!   - 使用するメソッド: [`range_freq`](WaveletMatrix::range_freq)
//!
//! - AOJ 1549: Hard Beans
//!   - 問題: <https://judge.u-aizu.ac.jp/onlinejudge/description.jsp?id=1549>
//!   - 提出: <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6168616>
//!   - 難易度: 貼るだけ
//!   - 使用するメソッド: [`next_value`](WaveletMatrix::next_value), [`prev_value`](WaveletMatrix::prev_value)
//!
//!
//! # パフォーマンスについての実験結果
//!
//! ## 実験 1: `sort_by_key` の代わりに `stable_partition_by_key` を自作
//!
//! 僅差ですが、自作のほうが若干速いようなので、そちらを採用しています。
//!
//! - [`std`] の `sort_by_key` (26 ms): <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6169044>
//! - 自作 `stable_partition_by_key` (22 ms): <https://judge.u-aizu.ac.jp/onlinejudge/review.jsp?rid=6169045>

use std::{
    fmt::Debug,
    iter::FromIterator,
    mem::size_of,
    ops::{Bound, Range, RangeBounds},
};

const UNIT: usize = size_of::<usize>();

/// ウェーブレット行列
///
/// [詳しいことは `wavelet_matrix` クレートのドキュメントにあります。](crate)
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
        Self::from_slice_of_usize_mut(&mut slice)
    }
}
impl WaveletMatrix {
    /// `a.is_empty()`
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }
    /// `a.len()`
    pub fn len(&self) -> usize {
        self.table.first().map_or(0, |row| row.len())
    }
    /// `a.iter().all(|&x| x < lim)` を満たす最小の２冪 `lim`
    pub fn lim(&self) -> usize {
        1 << self.table.len()
    }
    /// 特に高速化の意図がなければ、[`FromIterator`] を代わりにお使いください。
    pub fn from_slice_of_usize_mut(slice: &mut [usize]) -> Self {
        let ht = slice.iter().copied().max().map_or(0, |value| {
            (value + 1).next_power_of_two().trailing_zeros() as usize
        });
        let table = (0..ht)
            .rev()
            .map(|p| {
                let res = slice.iter().map(|&value| value >> p & 1 == 1).collect();
                stable_partition_by_key(slice, |value| value >> p & 1 == 1);
                res
            })
            .collect();
        Self { table }
    }
    /// `a[i]`
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
    /// `a[pos_range]` の要素のうち、`value_range` に含まれるものの個数。
    /// `a[l..r].iter().filter(|&&x| value_range.contains(&x)).count()` と等価
    ///
    pub fn range_freq(
        &self,
        pos_range: impl RangeBounds<usize>,
        value_range: impl RangeBounds<usize>,
    ) -> usize {
        fn range_freq(
            wv: &WaveletMatrix,
            i: usize,
            pos_range: Range<usize>,
            query: &Range<usize>,
            node: Range<usize>,
        ) -> usize {
            if is_disjoint_with(&node, query) {
                0
            } else if is_subrange_of(&node, query) {
                pos_range.len()
            } else {
                let mid = midpoint(&node);
                range_freq(
                    wv,
                    i + 1,
                    next_position_range(&wv.table[i], &pos_range, false),
                    query,
                    node.start..mid,
                ) + range_freq(
                    wv,
                    i + 1,
                    next_position_range(&wv.table[i], &pos_range, true),
                    query,
                    mid..node.end,
                )
            }
        }
        let (pl, pr) = open(pos_range, self.len());
        let (vl, vr) = open(value_range, self.lim());
        range_freq(self, 0, pl..pr, &(vl..vr), 0..self.lim())
    }
    pub fn next_value(
        &self,
        pos_range: impl RangeBounds<usize>,
        value_range: impl RangeBounds<usize>,
    ) -> Option<usize> {
        fn next_value(
            wv: &WaveletMatrix,
            i: usize,
            pos: Range<usize>,
            query: &Range<usize>,
            node: Range<usize>,
        ) -> Option<usize> {
            #[allow(clippy::len_zero)]
            if is_disjoint_with(&node, query) || pos.len() == 0 {
                None
            } else if node.len() == 1 {
                Some(node.start)
            } else {
                let mid = midpoint(&node);
                next_value(
                    wv,
                    i + 1,
                    next_position_range(&wv.table[i], &pos, false),
                    query,
                    node.start..mid,
                )
                .or_else(|| {
                    next_value(
                        wv,
                        i + 1,
                        next_position_range(&wv.table[i], &pos, true),
                        query,
                        mid..node.end,
                    )
                })
            }
        }
        let (pl, pr) = open(pos_range, self.len());
        let (vl, vr) = open(value_range, self.lim());
        next_value(self, 0, pl..pr, &(vl..vr), 0..self.lim())
    }
    pub fn prev_value(
        &self,
        pos_range: impl RangeBounds<usize>,
        value_range: impl RangeBounds<usize>,
    ) -> Option<usize> {
        fn prev_value(
            wv: &WaveletMatrix,
            i: usize,
            pos: Range<usize>,
            query: &Range<usize>,
            node: Range<usize>,
        ) -> Option<usize> {
            #[allow(clippy::len_zero)]
            if is_disjoint_with(&node, query) || pos.len() == 0 {
                None
            } else if node.len() == 1 {
                Some(node.end - 1)
            } else {
                let mid = midpoint(&node);
                prev_value(
                    wv,
                    i + 1,
                    next_position_range(&wv.table[i], &pos, true),
                    query,
                    mid..node.end,
                )
                .or_else(|| {
                    prev_value(
                        wv,
                        i + 1,
                        next_position_range(&wv.table[i], &pos, false),
                        query,
                        node.start..mid,
                    )
                })
            }
        }
        let (pl, pr) = open(pos_range, self.len());
        let (vl, vr) = open(value_range, self.lim());
        prev_value(self, 0, pl..pr, &(vl..vr), 0..self.lim())
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

fn open(range: impl RangeBounds<usize>, len: usize) -> (usize, usize) {
    (
        match range.start_bound() {
            Bound::Included(&l) => l,
            Bound::Excluded(&l) => l + 1,
            Bound::Unbounded => 0,
        },
        match range.end_bound() {
            Bound::Included(&r) => r + 1,
            Bound::Excluded(&r) => r,
            Bound::Unbounded => len,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use std::iter::repeat_with;

    #[test]
    fn test_stable_partition_by_key() {
        let mut rng = StdRng::seed_from_u64(42);
        let n = 12;
        let mut a = (0..n)
            .map(|i| i * 2 + rng.gen_bool(0.5) as usize)
            .collect::<Vec<_>>();
        let mut b = a.clone();
        dbg!(&a, &b);
        a.sort_by_key(|&x| x & 1);
        stable_partition_by_key(&mut b, |x| x & 1 == 1);
        dbg!(&a, &b);
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
                let vec = repeat_with(|| rng.gen_bool(p)).take(n).collect::<Vec<_>>();
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
        let h = 3;
        let w = 12;
        #[rustfmt::skip]
        let expected = vec![
            "111100110010",
            "100100000010",
            "110101111010",
        ];
        let expected = expected
            .iter()
            .map(|row| row.chars().map(|c| c == '1').collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let wm = vec![5, 4, 5, 5, 2, 1, 5, 6, 1, 3, 5, 0]
            .into_iter()
            .collect::<WaveletMatrix>();

        assert_eq!(wm.table.len(), h);
        for (i, row) in wm.table.iter().enumerate() {
            assert_eq!(row.len(), w);
            for j in 0..w {
                assert_eq!(row.access(j), expected[i][j]);
            }
        }
    }

    #[test]
    fn test_wavelet_matrix() {
        let slice = vec![5, 4, 5, 5, 2, 1, 5, 6, 1, 3, 5, 0];
        let wm = slice.iter().copied().collect::<WaveletMatrix>();
        let n = slice.len();
        let m = 8;

        // access
        for (i, &expected) in slice.iter().enumerate() {
            assert_eq!(wm.access(i), expected);
        }

        for l in 0..=n {
            for r in l..=n {
                for lower in 0..=m {
                    for upper in 0..=m {
                        // next_value
                        let expected = slice[l..r]
                            .iter()
                            .filter(|&&x| (lower..upper).contains(&x))
                            .count();
                        assert_eq!(wm.range_freq(l..r, lower..upper), expected);

                        // next_value
                        let expected = slice[l..r]
                            .iter()
                            .copied()
                            .filter(|&x| (lower..upper).contains(&x))
                            .min();
                        assert_eq!(wm.next_value(l..r, lower..upper), expected);

                        // prev_value
                        let expected = slice[l..r]
                            .iter()
                            .copied()
                            .filter(|&x| (lower..upper).contains(&x))
                            .max();
                        assert_eq!(wm.prev_value(l..r, lower..upper), expected);
                    }
                }
            }
        }
    }
}
