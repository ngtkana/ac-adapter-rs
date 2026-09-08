//! 冪等半群上の区間畳み込みを $O(1)$ で答える静的データ構造。
//!
//! 長さ $1$ の区間から始め、長さを $2$ 倍ずつ伸ばしながら区間の積をすべて前計算する。
//! 問い合わせ $[l, r)$ には、長さ $2^p \le r - l$ の区間を左右の端からそれぞれ $1$ つ取り、
//! 重なりを許したまま $2$ つの積を掛け合わせて答える。演算が結合的かつ冪等（$x \cdot x = x$）
//! であれば重複部分の混入は結果に影響しないため、単位元がなくても正しく計算できる。
//! 更新はできないが、前計算 $O(n \log n)$ のあとは各問い合わせを $O(1)$ で答えられる。
//!
//! # 仕様
//!
//! [`Op`] トレイトで冪等半群を定義する。
//!
//! - [`Op::mul`][]: 積 $x \cdot y$（結合律・冪等律 $x \cdot x = x$ を満たすこと）
//!
//! 構造体は次の $2$ 種類。
//!
//! - [`SparseTable`]（1 次元）
//! - [`SparseTable2d`]（2 次元。[`Op::mul`] にさらに可換律も要求する）
//!
//! # 例
//!
//! ```
//! use sparse_table::Op;
//! use sparse_table::SparseTable;
//!
//! enum Max {}
//! impl Op for Max {
//!     type Value = i64;
//!     fn mul(lhs: &i64, rhs: &i64) -> i64 {
//!         (*lhs).max(*rhs)
//!     }
//! }
//!
//! let st = SparseTable::<Max>::clone_from_slice(&[3, 1, 4, 1, 5]);
//! assert_eq!(st.fold(1..4), Some(4)); // max(1, 4, 1)
//! assert_eq!(st.fold(2..2), None); // 空区間
//! ```
//!
//! # 計算量
//!
//! - 構築（[`SparseTable::new`]）: $O(n \log n)$
//! - 畳み込み（[`SparseTable::fold`]）: $O(1)$

use std::fmt::Debug;
use std::iter::FromIterator;
use std::ops::Index;
use std::ops::RangeBounds;

/// 区間畳み込みに使う二項演算。結合律・冪等律 $x \cdot x = x$ を満たすこと。
pub trait Op {
    /// 値の型。
    type Value;

    /// 積 $x \cdot y$ を計算する。
    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

/// 1 次元のスパーステーブル。区間 $[l, r)$ の畳み込みを $O(1)$ で答える。
pub struct SparseTable<O: Op> {
    table: Vec<Vec<O::Value>>,
}
impl<O: Op> SparseTable<O> {
    /// 値の列からスパーステーブルを構築する。$O(n \log n)$。
    pub fn new(values: Vec<O::Value>) -> Self {
        values.into()
    }

    /// 値のスライスを複製してスパーステーブルを構築する。$O(n \log n)$。
    pub fn clone_from_slice(values: &[O::Value]) -> Self
    where
        O::Value: Clone,
    {
        values.into()
    }

    /// $x_i$ を返す。
    pub fn get(&self, index: usize) -> &O::Value {
        &self.table[0][index]
    }

    /// $x_l \cdot x_{l+1} \cdot \ldots \cdot x_{r-1}$ を返す。$l = r$ のときは `None`。$O(1)$。
    ///
    /// # 例
    ///
    /// ```
    /// use sparse_table::Op;
    /// use sparse_table::SparseTable;
    ///
    /// enum Max {}
    /// impl Op for Max {
    ///     type Value = i64;
    ///     fn mul(lhs: &i64, rhs: &i64) -> i64 {
    ///         (*lhs).max(*rhs)
    ///     }
    /// }
    ///
    /// let st = SparseTable::<Max>::clone_from_slice(&[3, 1, 4, 1, 5]);
    /// assert_eq!(st.fold(1..4), Some(4));
    /// assert_eq!(st.fold(2..2), None);
    /// ```
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Value> {
        let (start, end) = open(range, self.table[0].len());
        assert!(start <= end);
        (start < end).then_some(())?;
        let p = (end - start).ilog2() as usize;
        let row = &self.table[p];
        Some(O::mul(&row[start], &row[end - (1 << p)]))
    }

    /// $x_0, x_1, \ldots, x_{n-1}$ を順に返すイテレータ。
    pub fn iter(&self) -> impl Iterator<Item = &O::Value> {
        self.table[0].iter()
    }

    /// $x_0, x_1, \ldots, x_{n-1}$ のスライスを返す。
    pub fn as_slice(&self) -> &[O::Value] {
        &self.table[0]
    }

    /// $x_0, x_1, \ldots, x_{n-1}$ を複製して `Vec` にまとめる。
    pub fn collect_vec(&self) -> Vec<O::Value>
    where
        O::Value: Clone,
    {
        self.table[0].clone()
    }

    /// 内部テーブルを返す。`table[k][i]` は $x_i \cdot x_{i+1} \cdot \ldots \cdot x_{i+2^k-1}$。
    pub fn inner(&self) -> &Vec<Vec<O::Value>> {
        &self.table
    }
}

impl<O: Op> Debug for SparseTable<O>
where
    O::Value: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SparseTable")
            .field("table", &self.table)
            .finish()
    }
}

impl<O: Op> From<Vec<O::Value>> for SparseTable<O> {
    fn from(values: Vec<O::Value>) -> Self {
        let n = values.len();
        let mut table = vec![values];
        let mut i = 1;
        while i * 2 <= n {
            let last = table.last().unwrap();
            let current = last
                .iter()
                .zip(&last[i..])
                .map(|(a, b)| O::mul(a, b))
                .collect();
            table.push(current);
            i *= 2;
        }
        Self { table }
    }
}

impl<'a, O: Op> From<&'a [O::Value]> for SparseTable<O>
where
    O::Value: Clone,
{
    fn from(values: &'a [O::Value]) -> Self {
        values.to_vec().into()
    }
}

impl<O: Op> FromIterator<O::Value> for SparseTable<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        iter.into_iter().collect::<Vec<_>>().into()
    }
}

impl<O: Op> Index<usize> for SparseTable<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        &self.table[0][index]
    }
}

/// 2 次元のスパーステーブル。矩形領域の畳み込みを $O(1)$ で答える。
///
/// 矩形を高々 4 個の角ブロックに分解して積を取るため、[`Op::mul`] は可換律も満たす必要がある。
pub struct SparseTable2d<O: Op> {
    table: Vec<Vec<Vec<Vec<O::Value>>>>,
}

impl<O: Op> SparseTable2d<O> {
    /// 値の 2 次元配列からスパーステーブルを構築する。$O(hw \log h \log w)$。
    pub fn new(values: Vec<Vec<O::Value>>) -> Self {
        values.into()
    }

    /// 値の 2 次元スライスを複製してスパーステーブルを構築する。$O(hw \log h \log w)$。
    pub fn clone_from_slice(values: &[Vec<O::Value>]) -> Self
    where
        O::Value: Clone,
    {
        values.into()
    }

    /// $\left \lbrace x_{i, j} \mid i \in \text{{range}}_i, j \in \text{{range}}_j \right \rbrace$ の総積を返す。
    ///
    /// $i_0 = i_1$ または $j_0 = j_1$ のときは `None`。$O(1)$。
    pub fn fold(&self, i: impl RangeBounds<usize>, j: impl RangeBounds<usize>) -> Option<O::Value> {
        let (i0, mut i1) = open(i, self.table[0][0].len());
        let (j0, mut j1) = open(j, self.table[0][0].first().map_or(0, Vec::len));
        assert!(i0 <= i1);
        assert!(j0 <= j1);
        (i0 < i1 && j0 < j1).then_some(())?;
        let p = (i1 - i0).ilog2() as usize;
        let q = (j1 - j0).ilog2() as usize;
        let grid = &self.table[p][q];
        i1 -= 1 << p;
        j1 -= 1 << q;
        Some(O::mul(
            &O::mul(&grid[i0][j0], &grid[i1][j0]),
            &O::mul(&grid[i0][j1], &grid[i1][j1]),
        ))
    }

    /// 各行 $(x_{i, 0}, x_{i, 1}, \ldots, x_{i, w-1})$ を順に返すイテレータ。
    pub fn iter(&self) -> impl Iterator<Item = &[O::Value]> {
        self.table[0][0].iter().map(Vec::as_slice)
    }

    /// 値の 2 次元スライスを返す。
    pub fn as_slice(&self) -> &[Vec<O::Value>] {
        &self.table[0][0]
    }

    /// 値を複製して 2 次元の `Vec` にまとめる。
    pub fn collect_vec(&self) -> Vec<Vec<O::Value>>
    where
        O::Value: Clone,
    {
        self.table[0][0].clone()
    }

    /// 内部テーブルを返す。`table[p][q][i][j]` は $i$ 行 $j$ 列を起点とする
    /// $2^p \times 2^q$ ブロックの積。
    pub fn inner(&self) -> &Vec<Vec<Vec<Vec<O::Value>>>> {
        &self.table
    }
}

impl<O: Op> Debug for SparseTable2d<O>
where
    O::Value: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SparseTable2d")
            .field("table", &self.table)
            .finish()
    }
}

impl<O: Op> From<Vec<Vec<O::Value>>> for SparseTable2d<O> {
    fn from(values: Vec<Vec<O::Value>>) -> Self {
        let h = values.len();
        let w = values.first().map_or(0, Vec::len);
        let mut table = vec![vec![values]];
        let mut j = 1;
        while j * 2 <= w {
            let last = table[0].last().unwrap();
            let current = last
                .iter()
                .map(|row| {
                    row.iter()
                        .zip(&row[j..])
                        .map(|(a, b)| O::mul(a, b))
                        .collect::<Vec<_>>()
                })
                .collect();
            table[0].push(current);
            j *= 2;
        }
        let mut i = 1;
        while i * 2 <= h {
            let last = table.last().unwrap();
            let current = last
                .iter()
                .map(|grid| {
                    grid.iter()
                        .zip(&grid[i..])
                        .map(|(a, b)| {
                            a.iter()
                                .zip(b)
                                .map(|(a, b)| O::mul(a, b))
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>()
                })
                .collect();
            table.push(current);
            i *= 2;
        }
        Self { table }
    }
}

impl<'a, O: Op> From<&'a [Vec<O::Value>]> for SparseTable2d<O>
where
    O::Value: Clone,
{
    fn from(values: &'a [Vec<O::Value>]) -> Self {
        values.to_vec().into()
    }
}

fn open<B: RangeBounds<usize>>(bounds: B, n: usize) -> (usize, usize) {
    use std::ops::Bound;
    let start = match bounds.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    };
    let end = match bounds.end_bound() {
        Bound::Unbounded => n,
        Bound::Included(&x) => x + 1,
        Bound::Excluded(&x) => x,
    };
    (start, end)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::ops::Range;

    enum O {}
    impl Op for O {
        type Value = u64;

        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            (*lhs).max(*rhs)
        }
    }

    #[test]
    fn test_sparse_table() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let vec = (0..n)
                .map(|_| rng.gen_range(0..u64::MAX))
                .collect::<Vec<_>>();
            let st = SparseTable::<O>::clone_from_slice(&vec);
            for _ in 0..q {
                let range = random_range(&mut rng, n);
                let expected = vec[range.clone()].iter().copied().max();
                let actual = st.fold(range.clone());
                assert_eq!(expected, actual);
            }
        }
    }

    #[test]
    fn test_sparse_table_2d() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let h = rng.gen_range(1..=10);
            let w = rng.gen_range(1..=10);
            let q = rng.gen_range(1..=100);
            let vec = (0..h)
                .map(|_| {
                    (0..w)
                        .map(|_| rng.gen_range(0..u64::MAX))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let st = SparseTable2d::<O>::clone_from_slice(&vec);
            for _ in 0..q {
                let i = random_range(&mut rng, h);
                let j = random_range(&mut rng, w);
                let expected = vec[i.clone()]
                    .iter()
                    .flat_map(|row| &row[j.clone()])
                    .max()
                    .copied();
                let actual = st.fold(i.clone(), j.clone());
                assert_eq!(expected, actual);
            }
        }
    }

    fn random_range(rng: &mut StdRng, n: usize) -> Range<usize> {
        let start = rng.gen_range(0..=n + 1);
        let end = rng.gen_range(0..=n);
        if start <= end {
            start..end
        } else {
            end..start - 1
        }
    }
}
