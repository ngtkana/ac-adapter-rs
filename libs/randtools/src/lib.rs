//! 競技プログラミングのランダムテストケース生成用ユーティリティ。
//!
//! `rand` の `Distribution` トレイトを実装した型を提供する。`rng.sample(Xxx(...))` の形で
//! 呼び出し、範囲・木・グラフなどをランダムに生成する。一様分布だと大きさが偏る場面向けに
//! 対数一様分布（[`LogUniform`]）を、木は Prüfer 列との全単射を利用して一様ランダムな
//! ラベル付き木（[`Tree`]）を生成する。
//!
//! # 仕様
//!
//! - [`LogUniform`] は $[l, r)$ 上で $\ln x$ が一様となる整数 $x$ を生成する
//! - [`DistinctTwo`] は $[l, r)$ 上の相異なる 2 点 $(i, j)$ を生成する
//! - [`SubRange`] は $[l, r]$ の（空を許す）部分区間を生成する
//! - [`NonEmptySubRange`] は $[l, r]$ の空でない部分区間を生成する
//! - [`Tree`] は $n$ 頂点の一様ランダムなラベル付き木を隣接リストで生成する
//! - [`SimpleGraph`], [`SimpleDigraph`] は $n$ 頂点 $m$ 辺の単純（有向）グラフを生成する
//! - [`SimpleGraphEdges`], [`SimpleDigraphEdges`] は上記グラフの辺集合のみを生成する
//!
//! # 例
//!
//! ```
//! use rand::prelude::*;
//! use randtools::Tree;
//!
//! let mut rng = StdRng::seed_from_u64(42);
//! let g = rng.sample(Tree(5));
//! assert_eq!(g.len(), 5);
//! assert_eq!(g.iter().map(Vec::len).sum::<usize>(), 2 * (5 - 1)); // 辺数 n - 1 の 2 倍
//! ```
//!
//! # 計算量
//!
//! - $O(1)$: [`LogUniform`], [`DistinctTwo`], [`SubRange`], [`NonEmptySubRange`]
//! - $O(n \log n)$: [`Tree`]
//! - 期待 $O(m)$: [`SimpleGraph`], [`SimpleDigraph`], [`SimpleGraphEdges`], [`SimpleDigraphEdges`]（辺の衝突が稀な場合）

mod algo;

use rand::prelude::*;
use std::collections::HashSet;
use std::iter;
use std::mem;
use std::ops::Range;

/// 対数一様分布。範囲 $[l, r)$ 上で $\ln x$ が一様な整数 $x$ を生成する。
///
/// 通常の一様分布と異なり、桁数（オーダー）が揃うようにサンプルする。小さい入力から
/// 大きい入力までを均等に試したいランダムテストで使う。
///
/// # 仕様
///
/// `LogUniform(l..r)` は $0 < l < r$ を要求する。$u$ を $[\ln l, \ln r)$ 上の一様乱数として
/// $x = \lfloor e^u \rfloor$ を求め、丸め誤差を補正するため $[l, r-1]$ にクランプして返す。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::LogUniform;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let x: usize = rng.sample(LogUniform(1..1_000_000));
/// assert!((1..1_000_000).contains(&x));
/// ```
#[derive(Debug)]
pub struct LogUniform(pub Range<usize>);
impl Distribution<usize> for LogUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        let Range { start, end } = self.0;
        // start must be positive and the range non-empty: ln(0) is -inf, which
        // makes `gen_range` panic with an unhelpful "low non-finite" message.
        assert!(0 < start && start < end);
        let ln = rng.gen_range((start as f64).ln()..(end as f64).ln());
        (ln.exp().floor() as usize).max(start).min(end - 1)
    }
}

/// 範囲 $[l, r)$ 上の相異なる 2 点 $(i, j)$ を一様ランダムに生成する。
///
/// $i$ を $[l, r-1)$ から、$j$ を $[l, r)$ から独立に選び、$i \geq j$ なら $i$ を 1 増やして
/// $i \neq j$ を保証する。$i, j$ の大小関係は決まらない。
///
/// # 仕様
///
/// `DistinctTwo(l..r)` は $r - l \geq 2$ を要求する。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::DistinctTwo;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let (i, j): (usize, usize) = rng.sample(DistinctTwo(0..10));
/// assert!(i != j && i < 10 && j < 10);
/// ```
#[derive(Debug)]
pub struct DistinctTwo(pub Range<usize>);
impl Distribution<(usize, usize)> for DistinctTwo {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (usize, usize) {
        let Range { start, end } = self.0;
        assert!(start + 2 <= end);
        let mut i = rng.gen_range(start..end - 1);
        let j = rng.gen_range(start..end);
        if i >= j {
            i += 1;
        }
        (i, j)
    }
}

/// 範囲 $[l, r]$ に含まれる部分区間 $[s, e)$ をランダムに生成する（空区間も許す）。
///
/// # 仕様
///
/// `SubRange(l..r)` は $l \leq r$ を要求し、$l \leq s \leq e \leq r$ を満たす $s..e$ を返す。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::SubRange;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let range = rng.sample(SubRange(3..10));
/// assert!(3 <= range.start && range.start <= range.end && range.end <= 10);
/// ```
#[derive(Debug)]
pub struct SubRange(pub Range<usize>);
impl Distribution<Range<usize>> for SubRange {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Range<usize> {
        let Range { start, end } = self.0;
        assert!(start <= end);
        let mut l = rng.gen_range(start..end + 2);
        let mut r = rng.gen_range(start..=end);
        if l > r {
            mem::swap(&mut l, &mut r);
            r -= 1;
        }
        l..r
    }
}

/// 範囲 $[l, r]$ に含まれる空でない部分区間 $[s, e)$ をランダムに生成する。
///
/// # 仕様
///
/// `NonEmptySubRange(l..r)` は $l < r$ を要求し、$l \leq s < e \leq r$ を満たす $s..e$ を返す。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::NonEmptySubRange;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let range = rng.sample(NonEmptySubRange(3..10));
/// assert!(3 <= range.start && range.start < range.end && range.end <= 10);
/// ```
#[derive(Debug)]
pub struct NonEmptySubRange(pub Range<usize>);
impl Distribution<Range<usize>> for NonEmptySubRange {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Range<usize> {
        let Range { start, end } = self.0;
        assert!(start < end);
        let mut l = rng.gen_range(start..end);
        let mut r = rng.gen_range(start..=end);
        if l >= r {
            mem::swap(&mut l, &mut r);
            r += 1;
        }
        l..r
    }
}

/// $n$ 頂点の一様ランダムなラベル付き木を生成する（隣接リスト形式）。
///
/// Prüfer 列と $n$ 頂点のラベル付き木は全単射の関係にある（Cayley の公式）。そのため
/// 長さ $n - 2$ の数列を $[0, n)$ から独立一様に選んで木に復元すれば、木自体も
/// $n$ 頂点のラベル付き木全体の上で一様ランダムになる。
///
/// # 仕様
///
/// `Tree(n)` は $n \geq 1$ を要求し、頂点数 $n$、辺数 $n - 1$ の木を隣接リストで返す。
/// $n = 1$ のときは辺のない 1 頂点の木を返す。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::Tree;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let g = rng.sample(Tree(5));
/// assert_eq!(g.len(), 5);
/// assert_eq!(g.iter().map(Vec::len).sum::<usize>(), 2 * (5 - 1)); // 辺数 n - 1 の 2 倍
/// ```
///
/// # 計算量
///
/// $O(n \log n)$
#[derive(Debug)]
#[doc(alias = "prufer")]
pub struct Tree(pub usize);
impl Distribution<Vec<Vec<usize>>> for Tree {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let n = self.0;
        assert!(1 <= n);
        if n == 1 {
            vec![Vec::new()]
        } else {
            let prufer = iter::repeat_with(|| rng.gen_range(0..n))
                .take(n - 2)
                .collect::<Vec<_>>();
            algo::prufer2tree(&prufer)
        }
    }
}

/// $n$ 頂点 $m$ 辺の単純無向グラフを生成する（隣接リスト形式）。
///
/// [`SimpleGraphEdges`] で辺集合を生成し、両端点の隣接リストへそれぞれ追加する。
///
/// # 仕様
///
/// `SimpleGraph(n, m)` は $m \leq \binom{n}{2}$ を要求する。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::SimpleGraph;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let g = rng.sample(SimpleGraph(5, 4));
/// assert_eq!(g.iter().map(Vec::len).sum::<usize>(), 2 * 4); // 辺数 4 の 2 倍
/// ```
#[derive(Debug)]
pub struct SimpleGraph(pub usize, pub usize);
impl Distribution<Vec<Vec<usize>>> for SimpleGraph {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let &Self(n, m) = self;
        let mut g = vec![Vec::new(); n];
        for (u, v) in rng.sample(SimpleGraphEdges(n, m)) {
            g[u].push(v);
            g[v].push(u);
        }
        g
    }
}

/// $n$ 頂点 $m$ 辺の単純有向グラフを生成する（隣接リスト形式）。
///
/// 内部では [`SimpleGraphEdges`] を使って辺集合を生成し、各辺を一方向にのみ張る。
/// [`SimpleGraphEdges`] は逆順の組も含めて重複を除くため、$(u, v)$ を辺として選んだ場合
/// 逆辺 $(v, u)$ が同時に生成されることはない。
///
/// # 仕様
///
/// `SimpleDigraph(n, m)` は $m \leq \binom{n}{2}$ を要求する。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::SimpleDigraph;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let g = rng.sample(SimpleDigraph(5, 4));
/// assert_eq!(g.iter().map(Vec::len).sum::<usize>(), 4); // 有向辺数 4
/// ```
#[derive(Debug)]
pub struct SimpleDigraph(pub usize, pub usize);
impl Distribution<Vec<Vec<usize>>> for SimpleDigraph {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let &Self(n, m) = self;
        let mut g = vec![Vec::new(); n];
        for (u, v) in rng.sample(SimpleGraphEdges(n, m)) {
            g[u].push(v);
        }
        g
    }
}

/// $n$ 頂点上の重複のない無向辺 $m$ 本 $(u, v)$（$u \neq v$）を生成する。
///
/// [`DistinctTwo`] で相異なる 2 頂点を繰り返しサンプルし、既出の組（逆順を含む）を
/// 棄却しながら $m$ 本集める棄却サンプリングで実装する。
///
/// # 仕様
///
/// `SimpleGraphEdges(n, m)` は $m \leq \binom{n}{2}$ を要求する。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::SimpleGraphEdges;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let edges = rng.sample(SimpleGraphEdges(5, 4));
/// assert_eq!(edges.len(), 4);
/// ```
#[derive(Debug)]
pub struct SimpleGraphEdges(pub usize, pub usize);
impl Distribution<Vec<(usize, usize)>> for SimpleGraphEdges {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<(usize, usize)> {
        let &Self(n, m) = self;
        assert!(m <= n.saturating_sub(1) * n / 2);
        let mut set = HashSet::new();
        DistinctTwo(0..n)
            .sample_iter(rng)
            .filter(|&(u, v)| {
                let found = set.contains(&(u, v));
                set.insert((u, v));
                set.insert((v, u));
                !found
            })
            .take(m)
            .collect()
    }
}

/// $n$ 頂点上の重複のない有向辺 $m$ 本 $(u, v)$（$u \neq v$）を生成する。
///
/// [`DistinctTwo`] で相異なる 2 頂点を繰り返しサンプルし、既出の順序対のみを棄却する
/// （逆向きの辺 $(v, u)$ は別の辺として許容する）ため、[`SimpleGraphEdges`] と異なり
/// 対をなす 2 方向の辺が両方出現しうる。
///
/// # 仕様
///
/// `SimpleDigraphEdges(n, m)` は $m \leq n(n-1)$ を要求する。
///
/// # 例
///
/// ```
/// use rand::prelude::*;
/// use randtools::SimpleDigraphEdges;
///
/// let mut rng = StdRng::seed_from_u64(42);
/// let edges = rng.sample(SimpleDigraphEdges(5, 4));
/// assert_eq!(edges.len(), 4);
/// ```
#[derive(Debug)]
pub struct SimpleDigraphEdges(pub usize, pub usize);
impl Distribution<Vec<(usize, usize)>> for SimpleDigraphEdges {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<(usize, usize)> {
        let &Self(n, m) = self;
        // Directed edges are ordered pairs, so the capacity is n * (n - 1),
        // not n * (n - 1) / 2 (which undercounts by half and rejects valid m).
        assert!(m <= n.saturating_sub(1) * n);
        let mut set = HashSet::new();
        DistinctTwo(0..n)
            .sample_iter(rng)
            .filter(|&(u, v)| {
                let found = set.contains(&(u, v));
                set.insert((u, v));
                !found
            })
            .take(m)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::LogUniform;
    use super::NonEmptySubRange;
    use super::SubRange;
    use super::Tree;
    use rand::prelude::*;
    use std::ops::Range;
    mod algo;

    #[test]
    fn test_log_uniform() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let range = rng.sample(NonEmptySubRange(1..20));
            let x = rng.sample(LogUniform(range.clone()));
            assert!(range.contains(&x));
        }
    }

    #[test]
    fn test_open() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let d = rng.gen_range(2..8);
            let l = rng.gen_range(0..40);
            let r = l + d;
            let Range { start, end } = rng.sample(SubRange(l..r));

            assert!(l <= start && start <= end && end <= r);
        }
    }

    #[test]
    fn test_tree() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..1_000);
            let g = rng.sample(Tree(n));
            println!("g = {:?}", &g);
            assert!(algo::is_tree(&g));
        }
    }
}
