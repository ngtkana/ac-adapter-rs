//! メモリの局所性に配慮した隣接リスト表現。
//!
//! CSR（Compressed Sparse Row）形式で隣接リストを保持する。頂点 $i$ の隣接リストは
//! 連続領域 `edges[start[i]..start[i+1]]` に格納されるため、`Vec<Vec<_>>` のように
//! 頂点ごとに別々のヒープ領域を確保することがない。構築は counting sort による 1 パスで行い、
//! 最終的に保持する `start`・`edges` の 2 つの `Vec` 以外に動的メモリ確保は発生しない。
//!
//! # 仕様
//!
//! - 型: `Graph<E>`（`E` は辺重み。重みなしの場合は `E = usize` で隣接先の頂点番号を表す）
//! - 構築:
//!     - [`Graph::from_directed_edges`] — 有向グラフ
//!     - [`Graph::from_undirected_edges`] — 無向グラフ（逆辺も自動挿入）
//!     - [`Graph::from_parents`] — 親配列 $p_1, \ldots, p_{n-1}$ から外向き有向木を構築
//!     - [`Graph::from_directed_edges_with_weight`], [`Graph::from_undirected_edges_with_weight`] — 辺重み付き版
//! - アクセス: `&g[i]: &[E]` でインデックスアクセス、`g.iter()` で頂点 $0, 1, \ldots, n-1$ の隣接リストを順に走査
//! - 木の整列: [`Graph::sort_undirected_tree`], [`Graph::sort_undirected_tree_with_weight`] で無向木を、親方向の辺を取り除いた外向き有向木に変換
//!
//! # 例
//!
//! ```
//! use flat_graph::Graph;
//!
//! let g = Graph::from_undirected_edges(5, &[(0, 1), (0, 2), (2, 4)]);
//! assert_eq!(g[0], [1, 2]);
//! assert_eq!(g[1], [0]);
//! assert_eq!(g[2], [0, 4]);
//! assert_eq!(g[3], []);
//! assert_eq!(g[4], [2]);
//! ```
//!
//! # 計算量
//!
//! - 構築: $O(n + m)$（$n$: 頂点数、$m$: 辺数）
//! - インデックスアクセス（`g[i]`）: $O(1)$
//! - 木の整列（[`Graph::sort_undirected_tree`] 等）: $O(n)$

use std::ops::Index;

/// CSR 形式で隣接リストを保持するグラフ。
///
/// 頂点数を $n$ とすると、`start`（長さ $n + 1$）に各頂点の辺区間の開始位置を、
/// `edges` に辺の実体を保持する。頂点 $i$ の隣接リストは `edges[start[i]..start[i+1]]`。
///
/// # 例
///
/// ```
/// use flat_graph::Graph;
///
/// let g = Graph::from_undirected_edges(5, &[(0, 1), (0, 2), (2, 4)]);
/// assert_eq!(g[0], [1, 2]);
/// assert_eq!(g[1], [0]);
/// assert_eq!(g[2], [0, 4]);
/// assert_eq!(g[3], []);
/// assert_eq!(g[4], [2]);
/// ```
#[derive(Clone, Debug)]
pub struct Graph<E> {
    start: Vec<usize>,
    edges: Vec<E>,
}
impl Graph<usize> {
    /// 親配列 $p_1, p_2, \ldots, p_{n-1}$（頂点 $i$ の親が $p_i$）から外向き有向木を構築する。
    ///
    /// 各隣接リストはソート済みになる。
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let g = Graph::from_parents(&[0, 0, 1]);
    ///
    /// assert_eq!(g[0], [1, 2]);
    /// assert_eq!(g[1], [3]);
    /// assert_eq!(g[2], []);
    /// assert_eq!(g[3], []);
    /// ```
    pub fn from_parents(parents: &[usize]) -> Self {
        let n = parents.len() + 1;
        Self::from_edges_generic(
            n,
            n - 1,
            parents.iter().copied(),
            parents.iter().copied().zip(1..),
        )
    }
    /// 有向グラフを構築する。
    ///
    /// 各隣接リストは入力の辺の順番通りになる。
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let g = Graph::from_directed_edges(
    ///     5,
    ///     &[(0, 1), (0, 2), (2, 4)],
    /// );
    ///
    /// assert_eq!(g[0], [1, 2]);
    /// assert_eq!(g[1], []);
    /// assert_eq!(g[2], [4]);
    /// assert_eq!(g[3], []);
    /// assert_eq!(g[4], []);
    /// ```
    pub fn from_directed_edges(n: usize, edges: &[(usize, usize)]) -> Self {
        Self::from_edges_generic(
            n,
            edges.len(),
            edges.iter().map(|&(i, _)| i),
            edges.iter().map(|&(i, j)| (i, j)),
        )
    }

    /// 無向グラフを、片方向の辺のみを入力として構築する。
    ///
    /// 各隣接リストは、入力そのままの辺を順番通りに並べた後、逆辺を順番通りに続けたものになる。
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let g = Graph::from_undirected_edges(
    ///     5,
    ///     &[(0, 1), (0, 2), (2, 4)],
    /// );
    ///
    /// assert_eq!(g[0], [1, 2]);
    /// assert_eq!(g[1], [0]);
    /// assert_eq!(g[2], [0, 4]);
    /// assert_eq!(g[3], []);
    /// assert_eq!(g[4], [2]);
    /// ```
    pub fn from_undirected_edges(n: usize, edges: &[(usize, usize)]) -> Self {
        Self::from_edges_generic(
            n,
            edges.len() * 2,
            edges.iter().flat_map(|&(i, j)| [i, j]),
            edges.iter().flat_map(|&(i, j)| [(i, j), (j, i)]),
        )
    }

    /// 無向木を根 `root` からの外向き有向木に変換し、`(sorted, parent)` を返す。
    ///
    /// 根からの深さ優先探索の訪問順を `sorted` に、各頂点の親を `parent` に格納する。
    /// `self` の各隣接リストからは、親方向への辺が取り除かれる。
    ///
    /// # 仕様
    ///
    /// - `sorted`: 深さ優先探索の訪問順の頂点列（`sorted[0] == root`）
    /// - `parent[i]`: 頂点 $i$ の親（`parent[root] == root`）
    ///
    /// # 計算量
    ///
    /// $O(n)$
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let mut g = Graph::from_undirected_edges(
    ///     3,
    ///     &[(0, 1), (1, 2)],
    /// );
    ///
    /// assert_eq!(&g[0], [1]);
    /// assert_eq!(&g[1], [0, 2]);
    /// assert_eq!(&g[2], [1]);
    ///
    /// let (sorted, parent) = g.sort_undirected_tree(0);
    ///
    /// assert_eq!(&g[0], [1]);
    /// assert_eq!(&g[1], [2]);
    /// assert_eq!(&g[2], []);
    ///
    /// assert_eq!(sorted, [0, 1, 2]);
    /// assert_eq!(parent, [0, 0, 1]);
    /// ```
    pub fn sort_undirected_tree(&mut self, root: usize) -> (Vec<usize>, Vec<usize>) {
        self.sort_undirected_tree_generic(root, |&y| y)
    }
}

impl<T: Copy + Default> Graph<(usize, T)> {
    /// 辺重み付き有向グラフを構築する。
    ///
    /// 各要素は `(隣接先の頂点番号, 辺重み)` のペア。各隣接リストは入力の辺の順番通りになる。
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let g = Graph::from_directed_edges_with_weight(
    ///     5,
    ///     &[(0, 1, 'a'), (0, 2, 'b'), (2, 4, 'c')],
    /// );
    ///
    /// assert_eq!(g[0], [(1, 'a'), (2, 'b')]);
    /// assert_eq!(g[1], []);
    /// assert_eq!(g[2], [(4, 'c')]);
    /// assert_eq!(g[3], []);
    /// assert_eq!(g[4], []);
    /// ```
    pub fn from_directed_edges_with_weight(n: usize, edges: &[(usize, usize, T)]) -> Self {
        Self::from_edges_generic(
            n,
            edges.len(),
            edges.iter().map(|&(i, _, _)| i),
            edges.iter().map(|&(i, j, w)| (i, (j, w))),
        )
    }

    /// 辺重み付き無向グラフを、片方向の辺のみを入力として構築する。
    ///
    /// 各要素は `(隣接先の頂点番号, 辺重み)` のペア。逆辺には元の辺と同じ重みが割り当てられる。
    /// 各隣接リストは、入力そのままの辺を順番通りに並べた後、逆辺を順番通りに続けたものになる。
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let g = Graph::from_undirected_edges_with_weight(
    ///     5,
    ///     &[(0, 1, 'a'), (0, 2, 'b'), (2, 4, 'c')],
    /// );
    ///
    /// assert_eq!(g[0], [(1, 'a'), (2, 'b')]);
    /// assert_eq!(g[1], [(0, 'a')]);
    /// assert_eq!(g[2], [(0, 'b'), (4, 'c')]);
    /// assert_eq!(g[3], []);
    /// assert_eq!(g[4], [(2, 'c')]);
    /// ```
    pub fn from_undirected_edges_with_weight(n: usize, edges: &[(usize, usize, T)]) -> Self {
        Self::from_edges_generic(
            n,
            edges.len() * 2,
            edges.iter().flat_map(|&(i, j, _)| [i, j]),
            edges
                .iter()
                .flat_map(|&(i, j, w)| [(i, (j, w)), (j, (i, w))]),
        )
    }

    /// 辺重み付き無向木を根 `root` からの外向き有向木に変換し、`(sorted, parent)` を返す。
    ///
    /// [`Graph::sort_undirected_tree`] の辺重み付き版。仕様・計算量は同様。
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let mut g = Graph::from_undirected_edges_with_weight(
    ///     3,
    ///     &[(0, 1, 'a'), (1, 2, 'b')],
    /// );
    ///
    /// assert_eq!(&g[0], [(1, 'a')]);
    /// assert_eq!(&g[1], [(0, 'a'), (2, 'b')]);
    /// assert_eq!(&g[2], [(1, 'b')]);
    ///
    /// let (sorted, parent) = g.sort_undirected_tree_with_weight(0);
    ///
    /// assert_eq!(&g[0], [(1, 'a')]);
    /// assert_eq!(&g[1], [(2, 'b')]);
    /// assert_eq!(&g[2], []);
    ///
    /// assert_eq!(sorted, [0, 1, 2]);
    /// assert_eq!(parent, [0, 0, 1]);
    /// ```
    pub fn sort_undirected_tree_with_weight(&mut self, root: usize) -> (Vec<usize>, Vec<usize>) {
        self.sort_undirected_tree_generic(root, |e| e.0)
    }
}

impl<E: Default + Clone> Graph<E> {
    fn from_edges_generic(
        n: usize,
        m: usize,
        src: impl Iterator<Item = usize>,
        edges: impl Iterator<Item = (usize, E)>,
    ) -> Self {
        let mut start = vec![0; n + 1];
        for i in src {
            start[i + 1] += 1;
        }
        for i in 0..n {
            start[i + 1] += start[i];
        }
        let edge_count = m;
        let mut tar = vec![E::default(); edge_count];
        for (i, e) in edges {
            tar[start[i]] = e;
            start[i] += 1;
        }
        start.rotate_right(1);
        start[0] = 0;
        Self { start, edges: tar }
    }

    /// [`Graph::sort_undirected_tree`] / [`Graph::sort_undirected_tree_with_weight`] の一般化版。
    ///
    /// 辺 `E` から隣接先の頂点番号を取り出す関数 `tar` を受け取る。仕様は
    /// [`Graph::sort_undirected_tree`] を参照。
    ///
    /// # 計算量
    ///
    /// $O(n)$
    pub fn sort_undirected_tree_generic(
        &mut self,
        root: usize,
        tar: impl Fn(&E) -> usize,
    ) -> (Vec<usize>, Vec<usize>) {
        let n = self.start.len() - 1;
        assert_eq!(self.edges.len(), 2 * (n - 1));

        let mut sorted = vec![];
        let mut stack = vec![root];
        let mut parent = vec![usize::MAX; n];
        parent[root] = root;
        while let Some(x) = stack.pop() {
            sorted.push(x);
            for e in &self[x] {
                let y = tar(e);
                if parent[y] != usize::MAX {
                    continue;
                }
                parent[y] = x;
                stack.push(y);
            }
        }

        let mut i = 0;
        let mut j = 0;
        for x in 0..n {
            while j < self.start[x + 1] {
                if tar(&self.edges[j]) != parent[x] {
                    self.edges.swap(i, j);
                    i += 1;
                }
                j += 1;
            }
            self.start[x + 1] = i;
        }
        assert_eq!(i, n - 1);

        self.edges.truncate(n - 1);
        (sorted, parent)
    }
}

impl<E> Graph<E> {
    /// 頂点 $0, 1, \ldots, n-1$ の隣接リストを順に返すイテレータを構築する。
    ///
    /// # 例
    ///
    /// ```
    /// use flat_graph::Graph;
    ///
    /// let g = Graph::from_undirected_edges(
    ///     5,
    ///     &[(0, 1), (0, 2), (2, 4)],
    /// );
    ///
    /// let mut iter = g.iter();
    /// assert_eq!(iter.next().unwrap(), [1, 2]);
    /// assert_eq!(iter.next().unwrap(), [0]);
    /// assert_eq!(iter.next().unwrap(), [0, 4]);
    /// assert_eq!(iter.next().unwrap(), []);
    /// assert_eq!(iter.next().unwrap(), [2]);
    /// assert!(iter.next().is_none());
    /// ```
    pub fn iter(&self) -> Iter<'_, E> {
        Iter {
            index: 0,
            graph: self,
        }
    }
}

impl<E> Index<usize> for Graph<E> {
    type Output = [E];

    fn index(&self, index: usize) -> &Self::Output {
        &self.edges[self.start[index]..self.start[index + 1]]
    }
}

impl<'a, E> IntoIterator for &'a Graph<E> {
    type Item = &'a [E];

    type IntoIter = Iter<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// [`Graph::iter`] の戻り値の型。
pub struct Iter<'a, E> {
    index: usize,
    graph: &'a Graph<E>,
}
impl<'a, E> Iterator for Iter<'a, E> {
    type Item = &'a [E];

    fn next(&mut self) -> Option<Self::Item> {
        if self.index + 1 == self.graph.start.len() {
            None
        } else {
            self.index += 1;
            Some(&self.graph[self.index - 1])
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    #[test]
    fn test_from_directed_edges_nonempty() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..=6);
            let m = rng.gen_range(0..=n * n);
            let edges = (0..m)
                .map(|_| (rng.gen_range(0..n), rng.gen_range(0..n)))
                .collect::<Vec<_>>();
            let g = Graph::from_directed_edges(n, &edges);

            assert_eq!(g.start.len(), n + 1);
            assert_eq!(g.edges.len(), m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j) in &edges {
                expected_tar[i].push(j);
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.edges[g.start[i]..g.start[i + 1]], expected_tar[i]);
            }
        }
    }

    #[test]
    fn test_from_undirected_edges_nonempty() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..=6);
            let m = rng.gen_range(0..=n * n);
            let edges = (0..m)
                .map(|_| (rng.gen_range(0..n), rng.gen_range(0..n)))
                .collect::<Vec<_>>();
            let g = Graph::from_undirected_edges(n, &edges);

            assert_eq!(g.start.len(), n + 1);
            assert_eq!(g.edges.len(), 2 * m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j) in &edges {
                expected_tar[i].push(j);
                expected_tar[j].push(i);
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.edges[g.start[i]..g.start[i + 1]], expected_tar[i]);
            }
        }
    }

    #[test]
    fn test_from_directed_edges_with_weight_nonempty() {
        let mut rng = StdRng::seed_from_u64(42);
        let lim = 10;
        for _ in 0..200 {
            let n = rng.gen_range(1..=6);
            let m = rng.gen_range(0..=n * n);
            let edges = (0..m)
                .map(|_| {
                    (
                        rng.gen_range(0..n),
                        rng.gen_range(0..n),
                        rng.gen_range(0..lim),
                    )
                })
                .collect::<Vec<_>>();
            let g = Graph::from_directed_edges_with_weight(n, &edges);

            assert_eq!(g.start.len(), n + 1);
            assert_eq!(g.edges.len(), m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j, w) in &edges {
                expected_tar[i].push((j, w));
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.edges[g.start[i]..g.start[i + 1]], expected_tar[i]);
            }
        }
    }

    #[test]
    fn test_from_undirected_edges_with_weight_nonempty() {
        let mut rng = StdRng::seed_from_u64(42);
        let lim = 10;
        for _ in 0..200 {
            let n = rng.gen_range(1..=6);
            let m = rng.gen_range(0..=n * n);
            let edges = (0..m)
                .map(|_| {
                    (
                        rng.gen_range(0..n),
                        rng.gen_range(0..n),
                        rng.gen_range(0..lim),
                    )
                })
                .collect::<Vec<_>>();
            let g = Graph::from_undirected_edges_with_weight(n, &edges);

            assert_eq!(g.start.len(), n + 1);
            assert_eq!(g.edges.len(), 2 * m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j, w) in &edges {
                expected_tar[i].push((j, w));
                expected_tar[j].push((i, w));
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.edges[g.start[i]..g.start[i + 1]], expected_tar[i]);
            }
        }
    }
}
