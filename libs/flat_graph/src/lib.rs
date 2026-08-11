//! メモリの局所性に気を遣った隣接リスト表現
//!
//! [`Graph`] に説明があります。
//!

use std::ops::Index;

/// Flat graph です。
///
/// なるべく `Vec<Vec<_>>` に比べて使いづらくないよう、次のインターフェースを備えています。
///
/// * Index access: `&g[i]: &[E]`
/// * Iterator: `g.iter()`, `for _ in &g`
///
///
/// # Example
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
///
/// # 構築アルゴリズム
///
/// Counting sort で構築する。
/// 最終的に [`Graph`] に store される $2$ つの [`Vec`] 以外には、動的メモリ確保を行わない。
///
/// | 名前 | 長さ | 意味 |
/// | - | - | - |
/// | `start` | $n + 1$ | `tar` における offset |
/// | `tar` | 有向辺の本数 | 辺の実体 |
///
/// # 構築インターフェース
///
/// * [`from_undirected_edges`](Graph::from_undirected_edges): 逆辺も挿入する
#[derive(Clone, Debug)]
pub struct Graph<E> {
    start: Vec<usize>,
    tar: Vec<E>,
}
impl Graph<usize> {
    /// 有向グラフを構築する
    ///
    /// 各隣接リストは入力の順番通りになります。
    ///
    /// # Example
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

    /// 無向グラフを、片方の辺だけを入力として構築する
    ///
    /// 各隣接リストは次のような順番になります。
    ///
    /// * まず、入力そのままの辺を順番通りに
    /// * その後で、逆辺を順番通りに
    ///
    ///
    /// # Example
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

    /// 無向グラフ表現された木を外向き有向木表現にして、`(sorted, parent)` を返す
    ///
    /// # Example
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
        let n = self.start.len() - 1;
        assert_eq!(self.tar.len(), 2 * (n - 1));

        let mut sorted = vec![];
        let mut stack = vec![root];
        let mut parent = vec![usize::MAX; n];
        parent[root] = 0;
        while let Some(x) = stack.pop() {
            sorted.push(x);
            for &y in &self[x] {
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
                if self.tar[j] != parent[x] {
                    self.tar.swap(i, j);
                    i += 1;
                }
                j += 1;
            }
            self.start[x + 1] = i;
        }
        assert_eq!(i, n - 1);

        self.tar.truncate(n - 1);
        (sorted, parent)
    }
}

impl<T: Copy + Default> Graph<(usize, T)> {
    /// 重み付き有向グラフを構築する
    ///
    /// 各隣接リストは入力の順番通りになります。
    ///
    /// # Example
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

    /// 無向グラフを、片方の辺だけを入力として構築する
    ///
    /// 各隣接リストは次のような順番になります。
    ///
    /// * まず、入力そのままの辺を順番通りに
    /// * その後で、逆辺を順番通りに
    ///
    ///
    /// # Example
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
        Self { start, tar }
    }
}

impl<E> Graph<E> {
    /// 各頂点の隣接リストを訪問するイテレータを構築する
    ///
    /// # Example
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
        &self.tar[self.start[index]..self.start[index + 1]]
    }
}

impl<'a, E> IntoIterator for &'a Graph<E> {
    type Item = &'a [E];

    type IntoIter = Iter<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// [`Graph::iter`] の戻り値
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
            assert_eq!(g.tar.len(), m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j) in &edges {
                expected_tar[i].push(j);
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.tar[g.start[i]..g.start[i + 1]], expected_tar[i]);
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
            assert_eq!(g.tar.len(), 2 * m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j) in &edges {
                expected_tar[i].push(j);
                expected_tar[j].push(i);
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.tar[g.start[i]..g.start[i + 1]], expected_tar[i]);
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
            assert_eq!(g.tar.len(), m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j, w) in &edges {
                expected_tar[i].push((j, w));
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.tar[g.start[i]..g.start[i + 1]], expected_tar[i]);
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
            assert_eq!(g.tar.len(), 2 * m);

            let mut expected_tar = vec![vec![]; n];
            for &(i, j, w) in &edges {
                expected_tar[i].push((j, w));
                expected_tar[j].push((i, w));
            }

            for i in 0..n {
                assert_eq!(g.start[i + 1] - g.start[i], expected_tar[i].len());
                assert_eq!(g.tar[g.start[i]..g.start[i + 1]], expected_tar[i]);
            }
        }
    }
}
