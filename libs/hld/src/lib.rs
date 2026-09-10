//! 木を「重い辺」優先で連結パスに分解し、2頂点間パスを $O(\log n)$ 個の区間に分解する。
//!
//! 各頂点から部分木サイズ最大の子への辺を「重い辺」とし、重い辺だけを辿ってできる極大な鎖を連結パスとする。
//! 連結パスごとに DFS 順の連続番号（シリアル番号）を割り当てると、根から任意の頂点へのパスは高々 $O(\log n)$ 本の連結パスをまたぐ。
//! 軽い辺（重い辺でない辺）を1回通るごとに部分木サイズが半分以下になるため。
//!
//! # 仕様
//! - 頂点数 $n$ の木を親配列（[`Hld::from_parents`]）または辺集合（[`Hld::from_edges`]）から構築する
//! - [`Hld::path_segments`] は2頂点間のパスを [`PathSegment`]（連結パス内の連続区間）の列に、根側から葉側の順で分解する。区間数は $O(\log n)$
//! - [`Hld::lca`], [`Hld::dist`], [`Hld::in_this_order`] は `path_segments` を用いて実装される
//!
//! # 例
//! ```
//! use hld::Hld;
//!
//! //     0
//! //     |
//! //     1
//! //    / \
//! //   2   3
//! let parent = vec![0, 0, 1, 1];
//! let (hld, _g) = Hld::from_parents(parent);
//!
//! assert_eq!(hld.lca(2, 3), 1);
//! assert_eq!(hld.dist(2, 3), 2);
//! assert!(hld.in_this_order(2, 1, 3));
//! ```
//!
//! # 計算量
//! - [`Hld::from_parents`], [`Hld::from_edges`]: $O(n)$
//! - [`Hld::path_segments`], [`Hld::lca`], [`Hld::dist`], [`Hld::in_this_order`]: $O(\log n)$

use std::iter::FusedIterator;

/// 重軽分解の結果。
#[doc(alias = "Heavy-Light Decomposition")]
pub struct Hld {
    /// 元の頂点番号 -> 親の元の頂点番号
    parent: Vec<usize>,
    /// 元の頂点番号 -> シリアル番号
    index: Vec<usize>,
    /// 元の頂点番号 -> 連結パスの先頭（根側）の元の頂点番号
    head: Vec<usize>,
}
impl Hld {
    /// 指定した頂点のシリアル番号を返す。
    pub fn serial_id(&self, i: usize) -> usize {
        self.index[i]
    }

    /// $p _ 0, \dots, p _ { n - 1 }$ から構築する。根の親は**自分自身でなければならない**。
    pub fn from_parents(parent: Vec<usize>) -> (Self, Vec<Vec<usize>>) {
        let mut g = vec![Vec::new(); parent.len()];
        let mut root = usize::MAX;
        for (i, &p) in parent.iter().enumerate() {
            if p == i {
                assert_eq!(root, usize::MAX, "multiple roots");
                root = i;
            } else {
                g[p].push(i);
            }
        }
        (build_hld(root, &mut g, parent), g)
    }

    /// 辺集合をイテレータで受け取る版の [`from_edges`](Self::from_edges)
    pub fn from_edges(
        root: usize,
        edges: impl ExactSizeIterator<Item = (usize, usize)>,
    ) -> (Self, Vec<Vec<usize>>) {
        let mut g = vec![Vec::new(); edges.len() + 1];
        for (i, j) in edges {
            g[i].push(j);
            g[j].push(i);
        }
        let mut stack = vec![root];
        let mut parent = vec![usize::MAX; g.len()];
        parent[root] = root;
        while let Some(i) = stack.pop() {
            g[i].retain(|&j| parent[i] != j);
            for &j in &g[i] {
                parent[j] = i;
                stack.push(j);
            }
        }
        (build_hld(root, &mut g, parent), g)
    }

    /// 有向パス `from --> to` をパスセグメント列に分解する。
    ///
    /// 要素の型は [`PathSegment`]。
    pub fn path_segments(&self, from: usize, to: usize) -> PathSegments<'_> {
        PathSegments {
            hld: self,
            from,
            to,
            exhausted: false,
        }
    }

    /// 最小共通祖先（LCA）を返す。
    pub fn lca(&self, i: usize, j: usize) -> usize {
        self.path_segments(i, j)
            .find(|s| s.contains_lca)
            .map(|s| s.higher)
            .unwrap()
    }

    /// 2頂点間の距離を返す。
    pub fn dist(&self, i: usize, j: usize) -> usize {
        self.path_segments(i, j)
            .map(|s| s.vertex_count(self))
            .sum::<usize>()
            - 1
    }

    /// `i`, `j`, `k` がこの順に並んでいるかを判定する。
    pub fn in_this_order(&self, i: usize, j: usize, k: usize) -> bool {
        let m = self.index[j];
        self.path_segments(i, k)
            .any(|s| (self.index[s.higher]..=self.index[s.deeper]).contains(&m))
    }
}

/// [`Hld::path_segments()`] の要素。
#[derive(Clone, Copy)]
pub struct PathSegment {
    /// 根側の端点の元の頂点番号
    pub higher: usize,
    /// 葉側の端点の元の頂点番号
    pub deeper: usize,
    /// LCA を含む区間なら true
    pub contains_lca: bool,
    /// `from --> to` と `i --> j` の向きが逆なら true
    pub oppsite: bool,
}
impl PathSegment {
    /// 根側の端点のシリアル番号を返す。
    pub fn higher_serial_id(&self, hld: &Hld) -> usize {
        hld.index[self.higher]
    }

    /// 葉側の端点のシリアル番号を返す。
    pub fn deeper_serial_id(&self, hld: &Hld) -> usize {
        hld.index[self.deeper]
    }

    /// パスセグメントに含まれる頂点数を返す。
    pub fn vertex_count(&self, hld: &Hld) -> usize {
        hld.index[self.deeper] - hld.index[self.higher] + 1
    }
}

/// [`Hld::path_segments()`] のイテレータ。
pub struct PathSegments<'a> {
    hld: &'a Hld,
    from: usize,
    to: usize,
    exhausted: bool,
}
impl Iterator for PathSegments<'_> {
    type Item = PathSegment;

    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            hld:
                Hld {
                    index,
                    head,
                    parent,
                },
            from,
            to,
            exhausted,
        } = *self;
        (!exhausted).then_some(())?;
        let contains_lca = head[from] == head[to];
        let oppsite = index[from] > index[to];
        #[allow(clippy::collapsible_else_if)]
        let (higher, deeper) = if contains_lca {
            self.exhausted = true;
            if oppsite {
                (to, from)
            } else {
                (from, to)
            }
        } else {
            if oppsite {
                self.from = parent[head[from]];
                (head[from], from)
            } else {
                self.to = parent[head[to]];
                (head[to], to)
            }
        };
        Some(PathSegment {
            higher,
            deeper,
            contains_lca,
            oppsite,
        })
    }
}
impl FusedIterator for PathSegments<'_> {}

fn build_hld(root: usize, g: &mut [Vec<usize>], parent: Vec<usize>) -> Hld {
    let n = g.len();
    dfs_heavy_first(root, g);
    let mut index = vec![usize::MAX; n];
    let mut head = vec![usize::MAX; n];
    head[root] = root;
    dfs_calculate(root, g, &mut head, &mut index);
    Hld {
        parent,
        index,
        head,
    }
}

// Iterative (stack-based) preorder, to avoid stack overflow on deep (e.g. path-shaped) trees.
fn dfs_calculate(root: usize, g: &[Vec<usize>], head: &mut [usize], index: &mut [usize]) {
    let mut stack = vec![root];
    let mut current = 0;
    while let Some(i) = stack.pop() {
        index[i] = current;
        current += 1;
        for (e, &j) in g[i].iter().enumerate().rev() {
            head[j] = if e == 0 { head[i] } else { j };
            stack.push(j);
        }
    }
}

// Iterative (stack-based) postorder, to avoid stack overflow on deep (e.g. path-shaped) trees.
fn dfs_heavy_first(root: usize, g: &mut [Vec<usize>]) {
    let mut order = Vec::new();
    let mut stack = vec![root];
    while let Some(i) = stack.pop() {
        order.push(i);
        stack.extend(g[i].iter().copied());
    }
    let mut size = vec![1; g.len()];
    for &i in order.iter().rev() {
        let mut max = 0;
        for e in 0..g[i].len() {
            let csize = size[g[i][e]];
            if max < csize {
                max = csize;
                g[i].swap(0, e);
            }
        }
        size[i] = 1 + g[i].iter().map(|&j| size[j]).sum::<usize>();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::cmp::Ordering;
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;
    use std::collections::HashSet;

    fn random_tree(rng: &mut StdRng, n: usize) -> Vec<(usize, usize)> {
        assert_ne!(n, 0);
        if n == 1 {
            return Vec::new();
        }
        let prufer = (0..n - 2)
            .map(|_| rng.gen_range(0..n))
            .chain(std::iter::once(n - 1))
            .collect::<Vec<_>>();
        let mut count = vec![0; n];
        for &y in &prufer {
            count[y] += 1;
        }
        let mut heap = (0..n)
            .filter(|&i| count[i] == 0)
            .map(Reverse)
            .collect::<BinaryHeap<_>>();
        prufer
            .into_iter()
            .map(|y| {
                let Reverse(x) = heap.pop().unwrap();
                count[y] -= 1;
                if count[y] == 0 {
                    heap.push(Reverse(y));
                }
                (x, y)
            })
            .collect::<Vec<_>>()
    }

    #[test]
    fn test_fields() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let edges = random_tree(&mut rng, n);
            let root = rng.gen_range(0..n);
            let (hld, g) = Hld::from_edges(root, edges.iter().copied());
            let Hld {
                index,
                parent,
                head,
            } = &hld;

            let mut size = vec![1; n];
            {
                let mut stack = vec![root];
                let mut parent = vec![usize::MAX; n];
                let mut serial = Vec::new();
                while let Some(i) = stack.pop() {
                    serial.push(i);
                    for &j in &g[i] {
                        if parent[i] == j {
                            continue;
                        }
                        stack.push(j);
                        parent[j] = i;
                    }
                }
                for &i in serial.iter().rev() {
                    for &j in &g[i] {
                        if parent[i] == j {
                            continue;
                        }
                        size[i] += size[j];
                    }
                }
                assert_eq!(size[root], n);
            }

            // validate `g`
            assert_eq!(g.len(), n);
            {
                let mut edge_set = edges.iter().copied().collect::<HashSet<_>>();
                let mut count = 0;
                for (i, gi) in g.iter().enumerate() {
                    for &j in gi {
                        assert!(size[i] > size[j]);
                        assert!(edge_set.remove(&(i, j)) || edge_set.remove(&(j, i)));
                        count += 1;
                    }
                }
                assert_eq!(count, n - 1);
            }

            // validate `parent`
            {
                let mut edge_set = edges.iter().copied().collect::<HashSet<_>>();
                for (i, &p) in parent.iter().enumerate() {
                    if i == root {
                        assert_eq!(p, root);
                    } else {
                        assert!(edge_set.remove(&(i, p)) || edge_set.remove(&(p, i)));
                    }
                }
            }

            // validate heavy-first
            {
                for gi in &g {
                    for &j in gi {
                        assert!(size[j] <= size[gi[0]]);
                    }
                }
            }

            // validate head
            {
                for (i, gi) in g.iter().enumerate() {
                    for &j in gi {
                        if j == gi[0] {
                            assert_eq!(head[j], head[i]);
                        } else {
                            assert_eq!(head[j], j);
                        }
                    }
                }
            }

            // validate index
            {
                for (i, gi) in g.iter().enumerate() {
                    let mut prev = usize::MAX;
                    for &j in gi {
                        if prev == usize::MAX {
                            assert_eq!(index[i] + 1, index[j]);
                        } else {
                            assert!(prev < index[j]);
                        }
                        prev = index[j];
                    }
                }
            }
        }
    }

    #[test]
    fn test_path_decomposition() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let edges = random_tree(&mut rng, n);
            let root = rng.gen_range(0..n);
            let (hld, g) = Hld::from_edges(root, edges.iter().copied());
            let Hld {
                index,
                parent,
                head,
            } = &hld;

            for _ in 0..q {
                let i = rng.gen_range(0..n);
                let j = rng.gen_range(0..n);
                // find path by graph searching
                let path = {
                    let mut next = vec![usize::MAX; n];
                    let mut stack = vec![j];
                    next[j] = j;
                    while let Some(x) = stack.pop() {
                        for y in g[x].iter().copied().chain((x != root).then_some(parent[x])) {
                            if next[y] == usize::MAX {
                                next[y] = x;
                                stack.push(y);
                            }
                        }
                    }
                    let mut path = vec![i];
                    while path.last() != Some(&j) {
                        let next = next[*path.last().unwrap()];
                        path.push(next);
                    }
                    assert_eq!(path[0], i);
                    assert_eq!(path[path.len() - 1], j);
                    path
                };
                let mut index_to_path_position = vec![usize::MAX; n];
                for (e, &x) in path.iter().enumerate() {
                    index_to_path_position[index[x]] = e;
                }
                let path_segments = hld.path_segments(i, j).collect_vec();

                // validate upper bound
                assert!(path_segments.len() <= 1 + 2 * n.ilog2() as usize);

                // validate the vertex number
                assert_eq!(
                    path_segments
                        .iter()
                        .map(|&s| index[s.deeper] - index[s.higher] + 1)
                        .sum::<usize>(),
                    path.len()
                );

                // validate the vertex set
                for &s in &path_segments {
                    #[allow(clippy::needless_range_loop)]
                    for k in index[s.higher]..=index[s.deeper] {
                        assert_ne!(index_to_path_position[k], usize::MAX);
                    }
                }

                // validate the direction (root --> leaf)
                for &s in &path_segments {
                    assert!(index[s.higher] <= index[s.deeper]);
                }

                // validate the serialness (leafside to rootside)
                for (s, t) in path_segments.iter().copied().tuple_windows() {
                    assert!(index[s.deeper] >= index[t.higher]);
                }

                // validate last
                for (e, &s) in path_segments.iter().enumerate() {
                    assert_eq!(s.contains_lca, (e == path_segments.len() - 1));
                }

                // validate reverse
                for &s in &path_segments {
                    match index_to_path_position[index[s.higher]]
                        .cmp(&index_to_path_position[index[s.deeper]])
                    {
                        Ordering::Less => assert!(!s.oppsite),
                        Ordering::Equal => (),
                        Ordering::Greater => assert!(s.oppsite),
                    }
                }

                // validate greedyness
                {
                    for &s in &path_segments {
                        if !s.contains_lca {
                            assert_eq!(head[s.higher], s.higher);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_queries() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let edges = random_tree(&mut rng, n);
            let root = rng.gen_range(0..n);
            let (hld, g) = Hld::from_edges(root, edges.iter().copied());
            let Hld { index, parent, .. } = &hld;

            let mut serial = (0..n).collect_vec();
            serial.sort_by_key(|&i| index[i]);
            let mut depth = vec![0; n];
            for &i in &serial {
                for &j in &g[i] {
                    depth[j] = depth[i] + 1;
                }
            }

            // validate lca
            for _ in 0..q {
                let i = rng.gen_range(0..n);
                let j = rng.gen_range(0..n);
                let result = hld.lca(i, j);
                let expected = {
                    let mut i = i;
                    let mut j = j;
                    while depth[i] < depth[j] {
                        j = parent[j];
                    }
                    while depth[i] > depth[j] {
                        i = parent[i];
                    }
                    while i != j {
                        i = parent[i];
                        j = parent[j];
                    }
                    i
                };
                assert_eq!(result, expected);
            }

            // validate dist
            for _ in 0..q {
                let i = rng.gen_range(0..n);
                let j = rng.gen_range(0..n);
                let result = hld.dist(i, j);
                let q = hld.lca(i, j);
                let expected = depth[i] + depth[j] - 2 * depth[q];
                assert_eq!(result, expected);
            }

            // validate ordering of three vertices
            for _ in 0..q {
                let i = rng.gen_range(0..n);
                let j = rng.gen_range(0..n);
                let k = rng.gen_range(0..n);
                let result = hld.in_this_order(i, j, k);
                let expected = hld.dist(i, j) + hld.dist(j, k) == hld.dist(i, k);
                assert_eq!(result, expected);
            }
        }
    }
}
