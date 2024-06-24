//! Heavy-Light Decomposition
//!
//! # Usage
//!
//! - Constructor: [`Hld::from_edges()`]
//! - Iterator: [`Hld::path_segments()`]
//! - Fields: [`parent`](Hld::parent), [`index`](Hld::index), [`head`](Hld::head)

use std::iter::FusedIterator;

/// Heavy-Light Decomposition
pub struct Hld {
    /// vertex id -> parent vertex id
    pub parent: Vec<usize>,
    /// vertex id -> vertex index (in the hld order)
    pub index: Vec<usize>,
    /// vertex id -> head vertex id
    pub head: Vec<usize>,
}
impl Hld {
    /// From $p _ 1, \dots, p _ { n - 1 }$. Root is always $0$.
    pub fn from_short_parents(mut parent: Vec<usize>) -> (Self, Vec<Vec<usize>>) {
        parent.insert(0, 0);
        let mut g = vec![Vec::new(); parent.len()];
        for (i, &p) in parent.iter().enumerate().skip(1) {
            g[p].push(i);
        }
        (__build_hld(0, &mut g, parent), g)
    }

    /// From the set of undirected edges $(u _ 0, v _ 0), \dots ( u _ { n - 2 } , v _ { n - 2 } )$
    ///
    /// The second return value `g` is the graph with parents removed.
    pub fn from_edges(root: usize, edges: &[(usize, usize)]) -> (Self, Vec<Vec<usize>>) {
        Self::from_edge_iterator(root, edges.iter().copied())
    }

    /// Iterator version of [`from_edges`](Self::from_edges)
    pub fn from_edge_iterator(
        root: usize,
        edges: impl ExactSizeIterator<Item = (usize, usize)>,
    ) -> (Self, Vec<Vec<usize>>) {
        let mut g = vec![Vec::new(); edges.len() + 1];
        for (i, j) in edges {
            g[i].push(j);
            g[j].push(i);
        }
        let parent = __remove_parent(root, &mut g);
        (__build_hld(root, &mut g, parent), g)
    }

    /// Decompose the (directed) path `from --> to` to the path segments.
    ///
    /// # Items
    ///
    /// * `i`: root-side
    /// * `j`: left-side
    /// * `last`: last path segments (i.e. contains the LCA)
    /// * `reverse`: `from --> to` and `i --> j` is in the different direction
    pub fn path_segments(&self, from: usize, to: usize) -> PathSegments<'_> {
        PathSegments {
            hld: self,
            from,
            to,
            exhausted: false,
        }
    }

    /// Variation of [`path_segments`](Self::path_segments) that returns the `index`.
    pub fn path_segments_by_index(
        &self,
        i: usize,
        j: usize,
    ) -> impl Iterator<Item = (usize, usize, bool, bool)> + '_ {
        self.path_segments(i, j)
            .map(move |(i, j, last, reverse)| (self.index[i], self.index[j], last, reverse))
    }

    /// deprecated
    pub fn ledacy_iter_v(&self, i: usize, j: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.path_segments_by_index(i, j)
            .map(|(i, j, _last, _revresed)| (i, j))
    }

    /// Returns the lca
    pub fn lca(&self, i: usize, j: usize) -> usize {
        self.path_segments(i, j)
            .find(|&(_, _, last, _)| last)
            .map(|(q, _, _, _)| q)
            .unwrap()
    }

    /// Returns the distance between two vertices
    pub fn dist(&self, i: usize, j: usize) -> usize {
        self.path_segments_by_index(i, j)
            .map(|(l, r, last, _)| r - l + usize::from(!last))
            .sum()
    }

    /// `j` lies between `i` and `k`
    pub fn between(&self, i: usize, j: usize, k: usize) -> bool {
        let m = self.index[j];
        self.path_segments_by_index(i, k)
            .any(|(l, r, _, _)| (l..=r).contains(&m))
    }
}

/// Iterator
pub struct PathSegments<'a> {
    hld: &'a Hld,
    from: usize,
    to: usize,
    exhausted: bool,
}
impl Iterator for PathSegments<'_> {
    // i: usize         root-side,
    // j: usize         leaf-side,
    // last: bool       contains-lca
    // reverse: bool    false if from --> to and i --> j coincide
    type Item = (usize, usize, bool, bool);

    fn next(&mut self) -> Option<Self::Item> {
        (!self.exhausted).then_some(())?;
        let Self { hld, from, to, .. } = *self;
        let Hld {
            index,
            head,
            parent,
        } = hld;
        #[allow(clippy::collapsible_else_if)]
        Some(if head[from] == head[to] {
            self.exhausted = true;
            if index[from] < index[to] {
                (from, to, true, false)
            } else {
                (to, from, true, true)
            }
        } else {
            if index[from] < index[to] {
                self.to = parent[head[to]];
                (head[to], to, false, false)
            } else {
                self.from = parent[head[from]];
                (head[from], from, false, true)
            }
        })
    }
}
impl FusedIterator for PathSegments<'_> {}

fn __build_hld(root: usize, g: &mut [Vec<usize>], parent: Vec<usize>) -> Hld {
    let n = g.len();
    __heavy_first(root, g);
    let mut index = vec![usize::MAX; n];
    let mut head = vec![usize::MAX; n];
    head[root] = root;
    __head_and_index(root, &*g, &mut head, &mut index, &mut (0..));
    Hld {
        parent,
        index,
        head,
    }
}
fn __head_and_index(
    i: usize,
    g: &[Vec<usize>],
    head: &mut [usize],
    index: &mut [usize],
    current: &mut std::ops::RangeFrom<usize>,
) {
    index[i] = current.next().unwrap();
    for &j in &g[i] {
        head[j] = if j == g[i][0] { head[i] } else { j };
        __head_and_index(j, g, head, index, current);
    }
}

fn __heavy_first(i: usize, g: &mut [Vec<usize>]) -> usize {
    let mut max = 0;
    let mut size = 1;
    for e in 0..g[i].len() {
        let csize = __heavy_first(g[i][e], g);
        if max < csize {
            max = csize;
            g[i].swap(0, e);
        }
        size += csize;
    }
    size
}

fn __remove_parent(root: usize, g: &mut [Vec<usize>]) -> Vec<usize> {
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
    parent
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
            let n = rng.gen_range(1..=10);
            let edges = random_tree(&mut rng, n);
            let root = rng.gen_range(0..n);
            let (hld, g) = Hld::from_edges(root, &edges);
            let Hld {
                index,
                parent,
                head,
            } = &hld;

            let mut size = vec![1; n];
            {
                let mut stack = vec![root];
                let mut parent = vec![usize::MAX; n];
                let mut sorted = Vec::new();
                while let Some(i) = stack.pop() {
                    sorted.push(i);
                    for &j in &g[i] {
                        if parent[i] == j {
                            continue;
                        }
                        stack.push(j);
                        parent[j] = i;
                    }
                }
                for &i in sorted.iter().rev() {
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
            let n = rng.gen_range(1..=10);
            let q = rng.gen_range(1..=10);
            let edges = random_tree(&mut rng, n);
            let root = rng.gen_range(0..n);
            let (hld, g) = Hld::from_edges(root, &edges);
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
                        .map(|&(i, j, _, _)| index[j] - index[i] + 1)
                        .sum::<usize>(),
                    path.len()
                );

                // validate the vertex set
                for &(i, j, _, _) in &path_segments {
                    #[allow(clippy::needless_range_loop)]
                    for k in index[i]..=index[j] {
                        assert_ne!(index_to_path_position[k], usize::MAX);
                    }
                }

                // validate the direction (root --> leaf)
                for &(i, j, _, _) in &path_segments {
                    assert!(index[i] <= index[j]);
                }

                // validate the sortedness (leafside to rootside)
                for ((_, j, _, _), (k, _, _, _)) in path_segments.iter().copied().tuple_windows() {
                    assert!(index[j] >= index[k]);
                }

                // validate last
                for (e, &(_, _, last, _)) in path_segments.iter().enumerate() {
                    assert_eq!(last, (e == path_segments.len() - 1));
                }

                // validate reverse
                for &(i, j, _, reverse) in &path_segments {
                    match index_to_path_position[index[i]].cmp(&index_to_path_position[index[j]]) {
                        Ordering::Less => assert!(!reverse),
                        Ordering::Equal => (),
                        Ordering::Greater => assert!(reverse),
                    }
                }

                // validate greedyness
                {
                    for &(i, _, last, _) in &path_segments {
                        if !last {
                            assert_eq!(head[i], i);
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
            let n = rng.gen_range(1..=10);
            let q = rng.gen_range(1..=10);
            let edges = random_tree(&mut rng, n);
            let root = rng.gen_range(0..n);
            let (hld, g) = Hld::from_edges(root, &edges);
            let Hld { index, parent, .. } = &hld;

            let mut sorted = (0..n).collect_vec();
            sorted.sort_by_key(|&i| index[i]);
            let mut depth = vec![0; n];
            for &i in &sorted {
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

            // validate betweenness
            for _ in 0..q {
                let i = rng.gen_range(0..n);
                let j = rng.gen_range(0..n);
                let k = rng.gen_range(0..n);
                let result = hld.between(i, j, k);
                let expected = hld.dist(i, j) + hld.dist(j, k) == hld.dist(i, k);
                assert_eq!(result, expected);
            }
        }
    }
}
