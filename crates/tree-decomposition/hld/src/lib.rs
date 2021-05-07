//! 重軽分解をします。
//!
//! # Examples
//!
//! ```
//! use hld::Hld;
//! let root = 0;
//! let n = 4;
//! let edges = [[0, 1], [0, 2], [2, 3]];
//! let mut g = vec![
//!     vec![1, 2],
//!     vec![0],
//!     vec![0, 3],
//!     vec![2],
//! ];
//! let hld = Hld::new(root, &mut g);
//!
//! assert_eq!(g, vec![vec![2, 1], Vec::new(), vec![3], Vec::new()]);
//! assert_eq!(hld.time(), &[0, 3, 1, 2]);
//! assert_eq!(hld.ord(), &[0, 2, 3, 1]);
//! assert_eq!(hld.parent(), &[0, 0, 0, 2]);
//! assert_eq!(hld.head(), &[0, 1, 0, 0]);
//! ```
use std::{mem::swap, usize::MAX};

/// 重軽分解
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Hld {
    time: Vec<usize>,
    ord: Vec<usize>,
    parent: Vec<usize>,
    head: Vec<usize>,
}
impl Hld {
    /// HLD を構築するとともに、受け取ったグラフから親リンクを削除します。
    ///
    /// # 制約
    ///
    /// 入力は木である（根をひとつしか指定しないことからもわかるように、森はだめです。）
    ///
    pub fn new(root: usize, g: &mut [Vec<usize>]) -> Self {
        let (time, ord, parent, head) = hld(root, g);
        Self {
            time,
            ord,
            parent,
            head,
        }
    }
    /// 頂点番号から訪問時刻を引くテーブルを返します。
    pub fn time(&self) -> &[usize] {
        &self.time
    }
    /// 訪問時刻から頂点番号を引くテーブルを返します。
    pub fn ord(&self) -> &[usize] {
        &self.ord
    }
    /// 頂点番号から、親の頂点番号を引くテーブルを返します。
    ///
    /// ただし、根の親は自分自身です。
    pub fn parent(&self) -> &[usize] {
        &self.parent
    }
    /// 頂点番号から、Heavy path の先頭の頂点番号を引くテーブルを返します。
    pub fn head(&self) -> &[usize] {
        &self.head
    }
    /// 2 つの頂点番号から、LCA の先頭の頂点番号を返します。
    pub fn lca(&self, u: usize, v: usize) -> usize {
        __internal_for_each(self, u, v, |_, _| {}, true)
    }
    /// 2 つの頂点番号から、その間のパスを Heavy path に分解して、各々両端の頂点を処理します。
    ///
    /// つまり、`f` の引数は閉区間です。
    pub fn for_each_vertex(&self, u: usize, v: usize, f: impl FnMut(usize, usize)) -> usize {
        __internal_for_each(self, u, v, f, true)
    }
    /// [`Self::for_each_vertex`] とほぼ同様ですが、LCA だけスキップします。
    ///
    /// つまり、`f` の引数は閉区間です。
    pub fn for_each_edge(&self, u: usize, v: usize, f: impl FnMut(usize, usize)) -> usize {
        __internal_for_each(self, u, v, f, false)
    }
}

fn __internal_for_each(
    hld: &Hld,
    mut u: usize,
    mut v: usize,
    mut f: impl FnMut(usize, usize),
    contain_lca: bool,
) -> usize {
    while hld.head[u] != hld.head[v] {
        if hld.time[u] > hld.time[v] {
            swap(&mut u, &mut v);
        }
        let h = hld.head[v];
        f(hld.time[h], hld.time[v]);
        assert_ne!(hld.parent[h], h, "入力のグラフが非連結です。");
        v = hld.parent[h];
    }
    if hld.time[u] > hld.time[v] {
        swap(&mut u, &mut v);
    }
    if contain_lca {
        f(hld.time[u], hld.time[v]);
    } else if hld.time[u] != hld.time[v] {
        f(hld.time[u] + 1, hld.time[v]);
    }
    hld.ord[hld.time[u]]
}

fn hld(root: usize, g: &mut [Vec<usize>]) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
    dfs(root, root, g);
    let mut ord = Vec::new();
    let mut time = vec![MAX; g.len()];
    let mut parent = vec![MAX; g.len()];
    let mut head = vec![MAX; g.len()];
    parent[root] = root;
    head[root] = root;
    efs(root, &g, &mut time, &mut ord, &mut parent, &mut head);
    assert!(parent.iter().all(|&x| x != MAX), "入力が非連結です。");
    (time, ord, parent, head)
}

fn dfs(x: usize, p: usize, g: &mut [Vec<usize>]) -> usize {
    let mut child = g[x].iter().copied().filter(|&y| y != p).collect::<Vec<_>>();
    let mut size = 1;
    let mut max_size = 1;
    for i in 0..child.len() {
        let s = dfs(child[i], x, g);
        if max_size < s {
            max_size = s;
            child.swap(0, i);
        }
        size += s;
    }
    g[x] = child;
    size
}

fn efs(
    x: usize,
    g: &[Vec<usize>],
    time: &mut [usize],
    ord: &mut Vec<usize>,
    parent: &mut [usize],
    head: &mut [usize],
) {
    time[x] = ord.len();
    ord.push(x);
    if !g[x].is_empty() {
        let h = g[x][0];
        head[h] = head[x];
        parent[h] = x;
        efs(h, g, time, ord, parent, head);
        for &y in &g[x][1..] {
            head[y] = y;
            parent[y] = x;
            efs(y, g, time, ord, parent, head);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::mem::swap;

    use bfs::find_path;

    use {
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::Tree,
        std::usize::MAX,
        {
            super::{hld, Hld},
            make_graph::array_make_undirected,
        },
    };

    #[test]
    fn test_tree_parent() {
        fn dfs(x: usize, p: usize, g: &[Vec<usize>], parent: &mut [usize]) {
            for y in g[x].iter().copied().filter(|&y| y != p) {
                parent[y] = x;
                dfs(y, x, g, parent);
            }
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..12);
            let root = rng.gen_range(0..n);
            let mut g = rng.sample(Tree(n));
            let mut parent = vec![MAX; n];
            parent[root] = root;
            dfs(root, root, &g, &mut parent);
            let hld = Hld::new(root, &mut g);
            assert_eq!(hld.parent(), parent.as_slice());
        }
    }

    #[test]
    fn test_tree_lca() {
        fn dfs(x: usize, p: usize, g: &[Vec<usize>], height: &mut [usize], parent: &mut [usize]) {
            for y in g[x].iter().copied().filter(|&y| y != p) {
                parent[y] = x;
                height[y] = height[x] + 1;
                dfs(y, x, g, height, parent);
            }
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..12);
            let root = rng.gen_range(0..n);
            let mut g = rng.sample(Tree(n));
            let mut height = vec![MAX; n];
            let mut parent = vec![MAX; n];
            height[root] = 1;
            parent[root] = root;
            dfs(root, root, &g, &mut height, &mut parent);
            let hld = Hld::new(root, &mut g);
            for i in 0..n {
                for j in 0..n {
                    let result = hld.lca(i, j);
                    let mut i = i;
                    let mut j = j;
                    if height[i] > height[j] {
                        swap(&mut i, &mut j);
                    }
                    while height[i] < height[j] {
                        j = parent[j];
                    }
                    while i != j {
                        i = parent[i];
                        j = parent[j];
                    }
                    let expected = i;
                    assert_eq!(result, expected);
                }
            }
        }
    }

    #[test]
    fn test_tree_path_sum() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..12);
            let root = rng.gen_range(0..n);
            let orig_g = rng.sample(Tree(n));
            let mut g = orig_g.clone();
            let hld = Hld::new(root, &mut g);
            let a = (0..n).map(|i| 1u64 << i).collect::<Vec<_>>();
            let a_sorted = hld.ord.iter().map(|&i| a[i]).collect::<Vec<_>>();
            for i in 0..n {
                for j in 0..n {
                    let mut result = 0;
                    hld.for_each_vertex(i, j, |l, r| {
                        result += a_sorted[l..=r].iter().sum::<u64>();
                    });
                    let path = find_path(i, j, &orig_g).unwrap();
                    let expected = path.iter().map(|&i| a[i]).sum::<u64>();
                    assert_eq!(result, expected);
                }
            }
        }
    }

    #[test]
    fn test_hand_4vtx() {
        let n = 4;
        let edges = [[0, 1], [0, 2], [2, 3]];
        let (g, time, ord, parent, head) = test_dfs_efs_impl(n, &edges);
        assert_eq!(g, vec![vec![2, 1], Vec::new(), vec![3], Vec::new()]);
        assert_eq!(time, vec![0, 3, 1, 2]);
        assert_eq!(ord, vec![0, 2, 3, 1]);
        assert_eq!(parent, vec![0, 0, 0, 2]);
        assert_eq!(head, vec![0, 1, 0, 0]);
    }

    #[test]
    fn test_hand_9vtx() {
        let n = 9;
        let edges = [
            [0, 2],
            [0, 3],
            [1, 2],
            [2, 5],
            [3, 8],
            [4, 6],
            [5, 6],
            [5, 7],
        ];
        let (g, time, ord, parent, head) = test_dfs_efs_impl(n, &edges);
        assert_eq!(
            g,
            vec![
                vec![2, 3], // 0
                Vec::new(), // 1
                vec![5, 1], // 2
                vec![8],    // 3
                Vec::new(), // 4
                vec![6, 7], // 5
                vec![4],    // 6
                Vec::new(), // 7
                Vec::new(), // 8
            ]
        );
        assert_eq!(time, vec![0, 6, 1, 7, 4, 2, 3, 5, 8]);
        assert_eq!(ord, vec![0, 2, 5, 6, 4, 7, 1, 3, 8]);
        assert_eq!(parent, vec![0, 2, 0, 0, 6, 2, 5, 5, 3]);
        assert_eq!(head, vec![0, 1, 0, 3, 0, 0, 0, 7, 3]);
    }

    #[allow(clippy::type_complexity)]
    fn test_dfs_efs_impl(
        n: usize,
        edges: &[[usize; 2]],
    ) -> (
        Vec<Vec<usize>>,
        Vec<usize>,
        Vec<usize>,
        Vec<usize>,
        Vec<usize>,
    ) {
        assert_eq!(edges.len() + 1, n);
        let r = 0;
        let mut g = array_make_undirected(n, edges);
        let (ord, time, parent, head) = hld(r, &mut g);
        (g, ord, time, parent, head)
    }
}
