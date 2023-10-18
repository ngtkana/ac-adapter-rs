//! 重軽分解をします。
//!
//! # 使い方
//!
//! 構造体 [`Hld`] を使いましょう。
//!
//! ## 初期化
//!
//! * [`new`](Hld::new): 根付き木から構築します。
//!
//!
//! ## 基本的なメソッド
//!
//! * [`iter_v`](Hld::iter_v): パスを分解して、両端点を返すイテレータを作ります。
//! * [`iter_e`](Hld::iter_e): それの LCA だけスキップするバージョンです。
//!
//!
//! ## 便利なショートメソッド
//!
//! * [`dist`](Hld::dist): 2 点の間の距離を計算します。
//! * [`lca`](Hld::lca): 2 点の LCA を探します。
//! * [`between`](Hld::between): 3 点が一直線上にあるかどうかを判定します。
//!
//!
//! ## 頂点 ID 翻訳
//!
//! * [`ord`](Hld::ord): 訪問時刻 → もとの頂点番号
//! * [`time`](Hld::time): もとの頂点番号 → 訪問時刻
//!
//!
//! ## せっかく計算してるので公開している情報
//!
//! * [`child`](Hld::child): 親を消したグラフ
//! * [`size`](Hld::size): 部分木のサイズ
//! * [`parent`](Hld::parent): 受け取った根付き木における親
//! * [`head`](Hld::head): heavy path における先頭
//!
//!
//!
//! # Examples
//!
//! ```
//! use hld::Hld;
//! let root = 0;
//! let n = 4;
//! let edges = [[0, 1], [0, 2], [2, 3]];
//! let g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
//! let hld = Hld::new(root, &g);
//!
//! assert_eq!(hld.child(), &[vec![2, 1], Vec::new(), vec![3], Vec::new()]);
//! assert_eq!(hld.time(), &[0, 3, 1, 2]);
//! assert_eq!(hld.ord(), &[0, 2, 3, 1]);
//! assert_eq!(hld.parent(), &[0, 0, 0, 2]);
//! assert_eq!(hld.head(), &[0, 1, 0, 0]);
//! ```
use std::mem::swap;
use std::usize::MAX;

/// 重軽分解
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct Hld {
    child: Vec<Vec<usize>>,
    size: Vec<usize>,
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
    pub fn new(root: usize, g: &[Vec<usize>]) -> Self {
        let (child, [size, time, ord, parent, head]) = hld(root, g);
        Self {
            child,
            size,
            time,
            ord,
            parent,
            head,
        }
    }

    /// 親を消したグラフを返します。
    pub fn child(&self) -> &[Vec<usize>] { &self.child }

    /// 頂点番号から部分木のサイズを引くテーブルを返します。
    pub fn size(&self) -> &[usize] { &self.size }

    /// 頂点番号から訪問時刻を引くテーブルを返します。
    pub fn time(&self) -> &[usize] { &self.time }

    /// 訪問時刻から頂点番号を引くテーブルを返します。
    pub fn ord(&self) -> &[usize] { &self.ord }

    /// 頂点番号から、親の頂点番号を引くテーブルを返します。
    ///
    /// ただし、根の親は自分自身です。
    pub fn parent(&self) -> &[usize] { &self.parent }

    /// 頂点番号から、Heavy path の先頭の頂点番号を引くテーブルを返します。
    pub fn head(&self) -> &[usize] { &self.head }

    /// 頂点 `u`, `v` が隣接頂点であれば `true`、さもなくば `false` を返します。
    ///
    /// # Panics
    ///
    /// * `x`, `v` のいずれかが範囲外
    ///
    /// # Examples
    /// ```
    /// use hld::Hld;
    ///
    /// let g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// let hld = Hld::new(0, &g);
    /// assert_eq!(hld.is_adjacent(0, 3), false); // 1 -- 0 -- 2 -- 3
    /// assert_eq!(hld.is_adjacent(2, 1), false); // 1 -- 0 -- 2 -- 3
    /// assert_eq!(hld.is_adjacent(0, 2), true); // 1 -- 0 -- 2 -- 3
    /// ```
    pub fn is_adjacent(&self, u: usize, v: usize) -> bool {
        assert!(u < self.child.len(), "範囲外です。");
        assert!(v < self.child.len(), "範囲外です。");
        self.parent[u] == v || u == self.parent[v]
    }

    /// `x` の隣接頂点のうち、`toward` との間にあるものを返します。
    ///
    /// # Panics
    ///
    /// * `x`, `toward` のいずれかが範囲外
    /// * `x == toward`
    ///
    /// # Examples
    ///
    /// ```
    /// use hld::Hld;
    ///
    /// let g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// let hld = Hld::new(0, &g);
    /// assert_eq!(hld.adjacent_toward(0, 3), 2); // 1 -- 0 -- 2 -- 3
    /// assert_eq!(hld.adjacent_toward(2, 1), 0); // 1 -- 0 -- 2 -- 3
    /// ```
    pub fn adjacent_toward(&self, x: usize, toward: usize) -> usize {
        assert!(x < self.child.len(), "範囲外です。");
        assert!(toward < self.child.len(), "範囲外です。");
        assert_ne!(
            x, toward,
            "`x = toward = {} となっており、方向がわかりません。",
            x
        );
        if self.is_ancestor_of(x, toward) {
            self.child[x]
                .iter()
                .copied()
                .find(|&y| self.is_ancestor_of(y, toward))
                .unwrap()
        } else {
            self.parent[x]
        }
    }

    /// 2 つの頂点番号から、その間の距離を返します。
    ///
    /// # Panics
    ///
    /// * `u`, `v` のいずれかが範囲外
    ///
    /// # Examples
    ///
    /// ```
    /// use hld::Hld;
    ///
    /// let mut g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// let hld = Hld::new(0, &mut g);
    /// assert_eq!(hld.dist(1, 3), 3); // 1 -- 0 -- 2 -- 3
    /// ```
    pub fn dist(&self, u: usize, v: usize) -> usize {
        self.iter_e(u, v).map(|(l, r)| r - l + 1).sum::<usize>()
    }

    /// 2 つの頂点番号から、LCA の頂点番号を返します。
    ///
    /// # Panics
    ///
    /// * `p`, `x` のいずれかが範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use hld::Hld;
    ///
    /// let mut g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// let hld = Hld::new(0, &mut g);
    /// assert_eq!(hld.lca(1, 3), 0);
    /// ```
    pub fn lca(&self, u: usize, v: usize) -> usize {
        let (u, v) = self.iter_v(u, v).last().unwrap();
        self.ord[u.min(v)]
    }

    /// `p` が `u` の祖先であれば `true`、さもなくば `false` です。
    ///
    /// # Panics
    ///
    /// * `u`, `v` のいずれかが範囲外
    ///
    /// # Examples
    ///
    /// ```
    /// use hld::Hld;
    ///
    /// let g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// let hld = Hld::new(0, &g);
    /// assert_eq!(hld.is_ancestor_of(0, 3), true);
    /// assert_eq!(hld.is_ancestor_of(1, 3), false);
    /// assert_eq!(hld.is_ancestor_of(3, 0), false);
    /// ```
    pub fn is_ancestor_of(&self, p: usize, u: usize) -> bool { self.lca(p, u) == p }

    /// 3 つの頂点番号 `a`, `b`, `c` について、`b` が `a` と `c` を結ぶパス上にあれば
    ///   `true`、さもなくば `false` を返します。
    ///
    /// # Panics
    ///
    /// * `a`, `b`, `c` のいずれかが範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use hld::Hld;
    ///
    /// let g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// // 1 -- 0 -- 2 -- 3
    /// let hld = Hld::new(0, &g);
    /// assert_eq!(hld.between(1, 0, 2), true);
    /// assert_eq!(hld.between(1, 3, 2), false);
    /// assert_eq!(hld.between(1, 2, 2), true);
    /// ```
    pub fn between(&self, a: usize, b: usize, c: usize) -> bool {
        let mid = self.time[b];
        self.iter_v(a, c)
            .any(|(left, right)| (left..=right).contains(&mid))
    }

    /// 2 つの頂点番号から、その間のパスを Heavy path
    /// に分解して、各々両端の頂点**の訪問時刻**を返すイテレータを作ります。
    /// つまり、`f` の引数は閉区間です。
    ///
    /// # Panics
    ///
    /// * `u`, `v` のいずれかが範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use hld::Hld;
    ///
    /// let g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// // 1 -- 0 -- 2 -- 3
    /// let hld = Hld::new(0, &g);
    /// let vtx = hld
    ///     .iter_v(1, 3)
    ///     .map(|(u, v)| (hld.ord()[u], hld.ord()[v])) // 頂点番号に変換
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     vtx.as_slice(),
    ///     &[(1, 1), (0, 3)], // [ 1 ] + [ 0 -- 2 -- 3 ]
    /// );
    /// ```
    pub fn iter_v(&self, u: usize, v: usize) -> IterV<'_> {
        IterV {
            hld: self,
            u,
            v,
            finish: false,
        }
    }

    /// [`Self::iter_v`] とほぼ同様ですが、LCA だけスキップします。
    ///
    /// # Panics
    ///
    /// * `u`, `v` のいずれかが範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use hld::Hld;
    ///
    /// let g = vec![vec![1, 2], vec![0], vec![0, 3], vec![2]];
    ///
    /// let hld = Hld::new(0, &g);
    /// let vtx = hld
    ///     .iter_e(1, 3)
    ///     .map(|(u, v)| (hld.ord()[u], hld.ord()[v])) // 頂点番号に変換
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     vtx.as_slice(),
    ///     &[(1, 1), (2, 3)], // lca = 0 がスキップされていますね。
    /// );
    /// ```
    pub fn iter_e(&self, u: usize, v: usize) -> IterE<'_> {
        IterE {
            hld: self,
            u,
            v,
            finish: false,
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct IterV<'a> {
    hld: &'a Hld,
    u: usize,
    v: usize,
    finish: bool,
}
impl Iterator for IterV<'_> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.finish {
            return None;
        }
        let Self { hld, u, v, .. } = self;
        if hld.time[*u] > hld.time[*v] {
            swap(u, v);
        }
        Some(if hld.head[*u] == hld.head[*v] {
            self.finish = true;
            (hld.time[*u], hld.time[*v])
        } else {
            let h = hld.head[*v];
            let ans = (hld.time[h], hld.time[*v]);
            assert_ne!(hld.parent[h], h, "入力のグラフが非連結です。");
            *v = hld.parent[h];
            ans
        })
    }
}
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct IterE<'a> {
    hld: &'a Hld,
    u: usize,
    v: usize,
    finish: bool,
}
impl Iterator for IterE<'_> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.finish {
            return None;
        }
        let Self { hld, u, v, .. } = self;
        if hld.time[*u] > hld.time[*v] {
            swap(u, v);
        }
        if hld.head[*u] == hld.head[*v] {
            self.finish = true;
            if *u == *v {
                None
            } else {
                Some((hld.time[*u] + 1, hld.time[*v]))
            }
        } else {
            let h = hld.head[*v];
            let ans = (hld.time[h], hld.time[*v]);
            assert_ne!(hld.parent[h], h, "入力のグラフが非連結です。");
            *v = hld.parent[h];
            Some(ans)
        }
    }
}

fn hld(root: usize, g: &[Vec<usize>]) -> (Vec<Vec<usize>>, [Vec<usize>; 5]) {
    let n = g.len();
    let mut size = vec![1; n];
    let mut child = vec![Vec::<usize>::new(); n];
    dfs(root, root, g, &mut size, &mut child);
    let mut ord = Vec::new();
    let mut time = vec![MAX; n];
    let mut parent = vec![MAX; n];
    let mut head = vec![MAX; n];
    parent[root] = root;
    head[root] = root;
    efs(root, &child, &mut time, &mut ord, &mut parent, &mut head);
    assert!(parent.iter().all(|&x| x != MAX), "入力が非連結です。");
    (child, [size, time, ord, parent, head])
}

fn dfs(x: usize, p: usize, g: &[Vec<usize>], size: &mut [usize], child: &mut [Vec<usize>]) {
    let mut gx = g[x].iter().copied().filter(|&y| y != p).collect::<Vec<_>>();
    if !gx.is_empty() {
        for &y in &gx {
            dfs(y, x, g, size, child);
            size[x] += size[y];
        }
        let max_position = (0..gx.len()).max_by_key(|&i| size[gx[i]]).unwrap();
        gx.swap(0, max_position);
    }
    child[x] = gx;
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
    use super::hld;
    use super::Hld;
    use bfs::calc_dist;
    use bfs::find_path;
    use itertools::Itertools;
    use make_graph::array_make_undirected;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use randtools::Tree;
    use std::mem::swap;
    use std::usize::MAX;

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
            let g = rng.sample(Tree(n));
            let mut parent = vec![MAX; n];
            parent[root] = root;
            dfs(root, root, &g, &mut parent);
            let hld = Hld::new(root, &g);
            assert_eq!(hld.parent(), parent.as_slice());
        }
    }

    #[test]
    fn test_tree_dist() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..12);
            let root = rng.gen_range(0..n);
            let g = rng.sample(Tree(n));
            let dist = (0..n).map(|i| calc_dist(i, &g)).collect_vec();
            let hld = Hld::new(root, &g);
            for (i, dist_i) in dist.iter().enumerate() {
                for (j, &d) in dist_i.iter().enumerate() {
                    let result = hld.dist(i, j);
                    let expected = d as usize;
                    assert_eq!(result, expected);
                }
            }
        }
    }

    #[test]
    fn test_preorder() {
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
            let g = rng.sample(Tree(n));
            let mut height = vec![MAX; n];
            let mut parent = vec![MAX; n];
            height[root] = 1;
            parent[root] = root;
            dfs(root, root, &g, &mut height, &mut parent);
            let hld = Hld::new(root, &g);
            for i in 0..n {
                for j in 0..n {
                    // lca
                    {
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
                    // is_ancestor_of
                    {
                        let result = hld.is_ancestor_of(i, j);
                        let expected = || -> bool {
                            let mut j = j;
                            while i != j {
                                if j == parent[j] {
                                    return false;
                                }
                                j = parent[j]
                            }
                            true
                        }();
                        assert_eq!(result, expected);
                    }
                    // is_adjacent
                    {
                        let result = hld.is_adjacent(i, j);
                        let expected = parent[i] == j || i == parent[j];
                        assert_eq!(result, expected);
                    }
                    // child_toward
                    if i != j {
                        let result = hld.adjacent_toward(i, j);
                        assert!(hld.is_adjacent(result, i));
                        hld.between(i, result, j);
                    }
                }
            }
        }
    }

    #[test]
    fn test_tree_between() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..12);
            let root = rng.gen_range(0..n);
            let g = rng.sample(Tree(n));
            let dist = (0..n).map(|i| calc_dist(i, &g)).collect_vec();
            let hld = Hld::new(root, &g);
            for i in 0..n {
                for j in 0..n {
                    for k in 0..n {
                        let result = hld.between(i, j, k);
                        let expected = dist[i][j] + dist[j][k] == dist[i][k];
                        assert_eq!(result, expected);
                    }
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
            let g = orig_g.clone();
            let hld = Hld::new(root, &g);
            let a = (0..n).map(|i| 1u64 << i).collect::<Vec<_>>();
            let a_sorted = hld.ord.iter().map(|&i| a[i]).collect::<Vec<_>>();
            for i in 0..n {
                for j in 0..n {
                    let result = hld
                        .iter_v(i, j)
                        .map(|(l, r)| a_sorted[l..=r].iter().sum::<u64>())
                        .sum::<u64>();
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
        let (g, [size, time, ord, parent, head]) = test_dfs_efs_impl(n, &edges);
        assert_eq!(size, vec![4, 1, 2, 1]);
        assert_eq!(g, vec![vec![2, 1], Vec::new(), vec![3], Vec::new()]);
        assert_eq!(time, vec![0, 3, 1, 2]);
        assert_eq!(ord, vec![0, 2, 3, 1]);
        assert_eq!(parent, vec![0, 0, 0, 2]);
        assert_eq!(head, vec![0, 1, 0, 0]);
    }

    #[test]
    fn test_hand_9vtx() {
        let n = 9;
        let edges = [[0, 2], [0, 3], [1, 2], [2, 5], [3, 8], [4, 6], [5, 6], [
            5, 7,
        ]];
        let (g, [size, time, ord, parent, head]) = test_dfs_efs_impl(n, &edges);
        assert_eq!(g, vec![
            vec![2, 3], // 0
            Vec::new(), // 1
            vec![5, 1], // 2
            vec![8],    // 3
            Vec::new(), // 4
            vec![6, 7], // 5
            vec![4],    // 6
            Vec::new(), // 7
            Vec::new(), // 8
        ]);
        assert_eq!(size, vec![9, 1, 6, 2, 1, 4, 2, 1, 1]);
        assert_eq!(time, vec![0, 6, 1, 7, 4, 2, 3, 5, 8]);
        assert_eq!(ord, vec![0, 2, 5, 6, 4, 7, 1, 3, 8]);
        assert_eq!(parent, vec![0, 2, 0, 0, 6, 2, 5, 5, 3]);
        assert_eq!(head, vec![0, 1, 0, 3, 0, 0, 0, 7, 3]);
    }

    #[allow(clippy::type_complexity)]
    fn test_dfs_efs_impl(n: usize, edges: &[[usize; 2]]) -> (Vec<Vec<usize>>, [Vec<usize>; 5]) {
        assert_eq!(edges.len() + 1, n);
        let r = 0;
        let g = array_make_undirected(n, edges);
        hld(r, &g)
    }
}
