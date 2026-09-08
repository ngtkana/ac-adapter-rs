//! 無向グラフの low-link を計算し、関節点・橋・(2-)連結成分分解を求める。
//!
//! DFS 木を構築し、各頂点に pre-order 番号 $\mathrm{ord}(v)$ を振ったうえで、
//! $v$ の部分木から木辺を任意回・後退辺を高々 1 回辿って到達できる頂点の
//! $\mathrm{ord}$ の最小値 $\mathrm{low}(v)$ を帰りがけ順に計算する。
//! 関節点・橋はこの $\mathrm{ord}$ と $\mathrm{low}$ の大小比較だけで判定でき、
//! さらに DFS の帰りがけ順に辺・頂点をスタックへ積んで条件成立ごとに区切ることで
//! 2-連結成分・2-辺連結成分の分解も得られる。
//!
//! # 仕様
//!
//! - 型: [`LowLink`]（グラフは無向・多重辺・自己ループを許容）
//! - 構築: [`LowLink::new`] で頂点数 $n$ の空グラフを作り、[`LowLink::add_edge`] で辺を
//!   追加し、[`LowLink::build`] でビルドする
//! - 頂点が関節点か判定: [`LowLink::is_articulation_point`]
//! - 辺が橋か判定（辺が存在しないときの戻り値は未定義）: [`LowLink::is_bridge_unchecked`]
//! - 2-連結成分分解（辺の分割）: [`LowLink::biconnected_components`]
//! - 2-辺連結成分分解（頂点の分割）: [`LowLink::two_edge_components`]
//!
//! # 例
//!
//! ```
//! use low_link::LowLink;
//!
//! let mut low_link = LowLink::new(4);
//! low_link.add_edge(0, 1);
//! low_link.add_edge(0, 2);
//! low_link.add_edge(1, 2);
//! low_link.add_edge(2, 3);
//! low_link.build();
//!
//! assert!(low_link.is_articulation_point(2)); // 頂点 2 を除くと頂点 3 が孤立
//! assert!(low_link.is_bridge_unchecked(2, 3)); // 辺 (2, 3) は橋
//! ```
//!
//! # 計算量
//!
//! - ビルド（[`LowLink::build`]）: $O(n + m)$（$n$: 頂点数、$m$: 辺数）
//! - 関節点判定（[`LowLink::is_articulation_point`]）: $O(\deg x)$
//! - 橋判定（[`LowLink::is_bridge_unchecked`]）: $O(1)$
//! - 各種成分分解（[`LowLink::biconnected_components`], [`LowLink::two_edge_components`]）: $O(n + m)$

use std::mem::replace;
use std::mem::swap;
use std::mem::take;

/// 無向グラフの low-link を管理する構造体。
///
/// [`add_edge`](Self::add_edge) で辺を追加してから [`build`](Self::build) を呼ぶと、
/// 関節点・橋・(2-)連結成分分解のクエリに答えられるようになる。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct LowLink {
    g: Vec<Vec<usize>>, /* 隣接リストです。未ビルドならば無向グラフ、ビルド済みならば木辺と後退辺のみが入っています。 */
    sorted: Vec<usize>, // [i]: pre-order で i 番目である頂点の番号
    ord: Vec<usize>,    // [i]: 頂点 i の pre-order における順位
    low: Vec<usize>, /* [i]: 頂点 i から木辺を任意回、後退辺を高々１回辿って行ける頂点の pre-order の最小値 */
    parent: Vec<usize>, // [i]: 頂点 i が根なら i、さもなくの親頂点の番号
    built: bool,     // ビルド済みなら `true`
}
impl LowLink {
    /// 頂点数 $n$、辺なしの未ビルドグラフを構築する。
    ///
    /// # 例
    ///
    /// ```
    /// # use low_link::LowLink;
    /// let low_link = LowLink::new(4);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            g: vec![Vec::new(); n],
            ..Default::default()
        }
    }

    /// 未ビルドのグラフに無向辺 $\{i, j\}$ を追加する。
    ///
    /// # 例
    ///
    /// ```
    /// # use low_link::LowLink;
    /// let mut low_link = LowLink::new(4);
    /// low_link.add_edge(0, 3);
    /// low_link.add_edge(0, 2);
    /// ```
    pub fn add_edge(&mut self, i: usize, j: usize) {
        assert!(!self.built);
        self.g[i].push(j);
        self.g[j].push(i);
    }

    /// グラフをビルドし、各種クエリに答えられるようにする。
    ///
    /// DFS で各頂点に pre-order 番号 $\mathrm{ord}(v)$ を振り、木辺を任意回・後退辺を
    /// 高々 1 回辿って到達できる頂点の $\mathrm{ord}$ の最小値 $\mathrm{low}(v)$ を
    /// 帰りがけ順に計算する。連結成分ごとに最初に訪れた頂点が、その成分の DFS 木の根になる。
    ///
    /// # 計算量
    ///
    /// $O(n + m)$（$n$: 頂点数、$m$: 辺数）
    ///
    /// # 例
    ///
    /// ```
    /// # use low_link::LowLink;
    /// let mut low_link = LowLink::new(4);
    /// low_link.add_edge(0, 3);
    /// low_link.add_edge(0, 2);
    /// low_link.build();
    /// ```
    pub fn build(&mut self) {
        assert!(!self.built);
        self.built = true;
        let n = self.g.len();
        self.ord.resize(n, !0);
        self.parent.resize(n, !0);

        // Pre-order (`sorted`, `ord`), `parent` の計算
        let mut used = vec![false; n];
        for i in 0..n {
            if !used[i] {
                self.parent[i] = i;
                used[i] = true;
                build(
                    i,
                    i,
                    &mut self.g,
                    &mut self.parent,
                    &mut self.sorted,
                    &mut self.ord,
                    &mut used,
                );
            }
        }

        // Low-link (`low`) の計算
        self.low = self.ord.clone();
        for &x in self.sorted.iter().rev() {
            for &y in &self.g[x] {
                self.low[x] = self.low[x].min(if self.ord[x] < self.ord[y] {
                    self.low[y]
                } else {
                    self.ord[y]
                });
            }
        }
    }

    /// 頂点 `x` が関節点（取り除くとグラフが非連結になる頂点）なら `true` を返す。
    ///
    /// 根なら子が 2 つ以上あるとき、根でなければある子 $y$ が
    /// $\mathrm{ord}(x) \le \mathrm{low}(y)$ を満たすとき関節点となる。
    ///
    /// # 計算量
    ///
    /// $O(\deg x)$
    ///
    /// # 例
    ///
    /// ```
    /// # use low_link::LowLink;
    /// let mut low_link = LowLink::new(4);
    /// low_link.add_edge(0, 1);
    /// low_link.add_edge(0, 2);
    /// low_link.add_edge(1, 2);
    /// low_link.add_edge(2, 3);
    /// low_link.build();
    ///
    /// assert_eq!(low_link.is_articulation_point(0), false);
    /// assert_eq!(low_link.is_articulation_point(2), true);
    /// ```
    pub fn is_articulation_point(&self, x: usize) -> bool {
        assert!(self.built);
        if self.parent[x] == x {
            1 < self.g[x].len()
        } else {
            self.g[x]
                .iter()
                .any(|&y| self.ord[x] < self.ord[y] && self.ord[x] <= self.low[y])
        }
    }

    /// 頂点 `x`, `y` を結ぶ辺が橋（取り除くとグラフが非連結になる辺）なら `true` を返す。
    ///
    /// 辺 $\{x, y\}$ が存在しない場合の戻り値は未定義。DFS 木で `x`, `y` のうち
    /// 子側を $c$、親側を $p$ とすると、$\mathrm{ord}(p) < \mathrm{low}(c)$ が橋の条件
    /// （等号だと $c$ の部分木から $p$ 自身へ戻る後退辺がある）。
    ///
    /// # 計算量
    ///
    /// $O(1)$
    ///
    /// # 例
    ///
    /// ```
    /// # use low_link::LowLink;
    /// let mut low_link = LowLink::new(4);
    /// low_link.add_edge(0, 1);
    /// low_link.add_edge(0, 2);
    /// low_link.add_edge(1, 2);
    /// low_link.add_edge(2, 3);
    /// low_link.build();
    ///
    /// assert_eq!(low_link.is_bridge_unchecked(0, 1), false);
    /// assert_eq!(low_link.is_bridge_unchecked(2, 3), true);
    /// ```
    pub fn is_bridge_unchecked(&self, mut x: usize, mut y: usize) -> bool {
        assert!(self.built);
        if self.ord[x] > self.ord[y] {
            swap(&mut x, &mut y);
        }
        self.parent[y] == x && self.ord[x] < self.low[y]
    }

    /// 2-連結成分分解をし、各成分に属する辺のリストのリストを返す。
    ///
    /// 2-連結成分とは、任意の 2 頂点間に関節点を共有しない経路が存在する極大な部分グラフ。
    /// DFS の帰りがけ順に辺をスタックへ積み、関節点の条件
    /// $\mathrm{ord}(x) \le \mathrm{low}(y)$ が成り立つたびに、スタックの該当区間を
    /// 1 つの成分として取り出す。
    ///
    /// # 計算量
    ///
    /// $O(n + m)$（$n$: 頂点数、$m$: 辺数）
    ///
    /// # 例
    ///
    /// ```
    /// # use low_link::LowLink;
    /// let mut low_link = LowLink::new(4);
    /// low_link.add_edge(0, 1);
    /// low_link.add_edge(0, 2);
    /// low_link.add_edge(1, 2);
    /// low_link.add_edge(2, 3);
    /// low_link.build();
    ///
    /// let mut result = low_link.biconnected_components();
    /// result.iter_mut().flatten().for_each(|v| v.sort());
    /// result.iter_mut().for_each(|v| v.sort());
    /// result.sort();
    /// let expected = vec![vec![[0, 1], [0, 2], [1, 2]], vec![[2, 3]]];
    /// assert_eq!(result, expected);
    /// ```
    pub fn biconnected_components(&self) -> Vec<Vec<[usize; 2]>> {
        assert!(self.built);
        let n = self.g.len();
        let mut stack = Vec::new();
        let mut cmp = Vec::new();
        for i in (0..n).filter(|&i| self.parent[i] == i) {
            self.__biconnected_components_dfs(i, &mut stack, &mut cmp);
        }
        cmp
    }

    fn __biconnected_components_dfs(
        &self,
        x: usize,
        stack: &mut Vec<[usize; 2]>,
        cmp: &mut Vec<Vec<[usize; 2]>>,
    ) {
        for &y in &self.g[x] {
            stack.push([x, y]);
            if self.ord[x] < self.ord[y] {
                self.__biconnected_components_dfs(y, stack, cmp);
                if self.ord[x] <= self.low[y] {
                    let mut c = Vec::new();
                    while let Some([u, v]) = stack.pop() {
                        c.push([u, v]);
                        if [u, v] == [x, y] {
                            break;
                        }
                    }
                    cmp.push(c);
                }
            }
        }
    }

    /// 2-辺連結成分分解をし、各成分に属する頂点のリストのリストを返す。
    ///
    /// 2-辺連結成分とは、グラフから橋をすべて取り除いた後にできる各連結成分のこと。
    /// DFS の帰りがけ順に頂点をスタックへ積み、橋の条件 $\mathrm{ord}(x) < \mathrm{low}(y)$
    /// が成り立つたびに、スタックの該当区間を 1 つの成分として取り出す。
    ///
    /// # 計算量
    ///
    /// $O(n + m)$（$n$: 頂点数、$m$: 辺数）
    ///
    /// # 例
    ///
    /// ```
    /// # use low_link::LowLink;
    /// let mut low_link = LowLink::new(4);
    /// low_link.add_edge(0, 1);
    /// low_link.add_edge(0, 2);
    /// low_link.add_edge(1, 2);
    /// low_link.add_edge(2, 3);
    /// low_link.build();
    ///
    /// let mut result = low_link.two_edge_components();
    /// result.iter_mut().for_each(|v| v.sort());
    /// result.sort();
    /// let expected = vec![vec![0, 1, 2], vec![3]];
    /// assert_eq!(result, expected);
    /// ```
    pub fn two_edge_components(&self) -> Vec<Vec<usize>> {
        assert!(self.built);
        let n = self.g.len();
        let mut stack = Vec::new();
        let mut cmp = Vec::new();
        for i in (0..n).filter(|&i| self.parent[i] == i) {
            self.__two_edge_components_dfs(i, &mut stack, &mut cmp);
            cmp.push(take(&mut stack));
        }
        cmp
    }

    fn __two_edge_components_dfs(
        &self,
        x: usize,
        stack: &mut Vec<usize>,
        cmp: &mut Vec<Vec<usize>>,
    ) {
        stack.push(x);
        for &y in &self.g[x] {
            if self.ord[x] < self.ord[y] {
                self.__two_edge_components_dfs(y, stack, cmp);
                if self.ord[x] < self.low[y] {
                    let mut c = Vec::new();
                    while let Some(z) = stack.pop() {
                        c.push(z);
                        if z == y {
                            break;
                        }
                    }
                    cmp.push(c);
                }
            }
        }
    }
}

fn build(
    x: usize,
    p: usize,
    g: &mut [Vec<usize>],
    parent: &mut [usize],
    sorted: &mut Vec<usize>,
    ord: &mut [usize],
    used: &mut [bool],
) {
    ord[x] = sorted.len();
    sorted.push(x);
    let mut i = 0;
    while i < g[x].len() {
        let y = g[x][i];
        if y == p {
            g[x].swap_remove(i);
            continue;
        } else if replace(&mut used[y], true) {
            if ord[x] < ord[y] {
                g[x].swap_remove(i);
                continue;
            }
        } else {
            parent[y] = x;
            build(y, x, g, parent, sorted, ord, used);
        }
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::LowLink;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::HashSet;
    use std::mem::replace;
    use std::mem::take;

    #[test]
    fn test_low_link() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(2..=8);
            let m = rng.gen_range(1..=13.min(n * (n - 1) / 2));
            let mut edges = HashSet::new();
            while edges.len() < m {
                let u = rng.gen_range(0..n);
                let v = rng.gen_range(0..n);
                if u < v {
                    edges.insert([u, v]);
                }
            }
            let edges = edges.into_iter().collect::<Vec<_>>();

            let g = make_graph(n, &edges);
            let mut low_link = LowLink::new(n);
            for &[u, v] in &edges {
                low_link.add_edge(u, v);
            }
            low_link.build();

            // 関節点
            for i in 0..n {
                let result = low_link.is_articulation_point(i);
                let expected = is_articulation_point(i, &g);
                assert_eq!(result, expected);
            }

            // 橋
            for [u, v] in edges.iter().flat_map(|&[u, v]| vec![[u, v], [v, u]]) {
                let result = low_link.is_bridge_unchecked(u, v);
                let expected = is_bridge(u, v, &g);
                assert_eq!(result, expected);
            }

            // 2-連結成分分解
            {
                let mut result = low_link.biconnected_components();
                let mut expected = biconnected_components(n, &edges);
                result.iter_mut().flatten().for_each(|v| v.sort_unstable());
                expected
                    .iter_mut()
                    .flatten()
                    .for_each(|v| v.sort_unstable());
                for v in &mut result {
                    v.sort_unstable();
                }
                for v in &mut expected {
                    v.sort_unstable();
                }
                result.sort();
                expected.sort();
                assert_eq!(&result, &expected);
            }

            // 2-辺連結成分分解
            {
                let mut result = low_link.two_edge_components();
                let mut expected = two_edge_components(n, &edges);
                for v in &mut result {
                    v.sort_unstable();
                }
                for v in &mut expected {
                    v.sort_unstable();
                }
                result.sort();
                expected.sort();
                assert_eq!(&result, &expected);
            }
        }
    }

    fn make_graph(n: usize, edges: &[[usize; 2]]) -> Vec<Vec<usize>> {
        let mut g = vec![Vec::new(); n];
        for &[u, v] in edges {
            g[u].push(v);
            g[v].push(u);
        }
        g
    }

    fn two_edge_components(n: usize, edges: &[[usize; 2]]) -> Vec<Vec<usize>> {
        let mut ideal = HashSet::new();
        let mut ans = Vec::new();
        for bs in (0..1 << n).rev() {
            if !ideal.contains(&bs) && is_two_edge_connected(bs, n, edges) {
                ans.push((0..n).filter(|&i| bs >> i & 1 == 1).collect());
                ideal.insert(bs);
                let mut cs = bs;
                while cs != 0 {
                    cs = (cs - 1) & bs;
                    ideal.insert(cs);
                }
            }
        }
        ans
    }

    fn is_two_edge_connected(bs: u32, n: usize, edges: &[[usize; 2]]) -> bool {
        let edges = edges
            .iter()
            .copied()
            .filter(|&[u, v]| bs >> u & 1 == 1 && bs >> v & 1 == 1)
            .collect::<Vec<_>>();
        if edges.is_empty() {
            return bs.count_ones() <= 1;
        }
        let g = make_graph(n, &edges);

        let start = edges[0][0];
        let mut used = vec![false; n];
        let mut stack = vec![start];
        used[start] = true;
        while let Some(x) = stack.pop() {
            for &y in &g[x] {
                if !replace(&mut used[y], true) {
                    stack.push(y);
                }
            }
        }
        (0..n).all(|x| bs >> x & 1 == 0 || used[x])
            && edges.iter().all(|&[x, y]| !is_bridge(x, y, &g))
    }

    fn biconnected_components(n: usize, edges: &[[usize; 2]]) -> Vec<Vec<[usize; 2]>> {
        let m = edges.len();
        let mut ideal = HashSet::new();
        let mut ans = Vec::new();
        for bs in (0..1 << m).rev() {
            if !ideal.contains(&bs) && is_binonnected(bs, n, edges) {
                ans.push(
                    (0..m)
                        .filter(|&j| bs >> j & 1 == 1)
                        .map(|j| edges[j])
                        .collect(),
                );
                ideal.insert(bs);
                let mut cs = bs;
                while cs != 0 {
                    cs = (cs - 1) & bs;
                    ideal.insert(cs);
                }
            }
        }
        ans
    }

    fn is_binonnected(bs: u32, n: usize, edges: &[[usize; 2]]) -> bool {
        if bs == 0 {
            return true;
        }
        let edges = edges
            .iter()
            .enumerate()
            .filter(|&(i, _)| bs >> i & 1 == 1)
            .map(|(_, &e)| e)
            .collect::<Vec<_>>();
        let g = make_graph(n, &edges);

        let start = edges[0][0];
        let mut used = vec![false; n];
        let mut stack = vec![start];
        used[start] = true;
        while let Some(x) = stack.pop() {
            for &y in &g[x] {
                if !replace(&mut used[y], true) {
                    stack.push(y);
                }
            }
        }
        edges.iter().all(|&[x, y]| used[x] && used[y])
            && (0..n).all(|x| !is_articulation_point(x, &g))
    }

    fn is_bridge(x: usize, y: usize, g: &[Vec<usize>]) -> bool {
        let orig_count = count_connected_components(g);
        let mut g = g.to_vec();
        let i = g[x].iter().position(|&z| z == y).unwrap();
        g[x].remove(i);
        let j = g[y].iter().position(|&z| z == x).unwrap();
        g[y].remove(j);
        let new_count = count_connected_components(&g);
        orig_count < new_count
    }

    fn is_articulation_point(x: usize, g: &[Vec<usize>]) -> bool {
        let orig_count = count_connected_components(g);
        let mut g = g.to_vec();
        let gx = take(&mut g[x]);
        for y in gx {
            let i = g[y].iter().position(|&z| z == x).unwrap();
            g[y].remove(i);
        }
        let new_count = count_connected_components(&g);
        orig_count + 1 < new_count
    }

    fn count_connected_components(g: &[Vec<usize>]) -> usize {
        let n = g.len();
        let mut stack = Vec::new();
        let mut used = vec![false; n];
        let mut count = 0;
        for i in 0..n {
            if !replace(&mut used[i], true) {
                count += 1;
                stack.push(i);
                while let Some(x) = stack.pop() {
                    for &y in &g[x] {
                        if !replace(&mut used[y], true) {
                            stack.push(y);
                        }
                    }
                }
            }
        }
        count
    }
}
