//!
//! # このライブラリを使える問題
//!
//! - AOJ GRL_3_C - 強連結成分分解
//!   - 問題: <https://onlinejudge.u-aizu.ac.jp/problems/GRL_3_C>
//!   - 提出 (8 ms):
//!   <https://onlinejudge.u-aizu.ac.jp/status/users/ngtkana/submissions/1/GRL_3_C/judge/6179065/Rust>
//!   - 出題日: 2016-09-04
//!   - 難易度: 易しめ。
//!   - 制約:
//!     - N ≤ 10,000
//!     - M ≤ 30,000
//!     - Q ≤ 100,000
use std::collections::HashSet;
use std::mem::replace;

/// 本体です。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct Scc {
    g: Vec<Vec<usize>>,
    rg: Vec<Vec<usize>>,
    ord: Vec<usize>,    // トポロジカル順序に従って頂点番号が入ります。
    cmp_of: Vec<usize>, // 各頂点の属する強連結成分番号が入ります
    cmp_count: usize,   // 強連結成分の総数が入ります。
    built: bool,
}
impl Scc {
    /// 管理しているグラフが空グラフならば、`true` を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let scc = Scc::new(0);
    /// assert!(scc.is_empty());
    ///
    /// let scc = Scc::new(1);
    /// assert!(!scc.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.g.is_empty()
    }

    /// 管理しているグラフの頂点数を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let scc = Scc::new(0);
    /// assert_eq!(scc.len(), 0);
    ///
    /// let scc = Scc::new(1);
    /// assert_eq!(scc.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.g.len()
    }

    /// 頂点数 `n` の辺のない未ビルドのグラフを構築します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let scc = Scc::new(42);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            g: vec![Vec::new(); n],
            rg: vec![Vec::new(); n],
            ord: Vec::new(),
            cmp_of: Vec::new(),
            cmp_count: 0,
            built: false,
        }
    }

    /// 【Require: 未ビルド】
    /// 辺 (from, to) を追加します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(42);
    /// scc.add_edge(13, 18);
    /// scc.add_edge(13, 6);
    /// assert_eq!(&scc.g()[13], &[18, 6]);
    /// assert_eq!(&scc.g()[6], &[]);
    /// ```
    pub fn add_edge(&mut self, from: usize, to: usize) {
        assert!(!self.built);
        self.g[from].push(to);
        self.rg[to].push(from);
    }

    /// 正向きのグラフの隣接リストを返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(42);
    /// scc.add_edge(13, 18);
    /// scc.add_edge(13, 6);
    /// assert_eq!(&scc.g()[13], &[18, 6]);
    /// assert_eq!(&scc.g()[6], &[]);
    /// ```
    pub fn g(&self) -> &[Vec<usize>] {
        &self.g
    }

    /// 逆向きのグラフの隣接リストを返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(42);
    /// scc.add_edge(13, 18);
    /// scc.add_edge(13, 6);
    /// assert_eq!(&scc.rg()[13], &[]);
    /// assert_eq!(&scc.rg()[6], &[13]);
    /// ```
    pub fn rg(&self) -> &[Vec<usize>] {
        &self.rg
    }

    /// 【Require: ビルド済み】
    /// 商グラフにおけるトポロジカル順序に従って頂点番号の入ったスライスを返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(6);
    /// scc.add_edge(2, 0);
    /// scc.add_edge(1, 0);
    /// scc.add_edge(3, 4);
    /// scc.add_edge(4, 5);
    /// scc.add_edge(5, 4);
    /// scc.build();
    /// assert_eq!(&scc.ord(), &[3, 4, 5, 2, 1, 0]);
    /// ```
    pub fn ord(&self) -> &[usize] {
        assert!(self.built);
        &self.ord
    }

    /// 【Require: ビルド済み】
    /// 強連結成分の個数を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(6);
    /// scc.add_edge(2, 0);
    /// scc.add_edge(1, 0);
    /// scc.add_edge(3, 4);
    /// scc.add_edge(4, 5);
    /// scc.add_edge(5, 4);
    /// scc.build();
    /// assert_eq!(scc.cmp_count(), 5);
    /// ```
    pub fn cmp_count(&self) -> usize {
        assert!(self.built);
        self.cmp_count
    }

    /// 【Require: ビルド済み】
    /// 頂点 `x` の属する強連結成分の番号を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(6);
    /// scc.add_edge(2, 0);
    /// scc.add_edge(1, 0);
    /// scc.add_edge(3, 4);
    /// scc.add_edge(4, 5);
    /// scc.add_edge(5, 4);
    /// scc.build();
    /// assert_eq!(scc.cmp_of(0), 4);
    /// assert_eq!(scc.cmp_of(1), 3);
    /// ```
    pub fn cmp_of(&self, x: usize) -> usize {
        assert!(self.built);
        self.cmp_of[x]
    }

    /// 【Require: ビルド済み】
    /// 頂点番号から、その属する強連結成分の番号を検索できる
    /// スライスを返します。
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(6);
    /// scc.add_edge(2, 0);
    /// scc.add_edge(1, 0);
    /// scc.add_edge(3, 4);
    /// scc.add_edge(4, 5);
    /// scc.add_edge(5, 4);
    /// scc.build();
    /// assert_eq!(scc.cmp_of(0), 4);
    /// assert_eq!(scc.cmp_of(1), 3);
    /// ```
    pub fn cmp_ofs(&self) -> &[usize] {
        assert!(self.built);
        &self.cmp_of
    }

    /// 【Require: ビルド済み】
    /// 辺の重複と自己辺を除いた商グラフを構築して返します。
    ///
    /// # 計算量
    ///
    /// O(N)
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(6);
    /// scc.add_edge(2, 0);
    /// scc.add_edge(1, 0);
    /// scc.add_edge(3, 4);
    /// scc.add_edge(4, 5);
    /// scc.add_edge(5, 4);
    /// scc.build();
    ///
    /// let g = scc.quotient_graph();
    /// let expected = vec![vec![1], vec![], vec![4], vec![4], vec![]];
    /// assert_eq!(g, expected);
    /// ```
    pub fn quotient_graph(&self) -> Vec<Vec<usize>> {
        assert!(self.built);
        let mut ans = vec![Vec::new(); self.cmp_count];
        let mut used = HashSet::new();
        for x in 0..self.len() {
            for &y in &self.g[x] {
                let x = self.cmp_of[x];
                let y = self.cmp_of[y];
                if x != y && used.insert((x, y)) {
                    ans[x].push(y);
                }
            }
        }
        ans
    }

    /// 【Require: ビルド済み】
    /// 各強連結成分に属する頂点全体の集合を、[`Self::ord()`]  と同じ
    /// トポロジカル順序順序で返します。
    ///
    /// # 計算量
    ///
    /// O(N)
    ///
    /// # Example
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(6);
    /// scc.add_edge(2, 0);
    /// scc.add_edge(1, 0);
    /// scc.add_edge(3, 4);
    /// scc.add_edge(4, 5);
    /// scc.add_edge(5, 4);
    /// scc.build();
    ///
    /// let g = scc.quotient_set();
    /// let expected = vec![vec![3], vec![4, 5], vec![2], vec![1], vec![0]];
    /// assert_eq!(g, expected);
    /// ```
    pub fn quotient_set(&self) -> Vec<Vec<usize>> {
        assert!(self.built);
        let mut ans = vec![Vec::new(); self.cmp_count];
        for &x in &self.ord {
            ans[self.cmp_of(x)].push(x);
        }
        ans
    }

    /// 【Require: 未ビルド】
    /// ビルドします。
    ///
    /// # Examples
    ///
    /// ```
    /// use scc::Scc;
    ///
    /// let mut scc = Scc::new(6);
    /// scc.add_edge(2, 0);
    /// scc.add_edge(1, 0);
    /// scc.add_edge(3, 4);
    /// scc.add_edge(4, 5);
    /// scc.add_edge(5, 4);
    /// scc.build();
    /// ```
    pub fn build(&mut self) {
        assert!(!self.built);
        self.built = true;
        let mut cmp_of = vec![0; self.len()];
        let mut ord = Vec::new();
        (0..self.len()).for_each(|i| self.dfs1(i, &mut cmp_of, &mut ord));
        ord.reverse();
        for &i in &ord {
            if cmp_of[i] == !0 {
                self.dfs2(i, &mut cmp_of);
                self.cmp_count += 1;
            }
        }
        self.cmp_of = cmp_of;
        self.ord = ord;
    }

    fn dfs1(&self, x: usize, cmp_of: &mut [usize], ord: &mut Vec<usize>) {
        if replace(&mut cmp_of[x], !0) == 0 {
            self.g[x].iter().for_each(|&y| self.dfs1(y, cmp_of, ord));
            ord.push(x);
        }
    }

    fn dfs2(&self, x: usize, cmp_of: &mut [usize]) {
        cmp_of[x] = self.cmp_count;
        for &y in &self.rg[x] {
            if cmp_of[y] == !0 {
                self.dfs2(y, cmp_of);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[test]
    fn test_scc() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..20);
            let m = rng.gen_range(0..20);
            let mut g = vec![vec![false; n]; n];
            (0..n).for_each(|i| g[i][i] = true);
            let mut scc = Scc::new(n);
            for _ in 0..m {
                let u = rng.gen_range(0..n);
                let v = rng.gen_range(0..n);
                g[u][v] = true;
                scc.add_edge(u, v);
            }
            scc.build();
            for k in 0..n {
                for i in 0..n {
                    for j in 0..n {
                        g[i][j] |= g[i][k] && g[k][j];
                    }
                }
            }

            // equiv クエリ
            for i in 0..n {
                for j in 0..n {
                    let result = scc.cmp_of(i) == scc.cmp_of(j);
                    let expected = g[i][j] && g[j][i];
                    assert_eq!(result, expected);
                }
            }
            // その他整合性
            let qset = scc.quotient_set();
            assert_eq!(qset.iter().map(std::vec::Vec::len).sum::<usize>(), n);
            assert_eq!(qset.len(), scc.cmp_count());
            let mut used = vec![false; n];
            for (i, qset) in qset.iter().enumerate() {
                assert!(!qset.is_empty());
                for &j in qset {
                    assert_eq!(scc.cmp_of(j), i);
                    assert!(!used[j]);
                    used[j] = true;
                }
            }
            for (i, &j) in scc.cmp_ofs().iter().enumerate() {
                assert_eq!(j, scc.cmp_of(i));
            }
        }
    }
}
