//! 強連結成分分解をします。
//!
//! [厳密な出力要件は、`scc_flatgraph` をご覧ください。](scc_flatgraph)
//!
//! # Functions
//!
//! | お名前            | 入力グラフ表現    |
//! | -                 | -                 |
//! | [`scc_iterator`]  | 辺イテレータ      |
//! | [`scc_adjlist`]   | 隣接リスト表現    |
//! | [`scc_flatgraph`] | フラットグラフ    |
//!
//!
//! # Examples
//!
//! ```
//! # use scc::scc_adjlist;
//! let g = vec![
//!     vec![1],
//!     vec![2],
//!     vec![0, 3],
//!     vec![4],
//!     vec![5],
//!     vec![3],
//! ];
//! let result = scc_adjlist(&g);
//! assert_eq!(result.cmp_of, vec![0, 0, 0, 1, 1, 1]);
//! ```
//!
use std::{fmt::Debug, mem::replace, ops::Index};

/// 強連結成分をする関数 − 隣接リスト版
///
/// [厳密な出力要件は、`scc_flatgraph` をご覧ください。](scc_flatgraph)
///
/// # 実装の特徴
///
/// フラットグラフに変換して [`scc_flatgraph`] を呼び出しています。
///
pub fn scc_adjlist(g: &[Vec<usize>]) -> SccResult {
    scc_iterator(
        g.len(),
        g.iter()
            .enumerate()
            .flat_map(|(i, v)| v.iter().map(move |&j| [i, j])),
    )
}

/// 強連結成分をする関数 − 辺イテレータ版
///
/// # 実装の特徴
///
/// フラットグラフに変換して [`scc_flatgraph`] を呼び出しています。
///
pub fn scc_iterator(n: usize, iter: impl IntoIterator<Item = [usize; 2]>) -> SccResult {
    scc_flatgraph(n, &mut iter.into_iter().collect::<Vec<_>>())
}

/// 強連結成分をする関数 − フラットグラフ版
///
///
/// # 実装の特徴
///
/// 隣接リストを二次元 `Vec<Vec<usize>>` で構築せず、不安定計数ソートにより代用します。
/// これにより動的メモリ確保の回数を抑えるとともに、逆グラフでも同じ配列を
/// （ソートし直すことで）使い回すことができます。
///
///
/// # 出力要件
///
/// * `cmp_count` は強連結成分の個数
/// * `cmp_of` の要素は `0..cmp_count`
/// * `cmp_of[i] == cmp_of[j]` は、`i` と `j` が同じ強連結成分に入っていることと同値
/// * `i` から `j` へ到達可能ならば、`cmp_of[i] <= cmp_of[j]` （i.e.
/// 強連結成分はトポロジカルソートされています。）
///
pub fn scc_flatgraph(n: usize, edges: &mut [[usize; 2]]) -> SccResult {
    let start = counting_sort_by_key_unstable(edges, n, |&[u, _]| u);
    let mut post_order = Vec::new();
    let mut used = vec![false; n];
    (0..n).for_each(|x| dfs_post_order(x, edges, &start, &mut used, &mut post_order));

    let start = counting_sort_by_key_unstable(edges, n, |&[_, v]| v);
    let mut cmp_of = vec![!0; n];
    let mut cmp_count = 0;
    for &x in post_order.iter().rev() {
        if cmp_of[x] == !0 {
            dfs_sort(x, edges, &start, &mut cmp_of, cmp_count);
            cmp_count += 1;
        }
    }
    SccResult { cmp_of, cmp_count }
}

fn dfs_post_order(
    x: usize,
    edges: &[[usize; 2]],
    start: &[usize],
    used: &mut [bool],
    post_order: &mut Vec<usize>,
) {
    if !replace(&mut used[x], true) {
        edges[start[x]..start[x + 1]]
            .iter()
            .for_each(|&[_, y]| dfs_post_order(y, edges, start, used, post_order));
        post_order.push(x);
    }
}

fn dfs_sort(
    x: usize,
    edges: &[[usize; 2]],
    start: &[usize],
    cmp_of: &mut [usize],
    cmp_count: usize,
) {
    if cmp_of[x] == !0 {
        cmp_of[x] = cmp_count;
        edges[start[x]..start[x + 1]]
            .iter()
            .for_each(|&[y, _]| dfs_sort(y, edges, start, cmp_of, cmp_count))
    }
}

fn counting_sort_by_key_unstable<T>(a: &mut [T], k: usize, f: impl Fn(&T) -> usize) -> Vec<usize> {
    let mut end = vec![0; k];
    a.iter().map(|ai| f(ai)).for_each(|key| end[key] += 1);
    (0..k).skip(1).for_each(|i| end[i] += end[i - 1]);
    let mut start = end.clone();
    start.rotate_right(1);
    start[0] = 0;
    for i in 0..k {
        while start[i] != end[i] {
            let j = f(&a[start[i]]);
            if i == j {
                start[i] += 1;
            } else {
                while f(&a[start[j]]) == j {
                    start[j] += 1;
                }
                a.swap(start[i], start[j]);
            }
        }
    }
    start.insert(0, 0);
    start
}

/// 強連結成分分解情報を保持します。
///
/// [厳密な仕様は、`scc_flatgraph` をご覧ください。](scc_flatgraph)
///
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct SccResult {
    /// 各頂点の属する強連結成分番号です。
    pub cmp_of: Vec<usize>,
    /// 強連結成分の個数です。
    pub cmp_count: usize,
}
impl SccResult {
    /// 各強連結成分について、そこに属する頂点全体の昇順の列を返します。
    pub fn to_vec2(&self) -> Vec<Vec<usize>> {
        let mut res = vec![Vec::new(); self.cmp_count];
        self.cmp_of
            .iter()
            .enumerate()
            .for_each(|(i, &c)| res[c].push(i));
        res
    }
    /// 各強連結成分について、そこに属する頂点全体の**順不同の**列を与えるような [`FlatVec`] を返します。
    ///
    /// # 順不同な理由
    ///
    /// 内部で不安定計数ソートをしているためです。
    ///
    pub fn to_flatvec(&self) -> FlatVec {
        let mut vec = (0..self.cmp_of.len()).collect::<Vec<_>>();
        let start = counting_sort_by_key_unstable(&mut vec, self.cmp_count, |&x| self.cmp_of[x]);
        FlatVec { vec, start }
    }
}

/// 二次元配列を 2 本の [`Vec`] で管理する構造体です。[`SccResult::to_flatvec`] の戻り値に使います。
#[derive(Clone, Default, Hash, PartialEq)]
pub struct FlatVec {
    pub vec: Vec<usize>,
    pub start: Vec<usize>,
}
impl Index<usize> for FlatVec {
    type Output = [usize];
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index + 1 < self.start.len());
        &self.vec[self.start[index]..self.start[index + 1]]
    }
}
impl Debug for FlatVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.start.windows(2).map(|v| &self.vec[v[0]..v[1]]))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{scc_adjlist, scc_flatgraph, scc_iterator, SccResult},
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::{collections::HashSet, iter::repeat_with},
    };

    #[test]
    fn test_scc_iterator() {
        let mut rng = StdRng::seed_from_u64(42);
        combine(
            10, // 実装は `scc_flatgraph` を呼ぶだけなので、テスト弱めで
            &mut rng,
            test_case_random,
            |n, edges| scc_iterator(n, edges.to_vec()),
            validate,
        );
    }

    #[test]
    fn test_scc_adjlist() {
        let mut rng = StdRng::seed_from_u64(42);
        combine(
            10, // 実装は `scc_flatgraph` を呼ぶだけなので、テスト弱めで
            &mut rng,
            test_case_random,
            |n, edges| {
                let mut g = vec![Vec::new(); n];
                edges.iter().for_each(|&[u, v]| g[u].push(v));
                scc_adjlist(&g)
            },
            validate,
        );
    }

    #[test]
    fn test_scc_flatgraph() {
        let mut rng = StdRng::seed_from_u64(42);
        combine(200, &mut rng, test_case_random, scc_flatgraph, validate);
    }

    fn combine(
        repeat: usize,
        rng: &mut StdRng,
        test_case: impl Fn(&mut StdRng) -> (usize, Vec<[usize; 2]>),
        solve: impl Fn(usize, &mut [[usize; 2]]) -> SccResult,
        validate: impl Fn(usize, &[[usize; 2]], &SccResult),
    ) {
        for _ in 0..repeat {
            let (n, mut edges) = test_case(rng);
            let result = solve(n, &mut edges);
            validate(n, &edges, &result);
        }
    }

    /// # テストケース
    ///
    /// 自己辺・多重辺のあるかもしれない有効グラフです。
    /// 頂点の個数が [2, 30] で一様ランダム
    /// 辺の本数が [1, N²[ で対数的一様ランダム、
    /// それぞれの辺は独立に N² 通り一様ランダムな頂点をつなぎます。
    fn test_case_random(rng: &mut StdRng) -> (usize, Vec<[usize; 2]>) {
        let n = rng.gen_range(2..=30);
        let m = rng.gen_range(0_f64..2.0 * (n as f64).ln()).exp().floor() as usize;
        let edges = repeat_with(|| [rng.gen_range(0..n), rng.gen_range(0..n)])
            .take(m)
            .collect::<Vec<_>>();
        (n, edges)
    }

    /// # テスト実装
    ///
    /// Floyed−Warshall と比較します。
    ///
    ///
    /// # 計算量
    ///
    /// O ( N ³)
    ///
    fn validate(n: usize, edges: &[[usize; 2]], result: &SccResult) {
        // Floyed−Warshall
        let mut adj = vec![vec![false; n]; n];
        (0..n).for_each(|i| adj[i][i] = true);
        edges.iter().for_each(|&[u, v]| adj[u][v] = true);
        for k in 0..n {
            for i in 0..n {
                for j in 0..n {
                    adj[i][j] |= adj[i][k] && adj[k][j];
                }
            }
        }

        // Validate cmp_of
        for i in 0..n {
            for j in 0..n {
                assert_eq!(result.cmp_of[i] == result.cmp_of[j], adj[i][j] && adj[j][i]);
                if adj[i][j] {
                    assert!(result.cmp_of[i] <= result.cmp_of[j]);
                }
            }
        }

        // Validate cmp_count
        assert!((0..result.cmp_count).all(|i| result.cmp_of.iter().any(|&c| c == i)));
        assert!(result.cmp_of.iter().all(|&c| c < result.cmp_count));

        // Validate to_vec2
        let result_vec2 = result.to_vec2();
        let mut used = vec![false; n];
        result_vec2.iter().flatten().for_each(|&x| used[x] = true);
        assert!(used.iter().all(|&c| c));
        assert_eq!(result_vec2.iter().map(|v| v.len()).sum::<usize>(), n);
        assert_eq!(result_vec2.len(), result.cmp_count);
        assert!(result_vec2
            .iter()
            .enumerate()
            .all(|(i, v)| v.iter().all(|&x| result.cmp_of[x] == i)));
        assert!(result_vec2
            .iter()
            .all(|v| v.windows(2).all(|v| v[0] < v[1])));

        // Validate to_flatvec
        let result_flatvec = result.to_flatvec();
        assert!(
            (0..result.cmp_count).all(|i| result_flatvec[i].iter().collect::<HashSet<_>>()
                == result_vec2[i].iter().collect::<HashSet<_>>())
        );
    }
}
