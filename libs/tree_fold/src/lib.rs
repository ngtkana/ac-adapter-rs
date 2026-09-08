//! 全方位木DP（rerooting）。各頂点を根としたときの集約値をまとめて計算する。
//!
//! 森を頂点集合 $V$、モノイド $(F, \mathrm{op}, \mathrm{identity})$ の要素とみなし、
//! 「頂点 $v$ をルートとして森 $F$ に接続し木にする」演算 $\mathrm{up}: F \times V \to F$ を追加で与える。
//! 通常の部分木DP（子の集約値を `op` で畳み込み `up` でルートに接続する）を根から葉・葉から根の
//! 両方向に行うことで、「頂点 $v$ を根とする部分木の集約値」だけでなく「$v$ の親側を含めた
//! 残り全体の集約値」も $O(n)$ 回の演算で求まる。`op` は可換でなくてよく、各頂点で子を
//! 元の順序で `op` した前後の累積（prefix/suffix）を使って「自分を除いた残り」を計算する。
//!
//! # 仕様
//!
//! [`Op`] トレイトで演算を定義する。
//!
//! - `Op::up`: $F \times V \to F$。森に頂点 $v$ をルートとして接続する
//! - `Op::op`: $F \times F \to F$。森どうしの結合（結合律を満たせばよく、可換律は不要）
//! - `Op::identity`: 空の森
//!
//! [`two_way_tree_fold`] は木（頂点数 $n$）を根から葉への有向グラフとして表す隣接リスト
//! `g: &[Vec<usize>]`（`g[i]` は $i$ の子）と、親が子より前に来るトポロジカル順 `sorted` を
//! 受け取り、[`TwoWayTreeFoldResult`] を返す。
//!
//! - `branch[i]`: 頂点 $i$ を根とする部分木の集約値
//! - `lower[i]`: 頂点 $i$ の子部分木をすべて `op` で結合した値（`branch[i] = up(lower[i], i)`）
//! - `upper[i]`: 頂点 $i$ を除いた残り全体を $i$ に接続した集約値。根では `identity`
//!
//! # 例
//!
//! ```
//! use tree_fold::Op;
//! use tree_fold::two_way_tree_fold;
//!
//! struct SubtreeSize;
//! impl Op for SubtreeSize {
//!     type Value = usize;
//!     fn up(&self, value: &usize, _root: usize) -> usize {
//!         value + 1
//!     }
//!     fn op(&self, lhs: &usize, rhs: &usize) -> usize {
//!         lhs + rhs
//!     }
//!     fn identity(&self) -> usize {
//!         0
//!     }
//! }
//!
//! // 木: 0 -> 1, 0 -> 2, 1 -> 3
//! let g = vec![vec![1, 2], vec![3], vec![], vec![]];
//! let sorted = vec![0, 1, 2, 3];
//! let result = two_way_tree_fold(&SubtreeSize, &g, &sorted);
//! assert_eq!(result.branch, vec![4, 2, 1, 1]); // 各頂点を根とする部分木のサイズ
//! assert_eq!(result.upper, vec![0, 2, 3, 3]); // 各頂点から見た残り全体のサイズ（根は 0）
//! ```
//!
//! # 計算量
//!
//! - `two_way_tree_fold`: $O(n)$ 回の `up`/`op` 呼び出し（$n$ は頂点数）

/// 全方位木DPの演算。モノイド $(F, \mathrm{op}, \mathrm{identity})$ と、
/// 頂点 $v$ をルートとして森 $F$ に接続する演算 $\mathrm{up}$ を定義する。
pub trait Op: Sized {
    /// モノイド $F$ の値の型。
    type Value: Clone;

    /// 森 `value` に頂点 `root` をルートとして接続する: $F \times V \to F$。
    fn up(&self, value: &Self::Value, root: usize) -> Self::Value;

    /// 森どうしを結合する: $F \times F \to F$（結合律を満たせばよく、可換律は不要）。
    fn op(&self, lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    /// 空の森を返す: $\mathrm{identity} \in F$。
    fn identity(&self) -> Self::Value;

    /// [`two_way_tree_fold`] を呼び出す。詳細はそちらを参照。
    fn two_way_tree_fold(
        &self,
        g: &[Vec<usize>],
        sorted: &[usize],
    ) -> TwoWayTreeFoldResult<Self::Value> {
        two_way_tree_fold(self, g, sorted)
    }
}

/// [`two_way_tree_fold`] の返り値。
pub struct TwoWayTreeFoldResult<T> {
    /// `upper[i]`: 頂点 $i$ を除いた残り全体を $i$ に接続した集約値。根では `identity`。
    pub upper: Vec<T>,
    /// `lower[i]`: 頂点 $i$ の子部分木をすべて `op` で結合した値。
    pub lower: Vec<T>,
    /// `branch[i]`: 頂点 $i$ を根とする部分木の集約値（`up(lower[i], i)`）。
    pub branch: Vec<T>,
}

/// 全方位木DPを行う。詳細はモジュールレベルドキュメントの `# 仕様` を参照。
pub fn two_way_tree_fold<O: Op>(
    o: &O,
    g: &[Vec<usize>],
    sorted: &[usize],
) -> TwoWayTreeFoldResult<O::Value> {
    let n = g.len();
    let mut lower = vec![o.identity(); n];
    let mut branch = vec![o.identity(); n];
    for &i in sorted.iter().rev() {
        for &j in &g[i] {
            lower[i] = o.op(&lower[i], &branch[j]);
        }
        branch[i] = o.up(&lower[i], i);
    }
    let mut upper = vec![o.identity(); n];
    for &i in sorted {
        let mut suffix = upper[i].clone();
        for &j in g[i].iter().rev() {
            upper[j] = suffix.clone();
            suffix = o.op(&branch[j], &suffix);
        }
        let mut prefix = o.identity();
        for &j in &g[i] {
            upper[j] = o.up(&o.op(&upper[j], &prefix), i);
            prefix = o.op(&prefix, &branch[j]);
        }
    }
    TwoWayTreeFoldResult {
        upper,
        lower,
        branch,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::BinaryHeap;

    struct GenratedTree {
        g: Vec<Vec<usize>>,
        sorted: Vec<usize>,
        parent: Vec<usize>,
    }

    fn gen_tree(rng: &mut StdRng, n: usize) -> GenratedTree {
        let mut g = vec![Vec::new(); n];
        let rev_prufer = (0..n - 1)
            .map(|i| if i == n - 2 { 0 } else { rng.gen_range(0..n) })
            .collect::<Vec<_>>();
        let mut count = vec![0; n];
        for &y in &rev_prufer {
            count[y] += 1;
        }
        let mut heap = (0..n).filter(|&y| count[y] == 0).collect::<BinaryHeap<_>>();
        for &y in &rev_prufer {
            let x = heap.pop().unwrap();
            g[x].push(y);
            g[y].push(x);
            count[y] -= 1;
            if count[y] == 0 {
                heap.push(y);
            }
        }
        let root = rng.gen_range(0..n);
        let mut stack = vec![root];
        let mut parent = vec![usize::MAX; n];
        let mut sorted = Vec::new();
        parent[root] = root;
        while let Some(i) = stack.pop() {
            sorted.push(i);
            g[i].retain(|&j| parent[i] != j);
            for &j in &g[i] {
                stack.push(j);
                parent[j] = i;
            }
        }
        GenratedTree { g, sorted, parent }
    }

    #[test]
    fn test_subtree() {
        struct O;
        #[derive(Clone, PartialEq)]
        struct Tree {
            root: usize,
            child: Vec<Self>,
        }
        impl std::fmt::Debug for Tree {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple("")
                    .field(&self.root)
                    .field(&self.child)
                    .finish()
            }
        }
        impl Op for O {
            type Value = Vec<Tree>;

            fn up(&self, value: &Self::Value, root: usize) -> Self::Value {
                vec![Tree {
                    root,
                    child: value.clone(),
                }]
            }

            fn identity(&self) -> Self::Value {
                Vec::new()
            }

            fn op(&self, lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                lhs.iter().cloned().chain(rhs.iter().cloned()).collect()
            }
        }

        fn subtree(i: usize, p: usize, g: &[Vec<usize>]) -> Tree {
            Tree {
                root: i,
                child: match g[i].iter().position(|&j| j == p) {
                    None => g[i].iter().map(|&j| subtree(j, i, g)).collect(),
                    Some(e) => g[i][e + 1..]
                        .iter()
                        .chain(&g[i][..e])
                        .map(|&j| subtree(j, i, g))
                        .collect(),
                },
            }
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=30);
            let GenratedTree {
                g, sorted, parent, ..
            } = gen_tree(&mut rng, n);
            let TwoWayTreeFoldResult {
                lower,
                branch,
                upper,
            } = O.two_way_tree_fold(&g, &sorted);
            let mut g1 = g.clone();
            for (i, &p) in parent.iter().enumerate() {
                if i != p {
                    g1[i].push(p);
                }
            }
            for (i, &p) in parent.iter().enumerate() {
                assert_eq!(
                    lower[i],
                    g[i].iter().map(|&j| subtree(j, i, &g)).collect::<Vec<_>>()
                );
                assert_eq!(branch[i], vec![subtree(i, p, &g)]);
                assert_eq!(
                    upper[i],
                    if i == p { Vec::new() } else { vec![subtree(p, i, &g1)] }
                );
            }
        }
    }
}
