//! 木 DP をします。
//!
//! [詳しくは `Ops` のドキュメントへどうぞです。](Ops)
//!

use std::fmt::Debug;

/// 畳み込み演算を定義します。
///
/// # `dp[x]` の定義
///
/// ```[ignore]
/// self.finish(
///     g[x].iter()
///         .map(|(&y, w)| (&dp[y], w))
///         .fold(
///             self.identity(),
///             |acc, value| self.mul(acc, value)
///         ),
///     x,
/// ),
/// ```
///
/// # できないこと
///
/// - 葉の特別扱い
///     - `identity()` を `None` とかにして頑張るしかないですかね
/// - 辺重み
///     - `頂点重みで代用できませんかね。
///
///
pub trait Ops: Sized {
    type Value: Clone + Debug + Default;
    type Acc: Clone + Debug;
    fn identity(&self) -> Self::Acc;
    fn proj(&self, value: Self::Value) -> Self::Acc;
    fn mul(&self, acc: Self::Acc, value: Self::Acc) -> Self::Acc;
    fn finish(&self, acc: Self::Acc, index: usize) -> Self::Value;

    fn tree_fold(&self, root: usize, g: &[Vec<usize>]) -> Vec<Self::Value> {
        self.tree_fold_by_iter(root, g.len(), |x| g[x].iter().copied())
    }

    fn tree_fold_by_iter<I, A>(
        &self,
        root: usize,
        n: usize,
        g: impl Fn(usize) -> A,
    ) -> Vec<Self::Value>
    where
        I: Iterator<Item = usize>,
        A: IntoIterator<Item = usize, IntoIter = I>,
    {
        let sort_tree = sort_tree(root, n, &g);
        fold_up(self, &sort_tree)
    }

    fn two_way_tree_fold(&self, root: usize, g: &[Vec<usize>]) -> Vec<Self::Value> {
        self.two_way_tree_fold_by_iter(root, g.len(), |x| g[x].iter().copied())
    }

    fn two_way_tree_fold_by_iter<I, A>(
        &self,
        root: usize,
        n: usize,
        g: impl Fn(usize) -> A,
    ) -> Vec<Self::Value>
    where
        I: Iterator<Item = usize>,
        A: IntoIterator<Item = usize, IntoIter = I>,
    {
        let sort_tree = sort_tree(root, n, &g);
        let dp = fold_up_without_finish(self, &sort_tree);
        fold_down(self, &sort_tree, &dp)
    }
}

fn fold_up<O: Ops>(ops: &O, sort_tree: &SortedTree) -> Vec<O::Value> {
    let n = sort_tree.len();
    let mut dp = vec![O::Value::default(); n];
    for &x in sort_tree.ord.iter().rev() {
        dp[x] = ops.finish(
            sort_tree.child[x].iter().fold(ops.identity(), |acc, &y| {
                ops.mul(acc, ops.proj(dp[y].clone()))
            }),
            x,
        );
    }
    dp
}

fn fold_up_without_finish<O: Ops>(ops: &O, sort_tree: &SortedTree) -> Vec<O::Acc> {
    let n = sort_tree.len();
    let mut dp = vec![ops.identity(); n];
    for &x in sort_tree.ord.iter().rev() {
        dp[x] = sort_tree.child[x].iter().fold(ops.identity(), |acc, &y| {
            ops.mul(acc, ops.proj(ops.finish(dp[y].clone(), y)))
        })
    }
    dp
}

fn fold_down<O: Ops>(ops: &O, sort_tree: &SortedTree, dp: &[O::Acc]) -> Vec<O::Value> {
    let n = sort_tree.len();
    let mut ep = vec![ops.identity(); n];
    let g = &sort_tree.child;
    for &x in &sort_tree.ord {
        if !g[x].is_empty() {
            let mut acc_rev = vec![ops.identity()];
            for &y in g[x].iter().rev().take(g[x].len() - 1) {
                let aug = ops.mul(
                    acc_rev.last().unwrap().clone(),
                    ops.proj(ops.finish(dp[y].clone(), y)),
                );
                acc_rev.push(aug);
            }
            let mut acc = ep[x].clone();
            for (&y, acc_rev) in g[x].iter().zip(acc_rev.iter().rev().cloned()) {
                ep[y] = ops.proj(ops.finish(ops.mul(acc.clone(), acc_rev), y));
                acc = ops.mul(acc.clone(), ops.proj(ops.finish(dp[y].clone(), y)));
            }
        }
    }
    dp.iter()
        .zip(&ep)
        .enumerate()
        .map(|(x, (dp_x, ep_x))| ops.finish(ops.mul(dp_x.clone(), ep_x.clone()), x))
        .collect::<Vec<_>>()
}

fn sort_tree<I, A>(root: usize, n: usize, g: impl Fn(usize) -> A) -> SortedTree
where
    I: Iterator<Item = usize>,
    A: IntoIterator<Item = usize, IntoIter = I>,
{
    fn dfs<I, A>(
        x: usize,
        p: usize,
        g: &impl Fn(usize) -> A,
        child: &mut [Vec<usize>],
        parent: &mut [usize],
        ord: &mut Vec<usize>,
    ) where
        I: Iterator<Item = usize>,
        A: IntoIterator<Item = usize, IntoIter = I>,
    {
        parent[x] = p;
        ord.push(x);
        child[x] = g(x)
            .into_iter()
            .filter(|&y| y != p)
            .inspect(|&y| dfs(y, x, g, child, parent, ord))
            .collect::<Vec<_>>()
    }
    let mut parent = vec![!0; n];
    let mut child = vec![Vec::new(); n];
    let mut ord = Vec::new();
    dfs(root, root, &g, &mut child, &mut parent, &mut ord);
    SortedTree { child, parent, ord }
}

#[derive(Clone, Debug, Default, Hash, PartialEq)]
struct SortedTree {
    child: Vec<Vec<usize>>,
    parent: Vec<usize>,
    ord: Vec<usize>,
}
impl SortedTree {
    fn len(&self) -> usize {
        self.child.len()
    }
}

#[cfg(test)]
mod tests {
    use super::Ops;
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use randtools::Tree;

    #[test]
    fn test_size() {
        struct Size {}
        impl Ops for Size {
            type Value = usize;
            type Acc = usize;
            fn proj(&self, value: Self::Value) -> Self::Acc {
                value
            }
            fn identity(&self) -> Self::Acc {
                0
            }
            fn mul(&self, acc: Self::Acc, value: Self::Acc) -> Self::Acc {
                acc + value
            }
            fn finish(&self, acc: Self::Acc, _index: usize) -> Self::Value {
                acc + 1
            }
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..=40);
            let g = rng.sample(Tree(n));

            // 全ての根でテスト
            for root in 0..n {
                // 普通の DP
                let dp = Size {}.tree_fold(root, &g);
                assert_eq!(dp[root], n);

                // 全方位木 DP
                let dp = Size {}.two_way_tree_fold(root, &g);
                assert_eq!(dp, vec![n; n]);
            }
        }
    }

    #[test]
    fn test_tdpc_v() {
        struct O {}
        impl Ops for O {
            type Value = Value;
            type Acc = Acc;
            fn proj(&self, value: Self::Value) -> Self::Acc {
                Acc {
                    white: value.white,
                    all: value.black + value.white,
                }
            }
            fn identity(&self) -> Self::Acc {
                Acc { white: 1, all: 1 }
            }
            fn mul(&self, acc: Self::Acc, value: Self::Acc) -> Self::Acc {
                Acc {
                    white: acc.white * value.white,
                    all: acc.all * value.all,
                }
            }
            fn finish(&self, acc: Self::Acc, _index: usize) -> Self::Value {
                Value {
                    black: acc.all,
                    white: acc.white,
                }
            }
        }
        #[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
        struct Value {
            black: usize,
            white: usize,
        }
        #[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
        struct Acc {
            white: usize,
            all: usize,
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..=40);
            let g = rng.sample(Tree(n));

            // 全方位木 DP
            let result = O {}.two_way_tree_fold(0, &g);

            // 普通の DP n 回
            let expected = (0..n)
                .map(|root| O {}.tree_fold(root, &g)[root])
                .collect::<Vec<_>>();

            assert_eq!(result, expected);
        }
    }
}
