//! 木 DP をします。
//!
//! # Example
//!
//! 演算を定義したいときには、[`Ops`] トレイトを実装した型を定義して使いましょう。
//!
//! 部分木のサイズを計算する DP は、よく使うので [`Size`] 型として用意されています。
//!
//! ```
//! use tree_fold::{Ops, Size};
//! let n = 5;
//! let g = vec![
//!     vec![1, 2],
//!     vec![],
//!     vec![3],
//!     vec![],
//! ];
//! let ord = vec![0, 1, 2, 3];
//! let size = Size {}.tree_fold(&ord, &g);
//! assert_eq!(&size, &[4, 1, 2, 1]);
//! ```
//!

/// 木 DP の畳み込みを定義する演算群です。
///
/// 演算は、
///
/// * x が葉ならば `dp[x] = leaf()`
/// * さもなくば `dp[x] = up(mul(proj(g[y]), ...))`
///
/// で定義されます。
///
pub trait Ops {
    /// DP 配列の値
    type Value: Clone + Default;
    /// proj(Value)
    type Acc;
    /// 葉の値
    fn leaf(&self) -> Self::Value;
    /// フォールドする前に行う演算
    fn proj(&self, x: &Self::Value) -> Self::Acc;
    fn mul(&self, acc: Self::Acc, x: Self::Acc) -> Self::Acc;
    fn up(&self, acc: Self::Acc) -> Self::Value;
    /// 木 DP を行います。（注意：g は親なし）
    fn tree_fold(&self, ord: &[usize], g: &[Vec<usize>]) -> Vec<Self::Value> {
        let mut dp = vec![Self::Value::default(); g.len()];
        for &x in ord.iter().rev() {
            let mut acc = None;
            for f in g[x].iter().map(|&y| self.proj(&dp[y])) {
                acc = Some(match acc {
                    None => f,
                    Some(acc) => self.mul(acc, f),
                });
            }
            dp[x] = acc.map_or_else(|| self.leaf(), |x| self.up(x));
        }
        dp
    }
}

/// ［演算例］部分木のサイズを計算する演算
pub struct Size {}
impl Ops for Size {
    type Value = u32;
    type Acc = u32;
    fn leaf(&self) -> Self::Value {
        1
    }
    fn proj(&self, &x: &Self::Value) -> Self::Acc {
        x
    }
    fn mul(&self, acc: Self::Acc, x: Self::Acc) -> Self::Acc {
        acc + x
    }
    fn up(&self, acc: Self::Acc) -> Self::Value {
        acc + 1
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{Ops, Size},
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::Tree,
    };

    #[test]
    fn test_size() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..10);
            let mut g = rng.sample(Tree(n));
            let [ord, _parent] = sort_tree(0, &mut g);
            let size = Size {}.tree_fold(&ord, &g);
            for x in 0..n {
                let result = size[x];
                let expected = 1 + g[x].iter().map(|&y| size[y]).sum::<u32>();
                assert_eq!(result, expected);
            }
        }
    }

    fn sort_tree(root: usize, g: &mut [Vec<usize>]) -> [Vec<usize>; 2] {
        fn dfs(x: usize, p: usize, g: &[Vec<usize>], ord: &mut Vec<usize>, parent: &mut [usize]) {
            ord.push(x);
            for y in g[x].iter().copied().filter(|&y| y != p) {
                parent[y] = x;
                dfs(y, x, g, ord, parent);
            }
        }
        let mut ord = Vec::new();
        let mut parent = (0..g.len()).collect::<Vec<_>>();
        dfs(root, root, g, &mut ord, &mut parent);
        for (x, gx) in g.iter_mut().enumerate() {
            if let Some(i) = gx.iter().position(|&y| y == parent[x]) {
                gx.swap_remove(i);
            }
        }
        [ord, parent]
    }
}
