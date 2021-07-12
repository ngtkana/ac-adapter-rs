//! 普通の木 DP、全方位木 DP をします。
//!
//! [`Ops`] トレイトのメソッドにあります。
//!
//! - [`tree_fold`](Ops::tree_fold) : 普通の木 DP
//! - [`two_way_tree_fold`](Ops::two_way_tree_fold) : 全方位木 DP
//!
//! [`Ops::mul`] に逆元があるときには、[`Div`] トレイトのメソッドを経由して戻す DP ができます。
//!
//! - [`modosu_two_way_tree_fold`](Div::modosu_two_way_tree_fold) : 戻す DP 版全方位木 DP
//!
//! # Examples
//!
//! - 高さを計算する例 -> [`tree_fold`](Ops::tree_fold)
//! - TDPC V - Subtree -> [`two_way_tree_fold`](Ops::two_way_tree_fold)

use std::fmt::Debug;

/// 木 DP の畳み込みを定義する演算群です。
///
/// # Output
///
/// 葉において、例外的に `leaf()` （とくに、`up(identity())` ではないので注意です。）
///
/// x が葉ではないとき、`dp[x] = up(mul(proj(dp[y]), ...))` です。
///
pub trait Ops {
    /// DP 配列の値
    type Value: Clone + Default + Debug;
    /// proj(Value)
    type Acc: Clone + Debug;
    /// 葉の値
    fn leaf(&self) -> Self::Value;
    /// 前処理
    fn proj(&self, x: &Self::Value) -> Self::Acc;
    /// [`mul`](Self::mul) の単位元
    fn identity(&self) -> Self::Acc;
    /// 畳み込み演算
    fn mul(&self, acc: Self::Acc, x: Self::Acc) -> Self::Acc;
    /// 後処理
    fn up(&self, acc: Self::Acc) -> Self::Value;
    /// 木 DP を行います。（注意：g は親なし）
    ///
    /// # Examples
    ///
    /// サイズを計算する例（[`Size`] を使います。）
    ///
    /// ```
    /// # use tree_fold::{Ops, Size};
    /// let n = 5;
    /// let g = vec![
    ///     vec![1, 2],
    ///     vec![],
    ///     vec![3],
    ///     vec![],
    /// ];
    /// let ord = vec![0, 1, 2, 3];
    ///
    /// let size = Size {}.tree_fold(&ord, &g);
    /// assert_eq!(&size, &[4, 1, 2, 1]);
    /// ```
    ///
    /// 高さを計算する例（用意していないのでこういう感じで計算しましょう。）
    ///
    /// ```
    /// # use tree_fold::Ops;
    /// pub struct Hight {}
    /// impl Ops for Hight {
    ///     type Value = usize;
    ///     type Acc = usize;
    ///     fn leaf(&self) -> Self::Value {
    ///         0
    ///     }
    ///     fn proj(&self, &x: &Self::Value) -> Self::Acc {
    ///         x
    ///     }
    ///     fn identity(&self) -> Self::Acc {
    ///         0
    ///     }
    ///     fn mul(&self, acc: Self::Acc, x: Self::Acc) -> Self::Acc {
    ///         acc.max(x)
    ///     }
    ///     fn up(&self, acc: Self::Acc) -> Self::Value {
    ///         acc + 1
    ///     }
    /// }
    /// ```
    ///
    fn tree_fold(&self, ord: &[usize], g: &[Vec<usize>]) -> Vec<Self::Value> {
        let mut dp = vec![Self::Value::default(); g.len()];
        for &x in ord.iter().rev() {
            dp[x] = if g[x].is_empty() {
                self.leaf()
            } else {
                self.up(g[x]
                    .iter()
                    .map(|&y| self.proj(&dp[y]))
                    .fold(self.identity(), |acc, v| self.mul(acc, v)))
            };
        }
        dp
    }
    /// 全方位木 DP を行います。（注意：g は親なし）
    fn two_way_tree_fold(&self, ord: &[usize], g: &[Vec<usize>]) -> Vec<Self::Value> {
        let mut dp = self.tree_fold(ord, g);
        let mut ep = vec![Self::Value::default(); g.len()];
        for &x in ord {
            let d = g[x].len();
            let mut right = vec![self.identity()];
            for v in g[x].iter().rev().map(|&y| self.proj(&dp[y])) {
                let value = self.mul(right.last().unwrap().clone(), v);
                right.push(value);
            }
            let mut left = self.identity();
            for (i, &y) in g[x].iter().enumerate() {
                let mut value = self.mul(left.clone(), right[d - 1 - i].clone());
                if x != ord[0] {
                    value = self.mul(value, self.proj(&ep[x]));
                };
                ep[y] = self.up(value);
                left = self.mul(left, self.proj(&dp[y]));
            }
            if x != ord[0] {
                dp[x] = self.up(self.mul(right.last().unwrap().clone(), self.proj(&ep[x])));
            }
        }
        dp
    }
}
/// 逆元を取れるときの [`Ops`] の拡張です。
pub trait Div: Ops {
    /// [`mul`](Ops::mul) の逆元
    fn div(&self, num: &Self::Acc, den: Self::Acc) -> Self::Acc;
    /// 戻す DP 方式の全方位木 DP を行います。（注意：g は親なし）
    fn modosu_two_way_tree_fold(&self, ord: &[usize], g: &[Vec<usize>]) -> Vec<Self::Value> {
        let mut dp = self.tree_fold(ord, g);
        let mut ep = vec![Self::Value::default(); g.len()];
        for &x in ord {
            let all_prod = g[x]
                .iter()
                .map(|&y| self.proj(&dp[y]))
                .fold(self.identity(), |u, v| self.mul(u, v));
            for &y in &g[x] {
                let mut value = self.div(&all_prod, self.proj(&dp[y]));
                if x != ord[0] {
                    value = self.mul(value, self.proj(&ep[x]));
                };
                ep[y] = self.up(value);
            }
            if x != ord[0] {
                dp[x] = self.up(self.mul(all_prod, self.proj(&ep[x])));
            }
        }
        dp
    }
}

/// ［演算例］部分木のサイズを計算する演算
pub struct Size {}
impl Ops for Size {
    type Value = usize;
    type Acc = usize;
    fn leaf(&self) -> Self::Value {
        1
    }
    fn proj(&self, &x: &Self::Value) -> Self::Acc {
        x
    }
    fn identity(&self) -> Self::Acc {
        0
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
        super::{Div, Ops, Size},
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::Tree,
    };

    ////////////////////////////////////////////////////////////////////////////////
    // 普通の木 DP
    ////////////////////////////////////////////////////////////////////////////////

    #[test]
    fn test_size() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=50);
            let mut g = rng.sample(Tree(n));
            let [ord, _parent] = sort_tree(0, &mut g);
            let size = Size {}.tree_fold(&ord, &g);
            for x in 0..n {
                let result = size[x];
                let expected = 1 + g[x].iter().map(|&y| size[y]).sum::<usize>();
                assert_eq!(result, expected);
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // 全包囲木 DP
    ////////////////////////////////////////////////////////////////////////////////

    #[test]
    fn test_size_two_way() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=50);
            let mut g = rng.sample(Tree(n));
            let [ord, _parent] = sort_tree(0, &mut g);
            let result = Size {}.two_way_tree_fold(&ord, &g);
            let expected = vec![n; n];
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_tdpc_v() {
        fn brute(g: &[Vec<usize>]) -> Vec<u32> {
            let n = g.len();
            let mut ans = vec![0; n];
            for bs in 0..1 << n {
                if let Some(s) = (0..n).find(|&i| bs >> i & 1 == 1) {
                    let mut used = 0;
                    let mut stack = vec![s];
                    while let Some(x) = stack.pop() {
                        used |= 1 << x;
                        for &y in &g[x] {
                            if used >> y & 1 == 0 && bs >> y & 1 == 1 {
                                stack.push(y);
                            }
                        }
                    }
                    if used != bs {
                        continue;
                    }
                }
                for i in 0..n {
                    if bs >> i & 1 == 1 {
                        ans[i] += 1;
                    }
                }
            }
            ans
        }
        pub struct O {}
        impl Ops for O {
            type Value = Value;
            type Acc = Acc;
            fn leaf(&self) -> Self::Value {
                Value { black: 1, white: 1 }
            }
            fn proj(&self, &x: &Self::Value) -> Self::Acc {
                Acc {
                    white: x.white,
                    all: x.white + x.black,
                }
            }
            fn identity(&self) -> Self::Acc {
                Acc { white: 1, all: 1 }
            }
            fn mul(&self, acc: Self::Acc, x: Self::Acc) -> Self::Acc {
                Acc {
                    white: acc.white * x.white,
                    all: acc.all * x.all,
                }
            }
            fn up(&self, acc: Self::Acc) -> Self::Value {
                Value {
                    black: acc.all,
                    white: acc.white,
                }
            }
        }
        impl Div for O {
            fn div(&self, num: &Self::Acc, den: Self::Acc) -> Self::Acc {
                Acc {
                    white: num.white / den.white,
                    all: num.all / den.all,
                }
            }
        }
        #[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
        pub struct Value {
            black: u32,
            white: u32,
        }
        #[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
        pub struct Acc {
            white: u32,
            all: u32,
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=10);
            let mut g = rng.sample(Tree(n));
            let expected = brute(&g);
            let [ord, _parent] = sort_tree(0, &mut g);
            let result = O {}
                .two_way_tree_fold(&ord, &g)
                .into_iter()
                .map(|value| value.black)
                .collect::<Vec<_>>();
            assert_eq!(result, expected);
            let result = O {}
                .modosu_two_way_tree_fold(&ord, &g)
                .into_iter()
                .map(|value| value.black)
                .collect::<Vec<_>>();
            assert_eq!(result, expected);
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // ユーティル
    ////////////////////////////////////////////////////////////////////////////////

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
