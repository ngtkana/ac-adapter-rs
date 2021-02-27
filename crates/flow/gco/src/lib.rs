//! 2 次以下の劣モジュラー Graph cut 最適化問題を解きます。
//!
//! [詳細なインターフェースは `GCO` 構造体の各メソッドへどうぞ](GCO)
//!
//! # 依存ライブラリ
//!
//! [`dinic`]
//!
//!
//! # できること
//!
//! R: 実数体とします
//!
//! 関数 f: { 0, 1 } ^ n → R は必ず n 次以下の多項式で書ける。このような f
//! のうち性質の良いものについて、最小値 f(x) とそれを達成する x を計算します。
//!
//! f の条件は、次のものの和で表せることです。
//!
//! - 1 次の項
//! - 2 次の項であり、劣モジュラであるもの
//!
//!
//!
//! # 使い方
//!
//! [`unary`](`GCO::unary), [`binary`](GCO::binary)
//! メソッドで項を足していきます。
//!
//! ```
//! use gco::GCO;
//!
//! let mut gco = gco::GCO::new(2);
//! gco.unary(0, [10, 20]);
//! gco.unary(1, [40, 10]);
//! gco.binary([0, 1], [[0, 99], [99,  0]]);
//!
//! let result = gco.solve();
//! assert_eq!(result.value, 30);
//! assert_eq!(&result.args, &[true, true]);
//! ```
//!
//! - 負のコストも使えます。
//! - 変数のフリップはできません。
//! - 表現可能性は**項ごと**にチェックされます。
//! - 復元は、0 が `false`、1 が `true` で表されます。
//!
//!
//!
//! # 関連リンク
//!
//! [Graph cut optimization - Wikipedia](https://en.wikipedia.org/wiki/Graph_cut_optimization)
//!

use dinic::Dinic;
use std::cmp::Ordering;

/// 2 次以下の劣モジュラー Graph cut 最適化問題を解きます。
///
/// [概論は `gco` クレートのドキュメントへどうぞ](`self`)
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct GCO {
    vars: usize,
    unary: Vec<Unary>,
    binary: Vec<Binary>,
}
impl GCO {
    /// 変数 `n` 個からなる、制約のないインスタンスを作ります。
    pub fn new(n: usize) -> Self {
        Self {
            vars: n,
            ..Default::default()
        }
    }
    /// 1 次の項を足します。
    ///
    /// # 効果
    ///
    /// f(x) に項 `cost[x[i]]` を足します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use gco::GCO;
    ///
    /// let mut gco = gco::GCO::new(2);
    /// gco.unary(0, [0, 10]); // x _ 0 = 1 のときコスト 10
    /// gco.unary(0, [-40, 0]); // x _ 1 = 0 のときコスト -40
    /// ```
    ///
    pub fn unary(&mut self, i: usize, cost: [i64; 2]) {
        self.unary.push(Unary { i, cost });
    }
    /// モジュラーな 2 次の項を足します。
    ///
    /// # 効果
    ///
    /// f(x) に項 `cost[x[i]][x[j]]` を足します。
    ///
    ///
    /// # Panics
    ///
    /// モジュラーでないとき
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use gco::GCO;
    ///
    /// let mut gco = gco::GCO::new(2);
    /// gco.binary([0, 1], [[0, 10], [0, 0]]); // x _ 0 = 0, x _ 1 = 1 のときコスト 10
    /// ```
    ///
    pub fn binary(&mut self, ij: [usize; 2], cost: [[i64; 2]; 2]) {
        assert!(
            is_submodular(cost),
            "The cost should be submodular. cost = {:?}",
            cost
        );
        self.binary.push(Binary { ij, cost });
    }
    pub fn solve(&self) -> GCOResult {
        solve(&self)
    }
}

/// [`GCO::solve`] の返すオブジェクトです。
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct GCOResult {
    /// 最小値
    pub value: i64,
    /// 最小を達成する割当
    ///
    /// - x _ i = 0 のとき `args[i] == false`
    /// - x _ i = 1 のとき `args[i] == true`
    pub args: Vec<bool>,
}

fn solve(gco: &GCO) -> GCOResult {
    let GCO {
        vars,
        unary,
        binary,
    } = gco;
    let s = *vars;
    let t = s + 1;
    let vertex_count = t + 1;
    let mut constant = 0;
    let mut dinic = Dinic::<i64>::new(vertex_count);
    for &binary in binary {
        let Binary { ij, mut cost } = binary;
        let d = cost[0][1] + cost[1][0] - cost[0][0] - cost[1][1];
        match d.cmp(&0) {
            Ordering::Less => unreachable!(),
            Ordering::Greater => {
                dinic.add_edge(ij[0], ij[1], d);
                cost[0][1] -= d;
            }
            Ordering::Equal => (),
        }
        for p in 0..2 {
            let d = diff(cost, p);
            match d.cmp(&0) {
                Ordering::Less => {
                    constant += d;
                    dinic.add_edge(ij[p], t, -d);
                }
                Ordering::Greater => {
                    dinic.add_edge(s, ij[p], d);
                }
                Ordering::Equal => (),
            }
            for (i, j) in (0..2)
                .map(|i| (0..2).map(move |j| (i, j)))
                .flatten()
                .filter(|&(i, j)| [i, j][p] == 1)
            {
                cost[i][j] -= d;
            }
        }
        let d = cost[0][0];
        cost.iter_mut().flatten().for_each(|x| *x -= d);
        constant += d;
        assert_eq!(cost, [[0; 2]; 2]);
    }
    for &unary in unary {
        let cost = unary.cost;
        match cost[0].cmp(&cost[1]) {
            Ordering::Less => {
                dinic.add_edge(s, unary.i, cost[1] - cost[0]);
                constant += cost[0];
            }
            Ordering::Greater => {
                dinic.add_edge(unary.i, t, cost[0] - cost[1]);
                constant += cost[1];
            }
            Ordering::Equal => constant += cost[0],
        }
    }
    let value = constant + dinic.flow(s, t);
    let args = dinic.min_cut(s)[..*vars]
        .iter()
        .map(|&b| !b)
        .collect::<Vec<_>>();
    GCOResult { value, args }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
struct Unary {
    i: usize,
    cost: [i64; 2],
}
#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
struct Binary {
    ij: [usize; 2],
    cost: [[i64; 2]; 2],
}

fn index_by_array2(cost: [[i64; 2]; 2], index: [usize; 2]) -> i64 {
    cost[index[0]][index[1]]
}
fn diff(cost: [[i64; 2]; 2], p: usize) -> i64 {
    assert!(is_submodular(cost));
    let mut index = [0, 0];
    index[p] = 1;
    index_by_array2(cost, index) - cost[0][0]
}
fn is_submodular(cost: [[i64; 2]; 2]) -> bool {
    cost[0][0] + cost[1][1] <= cost[0][1] + cost[1][0]
}

#[cfg(test)]
mod tests {
    use randtools::DistinctTwo;

    use {
        super::{is_submodular, Binary, GCOResult, Unary, GCO},
        rand::{prelude::StdRng, Rng, SeedableRng},
    };

    fn brute(gco: &GCO) -> i64 {
        (0..1 << gco.vars)
            .map(|bs| {
                gco.unary
                    .iter()
                    .map(|&Unary { i, cost }| cost[bs >> i & 1])
                    .chain(
                        gco.binary
                            .iter()
                            .map(|&Binary { ij: [i, j], cost }| cost[bs >> i & 1][bs >> j & 1]),
                    )
                    .sum::<i64>()
            })
            .min()
            .unwrap()
    }

    #[test]
    fn test_random() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = 3;
            let mut gco = GCO::new(n);
            let unary_count = 0;
            let binary_count = 1;
            for _ in 0..unary_count {
                let i = rng.gen_range(0..n);
                let x = rng.gen_range(-9..10);
                let y = rng.gen_range(-9..10);
                gco.unary(i, [x, y]);
            }
            for _ in 0..binary_count {
                let (i, j) = rng.sample(DistinctTwo(0..n));
                let ij = [i, j];
                let cost = loop {
                    let cost = [
                        [rng.gen_range(-9..10), rng.gen_range(-9..10)],
                        [rng.gen_range(-9..10), rng.gen_range(-9..10)],
                    ];
                    if is_submodular(cost) {
                        break cost;
                    }
                };
                gco.binary(ij, cost);
            }

            let expected = brute(&gco);
            let GCOResult { value, args } = gco.clone().solve();
            assert_eq!(expected, value);
            assert_eq!(
                value,
                gco.unary
                    .iter()
                    .map(|&Unary { i, cost }| cost[args[i] as usize])
                    .chain(gco.binary.iter().map(
                        |&Binary { ij: [i, j], cost }| cost[args[i] as usize][args[j] as usize]
                    ),)
                    .sum::<i64>()
            );
        }
    }
}
