//! 次数 $2$ 以下の劣モジュラなグラフカット最適化問題を解く。
//!
//! 任意の擬似ブール関数 $f: \{0, 1\}^n \to \mathbb{R}$ は、多重線形多項式
//! $f(\boldsymbol{x}) = a + \sum_i a_i x_i + \sum_{i,j} a_{i,j} x_i x_j + \dots$
//! として一意に表せる。次数が $2$ 以下で、各二次項が劣モジュラ条件
//! $a_{i,i} + a_{j,j} \le a_{i,j} + a_{j,i}$ を満たすとき、$f$ の最小化は $s$-$t$ 最小カット問題に
//! 帰着できる。変数ごとに頂点を用意し、一次項をソース・シンクへの辺重みに、二次項を変数間の辺重みに
//! 変換することでこれを実現し、最小カットの計算には [`dinic`] を用いる。
//!
//! # 仕様
//!
//! - [`Gco::unary`] で一次項 $c_0 (1 - x_i) + c_1 x_i$ を、[`Gco::binary`] で二次項
//!   $c_{0,0}(1-x_i)(1-x_j) + c_{0,1}(1-x_i)x_j + c_{1,0}x_i(1-x_j) + c_{1,1}x_ix_j$ を追加する
//! - 二次項は劣モジュラ条件 $c_{0,0} + c_{1,1} \le c_{0,1} + c_{1,0}$ を満たす必要がある（違反時は panic）
//! - コストの型は [`i64`]
//! - [`Gco::solve`] で最小値と、それを達成する $x$（`false` は $0$、`true` は $1$）を得る
//! - 変数の反転（$x_i \mapsto 1 - x_i$）は自動で行われない
//!
//! # 例
//!
//! $f(x, y) = (10 + 10x) + (40 - 30y) + 99(x + y - 2xy)$ は $(x, y) = (1, 1)$ で最小値 $30$ を取る。
//!
//! ```
//! use gco::Gco;
//!
//! let mut gco = gco::Gco::new(2);
//! gco.unary(0, [10, 20]);
//! gco.unary(1, [40, 10]);
//! gco.binary([0, 1], [[0, 99], [99, 0]]);
//!
//! let result = gco.solve();
//! assert_eq!(result.value, 30);
//! assert_eq!(&result.args, &[true, true]);
//! ```
//!
//! # 計算量
//!
//! - [`Gco::solve`][]: $O(n^2 m)$（$n$ は頂点数、$m$ は辺数。[`dinic`] の最大流計算量に従う）

use dinic::Dinic;
use std::cmp::Ordering;

/// グラフカット最適化問題のソルバー。
///
/// [`Gco::new`] で変数の個数を指定して初期化し、[`Gco::unary`], [`Gco::binary`] で
/// $f$ に項を追加してから [`Gco::solve`] で最小値と最小点を求める。
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Gco {
    vars: usize,
    unary: Vec<Unary>,
    binary: Vec<Binary>,
}
impl Gco {
    /// $n$ 個の変数を持つソルバーを初期化する。項は何も追加されていない状態（$f \equiv 0$）から始まる。
    pub fn new(n: usize) -> Self {
        Self {
            vars: n,
            ..Self::default()
        }
    }

    /// 一次項 $c_0 (1 - x_i) + c_1 x_i$ を $f$ に加える。
    ///
    /// # 例
    ///
    /// ```
    /// # use gco::Gco;
    /// # let mut gco = gco::Gco::new(2);
    /// gco.unary(0, [0, 10]); // 10 x_0
    /// gco.unary(1, [-40, 0]); // -40 (1 - x_1)
    /// ```
    pub fn unary(&mut self, i: usize, cost: [i64; 2]) {
        self.unary.push(Unary { i, cost });
    }

    /// 二次項
    /// $$
    /// c_{0,0}(1-x_i)(1-x_j) + c_{0,1}(1-x_i)x_j + c_{1,0}x_i(1-x_j) + c_{1,1}x_ix_j
    /// $$
    /// を $f$ に加える。
    ///
    /// # panics
    ///
    /// 劣モジュラ条件 $c_{0,0} + c_{1,1} \le c_{0,1} + c_{1,0}$ を満たさないとき。
    ///
    /// # 例
    ///
    /// ```
    /// # use gco::Gco;
    /// # let mut gco = gco::Gco::new(2);
    /// gco.binary([0, 1], [[0, 10], [0, 0]]); // x_0 = 0, x_1 = 1 のとき 10
    /// ```
    pub fn binary(&mut self, ij: [usize; 2], cost: [[i64; 2]; 2]) {
        assert!(
            is_submodular(cost),
            "The cost should be submodular. cost = {cost:?}"
        );
        self.binary.push(Binary { ij, cost });
    }

    /// $f$ の最小値とそれを達成する $x$ を返す。
    ///
    /// # 計算量
    ///
    /// $O(n^2 m)$（$n$ は頂点数、$m$ は辺数）
    pub fn solve(&self) -> GcoResult {
        solve(self)
    }
}

/// [`Gco::solve`] の結果。$f$ の最小値と、それを達成する $x$ を保持する。
///
/// - $x_i = 0 \Leftrightarrow$ `args[i] == false`
/// - $x_i = 1 \Leftrightarrow$ `args[i] == true`
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct GcoResult {
    /// $f$ の最小値。
    pub value: i64,
    /// 最小値を達成する $x$。
    pub args: Vec<bool>,
}

fn solve(gco: &Gco) -> GcoResult {
    let Gco {
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
        for (p, &ij) in ij.iter().enumerate() {
            let d = diff(cost, p);
            match d.cmp(&0) {
                Ordering::Less => {
                    constant += d;
                    dinic.add_edge(ij, t, -d);
                }
                Ordering::Greater => {
                    dinic.add_edge(s, ij, d);
                }
                Ordering::Equal => (),
            }
            for (i, j) in (0..2)
                .flat_map(|i| (0..2).map(move |j| (i, j)))
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
    GcoResult { value, args }
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
    use super::is_submodular;
    use super::Binary;
    use super::Gco;
    use super::GcoResult;
    use super::Unary;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use randtools::DistinctTwo;

    fn brute(gco: &Gco) -> i64 {
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
            let mut gco = Gco::new(n);
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
                    let cost = [[rng.gen_range(-9..10), rng.gen_range(-9..10)], [
                        rng.gen_range(-9..10),
                        rng.gen_range(-9..10),
                    ]];
                    if is_submodular(cost) {
                        break cost;
                    }
                };
                gco.binary(ij, cost);
            }

            let expected = brute(&gco);
            let GcoResult { value, args } = gco.clone().solve();
            assert_eq!(expected, value);
            assert_eq!(
                value,
                gco.unary
                    .iter()
                    .map(|&Unary { i, cost }| cost[usize::from(args[i])])
                    .chain(gco.binary.iter().map(|&Binary { ij: [i, j], cost }| cost
                        [usize::from(args[i])][usize::from(args[j])]),)
                    .sum::<i64>()
            );
        }
    }
}
