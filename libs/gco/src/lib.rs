//! Solve a submodular graph cut optimizaion problem of degree $\le 2$
//!
//! As in [Graph cut optimization - Wikipedia](https://en.wikipedia.org/wiki/Graph_cut_optimization),
//! any pseudo-boolean function $f: \lbrace 0, 1 \rbrace ^ n → \mathbb R$ can be written uniquely
//! as a multi-linear polynominal:
//!
//! $$
//! f ( \boldsymbol x ) =
//!     a
//!     + \sum _ { i } a _ i x _ i
//!     + \sum _ { i, j } a _ { i, j } x _ i x _ j
//!     + \dots
//! $$
//!
//! This library can solve the minimum value of $f$ satisfying
//!
//! - $\mathop { \mathrm { deg } } f \le 2$
//! - $f$ is submodular $a _ { i, i } + a _ { j , j } \le a _ { i, j } + a _ { j, i }$
//!
//!
//! # Dependencies
//!
//! [`dinic`]
//!
//!
//! # Usages
//!
//!
//! - Use two methods [`unary`](`Gco::unary), [`binary`](Gco::binary) to add terms.
//! - The cost must has a type [`i64`].
//! - The result has a type [`bool`]. ($0$ is `false`, $1$ is `true`)
//! - We cannot automatically "filp" variables.
//!
//! This example code shows that a function
//!
//! $$
//! f (x, y) = (10 + 10 x) + (40 - 30 y) + 99 (x + y - 2xy)
//! $$
//!
//! takes its minimum $30$ at $(x, y) = (1, 1)$.
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

use dinic::Dinic;
use std::cmp::Ordering;

/// A solver of graph cut optimization problems.
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Gco {
    vars: usize,
    unary: Vec<Unary>,
    binary: Vec<Binary>,
}
impl Gco {
    /// Initialize a solver with $n$ terms.
    pub fn new(n: usize) -> Self {
        Self {
            vars: n,
            ..Self::default()
        }
    }

    /// Add a unary term.
    ///
    /// # Effects
    ///
    /// Add a unary term $c _ 0 ( 1 - x _ i ) + c _ 1 x _ i$ to $f$.
    ///
    /// # Examples
    ///
    /// ```
    /// # use gco::Gco;
    /// # let mut gco = gco::Gco::new(2);
    /// gco.unary(0, [0, 10]);
    /// gco.unary(1, [-40, 0]);
    /// ```
    pub fn unary(&mut self, i: usize, cost: [i64; 2]) { self.unary.push(Unary { i, cost }); }

    /// Add a binary term.
    ///
    /// # Effects
    ///
    /// Add the following binary term to $f$:
    ///
    /// $$
    /// c _ { 0, 0 } ( 1 - x _ i) ( 1 - x _ j )
    ///     + c _ { 0, 1 } ( 1 - x _ i ) x _ j
    ///     + c _ { 1, 0 } x _ i ( 1 - x _ j )
    ///     + c _ { 1, 1 } x _ i x _ j
    /// $$
    ///
    ///
    /// # Panics
    ///
    /// If this binary term is not submodular.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use gco::Gco;
    /// # let mut gco = gco::Gco::new(2);
    /// gco.binary([0, 1], [[0, 10], [0, 0]]); // Costs 10 when x0 = 0, x1 = 1
    /// ```
    pub fn binary(&mut self, ij: [usize; 2], cost: [[i64; 2]; 2]) {
        assert!(
            is_submodular(cost),
            "The cost should be submodular. cost = {:?}",
            cost
        );
        self.binary.push(Binary { ij, cost });
    }

    /// Returns the minimum value and an argmin of $f$.
    pub fn solve(&self) -> GcoResult { solve(self) }
}

/// The minimum value and and an argmin of $f$.
///
/// - $x _ i = 0 \Leftrightarrow \mathtt { args } _ i = \mathtt { false }$
/// - $x _ i = 1 \Leftrightarrow \mathtt { args } _ i = \mathtt { true }$
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct GcoResult {
    /// The minimum value
    pub value: i64,
    /// An argmin
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

fn index_by_array2(cost: [[i64; 2]; 2], index: [usize; 2]) -> i64 { cost[index[0]][index[1]] }
fn diff(cost: [[i64; 2]; 2], p: usize) -> i64 {
    assert!(is_submodular(cost));
    let mut index = [0, 0];
    index[p] = 1;
    index_by_array2(cost, index) - cost[0][0]
}
fn is_submodular(cost: [[i64; 2]; 2]) -> bool { cost[0][0] + cost[1][1] <= cost[0][1] + cost[1][0] }

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
