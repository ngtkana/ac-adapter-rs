//! 強連結成分分解と 2-SAT です。
//!
//! # 使い方
//!
//! [`Scc`] を使います。
//!
//! ```
//! use scc::*;
//! let mut scc = Scc::new(4);
//! scc.add_edge(0, 1);
//! scc.add_edge(2, 3);
//! scc.add_edge(3, 2);
//!
//! let (number_of_components, id) = scc.solve();
//! assert_eq!(number_of_components, 3);
//! assert_eq!(id, vec![0, 1, 2, 2]);
//!
//! assert_eq!(scc.groups(), vec![vec![0], vec![1], vec![2, 3]]);
//! ```
//!
//! # 仕様
//!
//! - [`solve`] で連結成分数と属する連結成分の番号のリストのペアが返ります。
//! - [`groups`] でそれを連結成分リストに変換したものを返します。
//!
//! # 2−SAT
//!
//! [`TwoSat`] を使いましょう。
//!
//! # おまけ
//!
//! - [`Traversal`] で pre-order, post-order が計算できます。
//! - [`WhiteStack`] で [`on_stack`] が線形でできるスタックができます。
//!
//!
//! [`Scc`]: struct.Scc.html
//! [`TwoSat`]: struct.TwoSat.html
//! [`Traversal`]: struct.Traversal.html
//! [`WhiteStack`]: struct.WhiteStack.html
//! [`solve`]: struct.Scc.html#method.solve
//! [`groups`]: struct.Scc.html#method.groups
//! [`on_stack`]: struct.WhiteStack.html#structfield.on_stack
mod traversal;
mod white_stack;

// TODO: この2つは別ライブラリに切り出しても良いかもです。
pub use traversal::*;
pub use white_stack::*;

use std::cmp;

/// 強連結成分分解ができます。
#[derive(Debug, Clone)]
pub struct Scc {
    forward: Vec<Vec<usize>>, // TODO: フラットグラフも試します。
    backward: Vec<Vec<usize>>,
}

impl Scc {
    /// 頂点数を指定して離散グラフを構築です。
    pub fn new(len: usize) -> Self {
        Self {
            forward: vec![Vec::new(); len],
            backward: vec![Vec::new(); len],
        }
    }
    /// 辺を追加です。
    pub fn add_edge(&mut self, u: usize, v: usize) {
        self.forward[u].push(v);
        self.backward[v].push(u);
    }
    /// 連結成分数と属する連結成分の番号のリストのペアが返ります。
    pub fn solve(&self) -> (usize, Vec<usize>) {
        fn dfs(x: usize, g: &[Vec<usize>], res: &mut [Option<usize>]) {
            for &y in &g[x] {
                if res[y].is_none() {
                    res[y] = res[x];
                    dfs(y, g, res);
                }
            }
        }
        let n = self.forward.len();
        let post_backward = Traversal::post_order(&self.backward);
        let mut res = vec![None; n];
        let mut counter = 0;
        for &x in post_backward.index.iter().rev() {
            if res[x].is_none() {
                res[x] = Some(counter);
                dfs(x, &self.forward, &mut res);
                counter += 1;
            }
        }
        (
            counter,
            res.iter().map(|x| counter - 1 - x.unwrap()).collect(),
        )
    }
    // TODO: 答えをいい感じにキャッシュするようにしても良いかもです。
    /// それを連結成分リストに変換したものを返します。
    pub fn groups(&self) -> Vec<Vec<usize>> {
        let (count, id) = self.solve();
        let mut res = vec![Vec::new(); count];
        for (i, &x) in id.iter().enumerate() {
            res[x].push(i);
        }
        res
    }
}

/// 2-SAT をときます。
#[derive(Debug, Clone)]
pub struct TwoSat {
    len: usize,
    scc: Scc,
}
impl TwoSat {
    /// 変項 `len` 個の空文を構築します。
    pub fn new(len: usize) -> Self {
        Self {
            len,
            scc: Scc::new(2 * len),
        }
    }
    /// `x[i] == f || x[j] == g` を追加します。
    pub fn add_clause(&mut self, i: usize, f: bool, j: usize, g: bool) {
        self.scc.add_edge(2 * i + !f as usize, 2 * j + g as usize);
        self.scc.add_edge(2 * j + !g as usize, 2 * i + f as usize);
    }
    /// 解いて、あれば答えを返し、なければ `None` を返します。
    pub fn solve(&mut self) -> Option<Vec<bool>> {
        self.scc
            .solve()
            .1
            .chunks_exact(2)
            .map(|v| {
                use cmp::Ordering::*;
                match v[0].cmp(&v[1]) {
                    Equal => None,
                    Less => Some(true),
                    Greater => Some(false),
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use std::iter;
    use test_case::test_case;

    #[test_case(3, &[(0, 1), (0, 2)] => (vec![0, 1, 2], vec![0, 1, 2]))]
    #[test_case(4, &[(0, 1), (1, 3), (0, 2)] => (vec![0, 1, 3, 2], vec![0, 1, 3, 2]))]
    #[test_case(4, &[(0, 2), (1, 2), (2, 3)] => (vec![0, 2, 3, 1], vec![0, 3, 1, 2]))]
    #[test_case(4, &[(0, 3), (1, 3), (2, 3)] => (vec![0, 3, 1, 2], vec![0, 2, 3, 1]))]
    fn test_preorder(n: usize, edges: &[(usize, usize)]) -> (Vec<usize>, Vec<usize>) {
        let mut graph = vec![Vec::new(); n];
        for &(u, v) in edges {
            graph[u].push(v);
        }
        let pre = Traversal::pre_order(&graph);
        (pre.index, pre.time)
    }

    #[test_case(4, &[ (0, 1), (1, 2), (2, 3), (3, 1), (2, 0) ] => (1, vec![0, 0, 0, 0]))]
    #[test_case(4, &[ (0, 1), (1, 2), (2, 3), (1, 0), (3, 2) ] => (2, vec![0, 0, 1, 1]))]
    #[test_case(8,
        &[ (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 5), (6, 4), (2, 0) ]
        => (3, vec![0, 0, 0, 1, 2, 2, 2, 2]))]
    #[test_case(8,
        &[ (0, 1), (1, 2), (0, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 5), (6, 4), (2, 0) ]
        => (3, vec![0, 0, 0, 1, 2, 2, 2, 2]))]
    fn test_scc_hand(n: usize, edges: &[(usize, usize)]) -> (usize, Vec<usize>) {
        let mut scc = Scc::new(n);
        for &(u, v) in edges {
            scc.add_edge(u, v);
        }
        scc.solve()
    }

    fn reachable(start: usize, end: usize, graph: &[Vec<usize>]) -> bool {
        let n = graph.len();
        let mut queue = std::collections::VecDeque::from(vec![start]);
        let mut ckd = vec![false; n];
        ckd[start] = true;
        while let Some(x) = queue.pop_front() {
            for &y in &graph[x] {
                if !std::mem::replace(&mut ckd[y], true) {
                    queue.push_back(y);
                }
            }
        }
        ckd[end]
    }

    #[test]
    fn test_scc_random() {
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..20 {
            let n = rng.gen_range(4..15);
            let mut graph = vec![Vec::new(); n];
            let mut scc = Scc::new(n);
            for _ in 0..2 * n {
                let u = rng.gen_range(0..n);
                let v = rng.gen_range(0..n);
                graph[u].push(v);
                scc.add_edge(u, v);
            }
            println!("graph = {:?}", &graph);
            let (_counter, ic) = scc.solve();
            for u in 0..n {
                for v in u..n {
                    let uv = reachable(u, v, &graph);
                    let vu = reachable(v, u, &graph);

                    println!("u = {}, v = {}, u -> v: {}, v -> u: {}", u, v, uv, vu);
                    match (uv, vu) {
                        (true, true) => assert_eq!(ic[u], ic[v]),
                        (true, false) => assert!(ic[u] < ic[v]),
                        (false, true) => assert!(ic[u] > ic[v]),
                        (false, false) => assert_ne!(ic[u], ic[v]),
                    }
                }
            }
        }
    }

    fn validate(n: usize, conditions: &[(usize, bool, usize, bool)], answer: Option<Vec<bool>>) {
        if let Some(answer) = answer {
            for &(i, f, j, g) in conditions {
                assert!(answer[i] == f || answer[j] == g);
            }
        } else {
            assert!((0..1 << n).all(|bs| conditions
                .iter()
                .any(|&(i, f, j, g)| !((bs >> i == 1) == f || (bs >> j == 1) == g))));
        }
    }

    #[test_case(2, &[(0, false, 1, true), (0, false, 1, false), (0, true, 1, true)])]
    #[test_case(2, &[(0, false, 1, true), (0, false, 1, false), (0, true, 1, false), (0, true, 1, true)])]
    #[test_case(2, &[(0, false, 1, true)])]
    #[test_case(3, &[(0, false, 1, true), (2, true, 1, false)])]
    #[test_case(4, &[(0, false, 1, true), (2, true, 1, false), (2, false, 1, false)])]
    fn test_two_sat_hand(n: usize, conditions: &[(usize, bool, usize, bool)]) {
        let mut two_sat = TwoSat::new(n);
        for &(i, f, j, g) in conditions {
            two_sat.add_clause(i, f, j, g);
        }
        let answer = two_sat.solve();
        validate(n, conditions, answer);
    }

    #[test]
    fn test_two_sat_random() {
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..40 {
            let n = rng.gen_range(4..15);
            let m = rng.gen_range(0..4 * n);
            let conditions = iter::repeat_with(|| {
                (
                    rng.gen_range(0..n),
                    rng.gen_ratio(1, 2),
                    rng.gen_range(0..n),
                    rng.gen_ratio(1, 2),
                )
            })
            .take(m)
            .collect::<Vec<_>>();
            println!("n = {}, conditions = {:?}", n, &conditions);

            let mut two_sat = TwoSat::new(n);
            for &(i, f, j, g) in &conditions {
                two_sat.add_clause(i, f, j, g);
            }
            let answer = two_sat.solve();
            println!("answer = {:?}", &answer);
            validate(n, &conditions, answer);
        }
    }
}
