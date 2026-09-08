//! Dinic 法による最大流アルゴリズム。
//!
//! BFS で各頂点に始点からの距離（レベル）を付け、レベルが単調増加する経路だけを辿って
//! DFS でブロッキングフロー（そのレベルグラフでは増やせなくなるまでの流量）を1フェーズで
//! まとめて求める。レベル付けができなくなるまでフェーズを繰り返すことで最大流に到達する。
//!
//! # 仕様
//!
//! [`Dinic`] にグラフを構築し、次の操作を提供する。
//!
//! - [`Dinic::new(n)`](Dinic::new): 頂点数 `n` で初期化
//! - [`add_edge(from, to, cap)`](Dinic::add_edge): 辺を追加し [`EdgeKey`] を返す
//! - [`flow(s, t)`](Dinic::flow): `s` から `t` への最大流を求める。複数回呼び出し可能
//! - [`flow_with_limit(s, t, limit)`](Dinic::flow_with_limit): 流量の上限付き版
//! - [`min_cut(s)`](Dinic::min_cut): 直前の `flow(s, t)` に対応する最小カット
//! - [`get_edge`](Dinic::get_edge) / [`get_edges`](Dinic::get_edges) / [`get_network`](Dinic::get_network): 辺の状態の取得
//! - [`get_excess`](Dinic::get_excess): 各頂点の余剰流量（符号付き整数型が必要）
//! - [`change_edge`](Dinic::change_edge): 辺の容量・流量を直接書き換える危険な操作（下限付き最大流などに使う）
//!
//! # 例
//!
//! ```
//! use dinic::Dinic;
//!
//! let mut dinic = Dinic::new(3);
//! dinic.add_edge(0, 1, 10);
//! dinic.add_edge(1, 2, 15);
//! dinic.add_edge(0, 2, 20);
//!
//! assert_eq!(dinic.flow(0, 2), 30);
//! assert_eq!(dinic.min_cut(0).as_slice(), &[true, false, false]);
//! ```
//!
//! # 計算量
//!
//! $n$: 頂点数、$m$: 辺数とする。
//!
//! - [`flow`](Dinic::flow): $O(n^2 m)$（単位容量グラフなら $O(\min(n^{2/3} m, m^{3/2}))$）
//! - [`get_edge`](Dinic::get_edge), [`change_edge`](Dinic::change_edge), [`add_edge`](Dinic::add_edge): $O(1)$ 償却
//! - [`get_edges`](Dinic::get_edges), [`get_excess`](Dinic::get_excess): $O(m)$
//! - [`get_network`](Dinic::get_network): $O(n + m)$

use std::collections::VecDeque;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::{self};
use std::iter::Sum;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Sub;
use std::ops::SubAssign;

/// [`Dinic`] の容量として使える整数型が実装するトレイト。全整数型に実装済み。
pub trait Value:
    Copy + Ord + Debug + Add<Output = Self> + AddAssign + Sub<Output = Self> + SubAssign + Sum
{
    /// 加法単位元 `0`。
    fn zero() -> Self;
    /// `Self` の最大値。Dinic 法の内部で無限大として使う。
    fn infinity() -> Self;
}

/// Dinic 法の状態を保持するグラフ本体。[モジュールレベルの説明を参照](self)。
#[derive(Clone, PartialEq)]
pub struct Dinic<T> {
    res: Vec<Vec<__ResidualEdge<T>>>,
    pos: Vec<__EdgeIndexer>,
}

impl<T> Dinic<T>
where
    T: Value,
{
    /// 頂点数 `n` のグラフで [`Dinic`] を初期化する。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::<u32>::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    /// assert_eq!(dinic.flow(0, 2), 30);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            res: vec![Vec::new(); n],
            pos: Vec::new(),
        }
    }

    /// 辺 `(from, to)` を容量 `cap` で追加し、後で参照するための [`EdgeKey`] を返す。
    ///
    /// # 仕様
    ///
    /// `from, to < n`、`cap >= 0` が前提。
    ///
    /// # 計算量
    ///
    /// $O(1)$ 償却。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// let key = dinic.add_edge(0, 1, 10);
    /// assert_eq!(dinic.get_edge(key).cap, 10);
    /// ```
    pub fn add_edge(&mut self, from: usize, to: usize, cap: T) -> EdgeKey {
        assert!(
            from < self.res.len() && to < self.res.len(),
            "`Dinic::add_edge` is called with from = {}, to = {}, but the number of verticies is \
             {}",
            from,
            to,
            self.res.len()
        );
        assert!(
            T::zero() <= cap,
            "`Dinic::add_edge` is called with a negative `cap`"
        );
        let size_from = self.res[from].len();
        let size_to = if from == to { self.res[to].len() + 1 } else { self.res[to].len() };
        let edge_key = self.pos.len();
        self.pos.push(__EdgeIndexer {
            from,
            index: size_from,
        });
        self.res[from].push(__ResidualEdge {
            to,
            cap,
            rev: size_to,
        });
        self.res[to].push(__ResidualEdge {
            to: from,
            cap: T::zero(),
            rev: size_from,
        });
        EdgeKey(edge_key)
    }

    /// `s` から `t` へ流せるだけ流し、増加した流量を返す。複数回呼び出し可能。
    ///
    /// 同じ `(s, t)` で複数回呼んだ場合、増加量の合計は1回で呼んだ場合と一致する。
    /// 異なる `(s, t)` で呼ぶと、2点以外にも余剰が生じ得る。
    ///
    /// # 仕様
    ///
    /// `s != t` が前提。戻り値は `T` で表現できる範囲に収まる必要がある。
    ///
    /// # 計算量
    ///
    /// $O(n^2 m)$。全ての容量が1なら $O(\min(n^{2/3} m, m^{3/2}))$。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    /// assert_eq!(dinic.flow(0, 2), 30);
    /// ```
    pub fn flow(&mut self, s: usize, t: usize) -> T {
        assert!(
            s < self.res.len() && t < self.res.len(),
            "`Dinic::flow` is called with `s` = {}, `t` = {}, while the number of vertices is {}",
            s,
            t,
            self.res.len()
        );
        dinic_impl(&mut self.res, s, t, T::infinity())
    }

    /// `s` から `t` へ、流量が `flow_with_limit` を超えない範囲で流せるだけ流す。増加した流量を返す。
    ///
    /// # 仕様
    ///
    /// `s != t` が前提。
    ///
    /// # 計算量
    ///
    /// [`flow`](Dinic::flow) と同じ。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    /// assert_eq!(dinic.flow_with_limit(0, 2, 28), 28);
    /// ```
    pub fn flow_with_limit(&mut self, s: usize, t: usize, flow_with_limit: T) -> T {
        assert!(
            s < self.res.len() && t < self.res.len(),
            "`Dinic::flow_with_limit` is called with `s` = {}, `t` = {}, while the number of \
             vertices is {}",
            s,
            t,
            self.res.len()
        );
        dinic_impl(&mut self.res, s, t, flow_with_limit)
    }

    /// 残余ネットワークで `s` から到達可能な頂点集合を返す（`i` 番目が `true` なら到達可能）。
    ///
    /// 直前に `flow(s, t)` を1回だけ呼んでいれば、これは `s`–`t` 最小カットに対応する。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    ///
    /// dinic.flow(0, 2);
    /// assert_eq!(dinic.min_cut(0).as_slice(), &[true, false, false]);
    /// ```
    pub fn min_cut(&self, s: usize) -> Vec<bool> {
        let mut visited = vec![false; self.res.len()];
        let mut queue = VecDeque::from(vec![s]);
        while let Some(from) = queue.pop_front() {
            visited[from] = true;
            queue.extend(
                self.res[from]
                    .iter()
                    .copied()
                    .filter(|&__ResidualEdge { to, cap, .. }| {
                        cap != T::zero() && !std::mem::replace(&mut visited[to], true)
                    })
                    .map(|__ResidualEdge { to, .. }| to),
            );
        }
        visited
    }

    /// `edge_key` に対応する辺の現在の状態（[`Edge`]）を返す。
    ///
    /// # 計算量
    ///
    /// $O(1)$。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// let edge_0 = dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.flow(0, 2);
    /// assert_eq!(dinic.get_edge(edge_0).flow, 10);
    /// ```
    pub fn get_edge(&self, edge_key: EdgeKey) -> Edge<T> {
        let EdgeKey(edge_key) = edge_key;
        assert!(
            edge_key < self.pos.len(),
            "Called `Dinic::get_edge` with `edge_key` = {:?}, but the length of `Dinic::pos` is {}",
            edge_key,
            self.pos.len()
        );
        self.restore_edge(self.pos[edge_key])
    }

    /// 全ての辺を追加順に [`Edge`] として集める。
    ///
    /// # 計算量
    ///
    /// $O(m)$。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.flow(0, 2);
    /// assert_eq!(dinic.get_edges().len(), 2);
    /// ```
    pub fn get_edges(&self) -> Vec<Edge<T>> {
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .collect::<Vec<_>>()
    }

    /// 全ての辺を隣接リスト形式（`network[from]` に始点が `from` の辺一覧）で集める。各行は追加順。
    ///
    /// # 計算量
    ///
    /// $O(n + m)$。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.flow(0, 1);
    /// let network = dinic.get_network();
    /// assert_eq!(network[0][0].to, 1);
    /// ```
    pub fn get_network(&self) -> Vec<Vec<Edge<T>>> {
        let mut network = vec![Vec::new(); self.res.len()];
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .for_each(|edge| network[edge.from].push(edge));
        network
    }

    /// 各頂点の余剰流量（流入 − 流出）を `Vec` で返す。`i` 番目が頂点 `i` の値。
    ///
    /// 始点の余剰はほぼ常に負になるため、符号なし整数型では実行時に必ずオーバーフローする。
    ///
    /// # 計算量
    ///
    /// $O(n + m)$。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    /// dinic.flow(0, 2);
    /// assert_eq!(dinic.get_excess().as_slice(), &[-30, 0, 30]);
    /// ```
    pub fn get_excess(&self) -> Vec<T> {
        let mut excess = vec![T::zero(); self.res.len()];
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .for_each(|Edge { to, flow, .. }| excess[to] += flow);
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .for_each(|Edge { from, flow, .. }| excess[from] -= flow);
        excess
    }

    /// 内部用。`edge_indexer` は `self.pos` から取得したものが前提。
    fn restore_edge(&self, edge_indexer: __EdgeIndexer) -> Edge<T> {
        let __EdgeIndexer { from, index } = edge_indexer;
        let __ResidualEdge { to, cap, rev } = self.res[from][index];
        let rev = self.res[to][rev];
        Edge {
            from,
            to,
            cap: cap + rev.cap,
            flow: rev.cap,
        }
    }

    /// 辺 `edge_key` の容量・流量を `new_cap`, `new_flow` に直接書き換える。他の辺は変わらない。
    ///
    /// 下限付き最大流や、特定の辺の使用を禁止した上で最大流を求め直す用途に使う危険な操作。
    ///
    /// # 仕様
    ///
    /// `T::zero() <= new_flow <= new_cap` が前提。
    ///
    /// # 計算量
    ///
    /// $O(1)$。
    ///
    /// # 例
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// let e = dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.flow(0, 2);
    ///
    /// dinic.change_edge(e, 5, 5); // 容量を10→5に減らす（既に流れている5はそのまま）
    /// assert_eq!(dinic.get_edge(e).cap, 5);
    /// assert_eq!(dinic.get_edge(e).flow, 5);
    /// ```
    pub fn change_edge(&mut self, edge_key: EdgeKey, new_cap: T, new_flow: T) {
        let EdgeKey(edge_key) = edge_key;
        assert!(
            edge_key < self.pos.len(),
            "Called `Dinic::get_edge` with `edge_key` = {:?}, but the length of `Dinic::pos` is {}",
            edge_key,
            self.pos.len()
        );
        assert!(
            T::zero() <= new_flow && new_flow <= new_cap,
            "Called `Dinic::change_edge` by new_flow = {new_flow:?}, new_cap = {new_cap:?}"
        );
        let __EdgeIndexer { from, index } = self.pos[edge_key];
        let __ResidualEdge { to, rev, cap } = &mut self.res[from][index];
        *cap = new_cap - new_flow;
        let to = *to;
        let rev = *rev;
        self.res[to][rev].cap = new_flow;
    }
}
impl<T: Value> Debug for Dinic<T> {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        write!(w, "{:?}", self.get_network())
    }
}

/// [`Dinic::get_edge`] 等が返す、辺の状態のスナップショット。
#[derive(Clone, PartialEq, Copy, Eq)]
pub struct Edge<T> {
    /// 辺の始点。
    pub from: usize,
    /// 辺の終点。
    pub to: usize,
    /// 辺の容量。
    pub cap: T,
    /// 辺に流れている流量。
    pub flow: T,
}
impl<T: Debug> Debug for Edge<T> {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        let Self {
            from,
            to,
            cap,
            flow,
        } = self;
        write!(
            w,
            // \x1b[1m: bold, \1b[m: cancel
            "{from}->{to}(\x1b[01m{flow:?}\x1b[m/\x1b[01m{cap:?}\x1b[m)",
        )
    }
}

/// 辺を指す不透明なキー。[`Dinic::add_edge`] が返し、[`Dinic::get_edge`] 等に渡す。
#[derive(Debug, Clone, PartialEq, Copy, Eq)]
pub struct EdgeKey(usize);

fn dinic_impl<T>(res: &mut [Vec<__ResidualEdge<T>>], s: usize, t: usize, flow_limit: T) -> T
where
    T: Value,
{
    assert_ne!(s, t);

    let mut flow = T::zero();

    loop {
        // calculate labels
        let mut label = vec![u32::MAX; res.len()];
        label[s] = 0;
        let mut queue = VecDeque::from(vec![s]);
        while let Some(from) = queue.pop_front() {
            for &__ResidualEdge { to, cap, .. } in &res[from] {
                if cap == T::zero() || label[to] != u32::MAX {
                    continue;
                }
                label[to] = label[from] + 1;
                queue.push_back(to);
            }
        }

        if label[t] == u32::MAX {
            // saturated
            return flow;
        }

        // make a current-dege data structure
        let mut cur = vec![0; res.len()];
        cur[t] = res[t].len();

        // find augmenting paths
        'PRIMAL_STEP: loop {
            let mut path = Vec::<(usize, usize)>::new();
            // depth-first search
            'FIND_AUGUMENTING_PATH: loop {
                let from = path.last().map_or(s, |&(x, i)| res[x][i].to);
                loop {
                    if let Some(&__ResidualEdge { to, cap, .. }) = res[from].get(cur[from]) {
                        if cap == T::zero() || label[from] + 1 != label[to] {
                            cur[from] += 1;
                        } else {
                            path.push((from, cur[from]));
                            break;
                        }
                    } else if from == s {
                        break 'PRIMAL_STEP;
                    } else if from == t {
                        break 'FIND_AUGUMENTING_PATH;
                    } else {
                        path.pop().unwrap();
                        let from = path.last().map_or(s, |&(x, i)| res[x][i].to);
                        cur[from] += 1;
                        break;
                    }
                }
            }

            // augment the flow
            let aug = path
                .iter()
                .map(|&(x, i)| res[x][i].cap)
                .min()
                .unwrap()
                .min(flow_limit - flow);
            if aug == T::zero() {
                return flow;
            }
            flow += aug;
            for (from, i) in path {
                let __ResidualEdge { to, rev, .. } = res[from][i];
                res[from][i].cap -= aug;
                res[to][rev].cap += aug;
            }
        }
    }
}

macro_rules! impl_value {
    ($($T:ident),* $(,)?) => {$(
        impl Value for $T {
            fn zero() -> Self {
                0
            }
            fn infinity() -> Self {
                $T::MAX
            }
        }
    )*}
}

impl_value! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct __ResidualEdge<T> {
    to: usize,
    cap: T,
    rev: usize,
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct __EdgeIndexer {
    from: usize,
    index: usize,
}

#[cfg(test)]
mod tests {
    use super::Dinic;
    use super::Edge;
    use super::EdgeKey;
    use rand::prelude::*;
    use randtools::DistinctTwo;
    use std::collections::HashSet;
    use test_case::test_case;

    ////////////////////////////////////////////////////////////////////////////////
    // Max-flow min-cut theorem test
    ////////////////////////////////////////////////////////////////////////////////

    #[allow(clippy::unused_unit)]
    #[test_case(2, 1, 10; "trivially small graph")]
    #[test_case(5, 8, 1000; "small sparse graph")]
    #[test_case(10, 8, 100; "very sparse graph")]
    #[test_case(10, 20, 100; "sparse graph")]
    #[test_case(10, 80, 50; "dense graph")]
    fn test_max_flow_min_cut(n: usize, m: usize, iter: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            let network = std::iter::repeat_with(|| {
                (
                    rng.gen_range(0..n),
                    rng.gen_range(0..n),
                    rng.gen_range(0..1_u32 << 16),
                )
            })
            .take(m)
            .collect::<Vec<_>>();
            let (s, t) = rng.sample(DistinctTwo(0..n));
            test_max_flow_min_cut_impl(n, s, t, &network);
        }
    }

    #[allow(clippy::unused_unit)]
    #[test_case(10; "small hack")]
    #[test_case(100; "large hack")]
    fn test_hack(n: usize) {
        let (s, t, network) = generate_hack(n);
        test_max_flow_min_cut_impl(n, s, t, &network);
    }

    fn test_max_flow_min_cut_impl(n: usize, s: usize, t: usize, network: &[(usize, usize, u32)]) {
        let mut dinic = Dinic::new(n);
        let edge_keys = network
            .iter()
            .map(|&(u, v, cap)| dinic.add_edge(u, v, cap))
            .collect::<Vec<_>>();
        let flow = dinic.flow(s, t);
        validate_max_flow_min_cut(n, s, t, &dinic, flow, &edge_keys);
    }

    fn validate_max_flow_min_cut(
        n: usize,
        s: usize,
        t: usize,
        dinic: &Dinic<u32>,
        flow: u32,
        edge_keys: &[EdgeKey],
    ) {
        let min_cut = dinic.min_cut(s);

        // print
        println!("Validating dinic..");
        println!("flow = {flow}");
        println!("min_cut = {min_cut:?}");
        println!("s = {s}, t = {t}");
        println!();

        // cut is feasible
        assert!(min_cut[s]);
        assert!(!min_cut[t]);

        // flow is feasible
        let mut excess = vec![0; n];
        for Edge {
            from,
            to,
            cap,
            flow,
        } in edge_keys.iter().map(|&edge| dinic.get_edge(edge))
        {
            excess[from] -= i64::from(flow);
            excess[to] += i64::from(flow);
            assert!(flow <= cap);
        }
        let mut excess_expected = vec![0; n];
        excess_expected[s] -= i64::from(flow);
        excess_expected[t] += i64::from(flow);
        assert_eq!(excess, excess_expected);

        // max-flow min-cut theorem
        let min_cut_cap = edge_keys
            .iter()
            .map(|&edge_key| dinic.get_edge(edge_key))
            .filter(|&edge| min_cut[edge.from] && !min_cut[edge.to])
            .map(|edge| edge.flow)
            .sum::<u32>();
        assert_eq!(min_cut_cap, flow);
    }

    // https://misawa.github.io/others/flow/dinic_time_complexity.html
    fn generate_hack(n: usize) -> (usize, usize, Vec<(usize, usize, u32)>) {
        let s = 0;
        let a = 1;
        let b = 2;
        let c = 3;
        let t = 4;
        let mut uv = [5, 6];

        let mut edges = Vec::new();
        edges.extend(vec![(s, a, 1), (s, b, 2), (b, a, 2), (c, t, 2)]);
        edges.extend(uv.iter().map(|&x| (a, x, 3)));
        loop {
            let next_uv = [uv[0] + 2, uv[1] + 2];
            if n <= next_uv[1] {
                break;
            }
            edges.extend(uv.iter().zip(next_uv.iter()).map(|(&x, &y)| (x, y, 3)));
            uv = next_uv;
        }
        edges.extend(uv.iter().map(|&x| (x, c, 3)));
        (s, t, edges)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Kőnig's theorem test
    ////////////////////////////////////////////////////////////////////////////////

    #[allow(clippy::unused_unit)]
    #[test_case(3, 5, 10, 10; "small graph")]
    #[test_case(5, 8, 10, 10; "medium graph")]
    #[test_case(10, 20, 10, 10; "large graph")]
    fn test_konig(n: usize, m: usize, iter: usize, change_edge_count: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            // Initialize
            let mut dinic = Dinic::new(2 * n + 2);
            let s = 2 * n;
            let t = 2 * n + 1;
            let mut edges = HashSet::new();
            while edges.len() < m {
                edges.insert([rng.gen_range(0..n), rng.gen_range(n..2 * n)]);
            }
            let edge_keys = (0..2 * n)
                .map(|i| if i < n { (s, i, 1) } else { (i, t, 1) })
                .chain(edges.iter().map(|&[from, to]| (from, to, 0)))
                .map(|(from, to, cap)| dinic.add_edge(from, to, cap))
                .collect::<Vec<_>>();
            let mut cnt = dinic.flow(s, t);
            println!("Initial flow = {cnt}");
            validate_konig(n, cnt, &dinic, &edge_keys);

            for _ in 0..change_edge_count {
                let edge_key = edge_keys[rng.gen_range(2 * n..2 * n + m)];
                let Edge {
                    from,
                    to,
                    flow,
                    cap,
                    ..
                } = dinic.get_edge(edge_key);
                if cap == 1 {
                    println!("Forbid ({from}, {to})");
                    // Forbid this match.
                    dinic.change_edge(edge_key, 0, 0);
                    if flow == 1 {
                        dinic.change_edge(edge_keys[from], 1, 0);
                        dinic.change_edge(edge_keys[to], 1, 0);
                        cnt -= 1;
                    }
                } else if cap == 0 {
                    println!("Remove the ban of ({from}, {to})");
                    // Remove the ban of this edge.
                    dinic.change_edge(edge_key, 1, 0);
                }
                cnt += dinic.flow(s, t);
                validate_konig(n, cnt, &dinic, &edge_keys);
            }
        }
    }

    fn validate_konig(n: usize, cnt: u32, dinic: &Dinic<u32>, edge_keys: &[EdgeKey]) {
        let s = 2 * n;

        println!("dinic: {:?}", &dinic);
        println!("dinic:");
        dinic
            .get_network()
            .iter()
            .enumerate()
            .for_each(|(i, v)| println!("{} {:?}", i, &v));
        println!("n = {n}, cnt = {cnt}");
        let edges = edge_keys
            .iter()
            .map(|&edge_key| dinic.get_edge(edge_key))
            .filter(|&Edge { from, to, cap, .. }| {
                cap == 1 && (0..n).contains(&from) && (n..2 * n).contains(&to)
            })
            .map(|Edge { from, to, .. }| (from, to))
            .collect::<Vec<_>>();
        println!("edges = {:?}", &edges);

        // matching is feasible
        let matching = edge_keys
            .iter()
            .map(|&edge_key| dinic.get_edge(edge_key))
            .filter(|&Edge { flow, from, to, .. }| {
                flow == 1 && (0..n).contains(&from) && (n..2 * n).contains(&to)
            })
            .map(|edge| [edge.from, edge.to])
            .collect::<Vec<_>>();
        println!("matching = {} ({:?})", matching.len(), &matching);
        assert_eq!(matching.len() as u32, cnt);
        let mut ckd = vec![false; 2 * n];
        matching.iter().flatten().for_each(|&x| {
            assert!(!ckd[x]);
            ckd[x] = true;
        });

        // maximum stable set is feasible
        let mut max_stable_set = dinic.min_cut(s);
        max_stable_set.truncate(2 * n);
        max_stable_set[n..].iter_mut().for_each(|x| *x = !*x);
        let max_stable_set_size = max_stable_set.iter().filter(|&&b| b).count();
        println!(
            "max_stable_set = {} ({:?})",
            max_stable_set_size, &max_stable_set
        );
        for &(from, to) in &edges {
            assert!(!max_stable_set[from] || !max_stable_set[to]);
        }
        assert_eq!(max_stable_set_size, 2 * n - cnt as usize);

        println!();
    }
}
