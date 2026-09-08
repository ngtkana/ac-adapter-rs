//! 最小費用流問題を Primal-Dual 法（Dijkstra 法による最短路反復）で解く。
//!
//! 各頂点にポテンシャル（[`MinCostFlow::slope`] 内部の `dual`）を持たせ、辺のコストを
//! reduced cost $\mathrm{cost}(u, v) + \mathrm{dual}(u) - \mathrm{dual}(v) \ge 0$ に保つことで、
//! 負辺があっても Dijkstra 法で最短増加路を求められる（Johnson 法と同じ考え方）。
//! 増加路が見つかるたびにそのボトルネック容量分だけ一気に流し、ポテンシャルを更新して
//! 次の増加路を探す、という操作を最短路長が単調に増加しなくなるまで繰り返す。
//!
//! # 仕様
//!
//! - [`MinCostFlow::new`][]: 頂点数 `n` で初期化
//! - [`MinCostFlow::add_edge`][]: 辺 `(from, to)` を容量 `cap`・コスト `cost` で追加し、辺番号を返す
//! - [`MinCostFlow::get_edge`][]: 辺番号から現在の流量込みの [`Edge`] を取得
//! - [`MinCostFlow::flow`][]: `source` から `sink` へ流量 `flow_limit` を上限に最小費用で流し、
//!   `(流量, 費用)` を返す
//! - [`MinCostFlow::slope`][]: 流量を $0$ から `flow_limit` まで増やす過程の
//!   費用関数（流量の区分線形凸関数）の頂点列 `(流量, 費用)` を返す
//!
//! # 例
//!
//! ```
//! use mincost_flow::MinCostFlow;
//!
//! let mut mcf = MinCostFlow::new(4);
//! mcf.add_edge(0, 1, 1, 20); // from, to, cap, cost
//! mcf.add_edge(0, 2, 1, 20);
//! mcf.add_edge(1, 2, 1, 10);
//!
//! let slope = mcf.slope(0, 2, i64::MAX);
//! assert_eq!(slope, vec![(0, 0), (1, 20), (2, 50)]);
//! ```
//!
//! # 計算量
//!
//! 頂点数 $n$、辺数 $m$、増加路を見つけた回数 $K$ とする。
//!
//! - Dijkstra 法 1 回: $O((n + m) \log n)$
//! - [`MinCostFlow::flow`][]、[`MinCostFlow::slope`][]: $O(K(n + m) \log n)$

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fmt::Debug;
use std::mem::replace;

/// [`MinCostFlow::get_edge`] が返す、辺の現在の状態（容量・流量・コスト）。
#[derive(Clone, Default, Hash, PartialEq, Eq, Copy)]
pub struct Edge {
    from: usize,
    to: usize,
    flow: i64,
    cap: i64,
    cost: i64,
}
impl Debug for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn fmt_i64(x: i64) -> String {
            if x == i64::MAX {
                "_".to_owned()
            } else {
                x.to_string()
            }
        }
        let &Self {
            from,
            to,
            flow,
            cap,
            cost,
        } = self;
        write!(
            f,
            "({}->{}, {}/{}, {})",
            from,
            to,
            fmt_i64(flow),
            fmt_i64(cap),
            fmt_i64(cost),
        )
    }
}
#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
struct __InternalEdge {
    to: usize,
    rev: usize,
    cap: i64,
    cost: i64,
}

/// 最小費用流を管理するグラフ本体。[`MinCostFlow::new`] で構築し、
/// [`MinCostFlow::add_edge`] で辺を追加してから [`MinCostFlow::flow`] / [`MinCostFlow::slope`] を呼ぶ。
///
/// # 例
///
/// ```
/// # use mincost_flow::MinCostFlow;
/// let mut mcf = MinCostFlow::new(4);
/// mcf.add_edge(0, 1, 1, 20); // from, to, cap, cost
/// mcf.add_edge(0, 2, 1, 20);
/// mcf.add_edge(1, 2, 1, 10);
///
/// let slope = mcf.slope(0, 2, i64::MAX);
/// assert_eq!(slope, vec![(0, 0), (1, 20), (2, 50)]);
/// ```
#[derive(Clone, Default, Hash, PartialEq)]
pub struct MinCostFlow {
    g: Vec<Vec<__InternalEdge>>,
    edge_position: Vec<[usize; 2]>,
}
impl Debug for MinCostFlow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries((0..self.g.len()).map(|i| self.get_edge(i)))
            .finish()
    }
}

impl MinCostFlow {
    /// 頂点数 `n` の空グラフを構築する。
    pub fn new(n: usize) -> Self {
        Self {
            g: vec![Vec::new(); n],
            edge_position: Vec::new(),
        }
    }

    /// 頂点 `from` から `to` へ容量 `cap`・コスト `cost` の辺を追加し、辺番号（[`MinCostFlow::get_edge`] で使う）を返す。
    pub fn add_edge(&mut self, from: usize, to: usize, cap: i64, cost: i64) -> usize {
        let res = self.edge_position.len();
        let s_from = self.g[from].len();
        let s_to = self.g[to].len();
        self.g[from].push(__InternalEdge {
            to,
            rev: s_to,
            cap,
            cost,
        });
        self.g[to].push(__InternalEdge {
            to: from,
            rev: s_from,
            cap: 0,
            cost: -cost,
        });
        self.edge_position.push([from, s_from]);
        res
    }

    /// `i` 番目に追加した辺の現在の状態（流量込み）を [`Edge`] として取得する。
    pub fn get_edge(&self, i: usize) -> Edge {
        assert!(i < self.edge_position.len());
        let [from, i] = self.edge_position[i];
        let e = self.g[from][i];
        let to = e.to;
        let rev = &self.g[to][e.rev];
        Edge {
            from,
            to,
            cap: e.cap + rev.cap,
            flow: rev.cap,
            cost: e.cost,
        }
    }

    /// `source` から `sink` へ流量 `flow_limit` を上限に最小費用で流し、`(流量, 費用)` を返す。
    pub fn flow(&mut self, source: usize, sink: usize, flow_limit: i64) -> (i64, i64) {
        self.slope(source, sink, flow_limit).pop().unwrap()
    }

    /// 流量を $0$ から `flow_limit` まで増やす過程の費用関数（流量の区分線形凸関数）の
    /// 頂点列 `(流量, 費用)` を、流量の昇順に返す。
    ///
    /// # 例
    ///
    /// ```
    /// use mincost_flow::MinCostFlow;
    ///
    /// let mut mcf = MinCostFlow::new(2);
    /// mcf.add_edge(0, 1, 3, 5); // 容量3・コスト5の辺のみ
    /// assert_eq!(mcf.slope(0, 1, i64::MAX), vec![(0, 0), (3, 15)]); // 傾き5の線分1本
    /// ```
    pub fn slope(&mut self, source: usize, sink: usize, flow_limit: i64) -> Vec<(i64, i64)> {
        let n = self.g.len();
        let mut slope = vec![(0, 0)];
        let mut flow = 0;
        let mut cost = 0;
        let mut prev_price = i64::MAX;
        while flow < flow_limit {
            let mut dual = vec![0; n];
            let mut used = vec![false; n];
            let mut prev = vec![!0; n];
            let mut pree = vec![!0; n];
            if !self.refine_dual_dijkstra(source, sink, &mut dual, &mut used, &mut prev, &mut pree)
            {
                break;
            }

            // 増分流量 aug の計算
            let mut aug = flow_limit - flow;
            let mut crr = sink;
            while crr != source {
                aug = aug.min(self.g[prev[crr]][pree[crr]].cap);
                crr = prev[crr];
            }

            // ネットワークの更新
            let mut crr = sink;
            while crr != source {
                self.g[prev[crr]][pree[crr]].cap -= aug;
                let rev = self.g[prev[crr]][pree[crr]].rev;
                self.g[crr][rev].cap += aug;
                crr = prev[crr];
            }

            // Min-cost slope への書き込み
            let price = -dual[source];
            flow += aug;
            cost += price * aug;
            if replace(&mut prev_price, price) == price {
                slope.pop().unwrap();
            }
            slope.push((flow, cost));
        }
        slope
    }

    fn refine_dual_dijkstra(
        &self,
        source: usize,
        sink: usize,
        dual: &mut [i64],
        used: &mut [bool],  // キューから出したことがあれば、`true`
        prev: &mut [usize], // 前者頂点を指す復元配列
        pree: &mut [usize], // 前者辺の前者頂点からの隣接リストに於ける位置を指す復元配列
    ) -> bool {
        let mut heap = BinaryHeap::<(Reverse<i64>, usize)>::new();
        heap.push((Reverse(0), source));
        let mut dist = vec![i64::MAX; self.g.len()];
        dist[source] = 0;
        while let Some((Reverse(dx), x)) = heap.pop() {
            used[x] = true;
            if x == sink {
                break;
            }
            for (i, &e) in self.g[x].iter().enumerate() {
                let y = e.to;
                if e.cap == 0 {
                    continue;
                }
                let dy = dx.saturating_add(e.cost) + dual[x] - dual[y];
                if dy < dist[y] {
                    prev[y] = x;
                    pree[y] = i;
                    dist[y] = dy;
                    heap.push((Reverse(dy), y));
                }
            }
        }
        if !used[sink] {
            return false;
        }
        for i in (0..self.g.len()).filter(|&i| used[i]) {
            dual[i] -= dist[sink] - dist[i];
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::MinCostFlow;

    #[test]
    fn test_mincost_flow() {
        let mut graph = MinCostFlow::new(4);
        assert_eq!(graph.add_edge(0, 1, 2, 1), 0);
        assert_eq!(graph.add_edge(0, 2, 1, 2), 1);
        assert_eq!(graph.add_edge(1, 2, 1, 1), 2);
        assert_eq!(graph.add_edge(1, 3, 1, 3), 3);
        assert_eq!(graph.add_edge(2, 3, 2, 1), 4);
        assert_eq!(graph.flow(0, 3, 2), (2, 6));
    }

    #[test]
    fn test_reduced_slope() {
        let mut graph = MinCostFlow::new(3);
        assert_eq!(graph.add_edge(0, 1, 1, 1), 0);
        assert_eq!(graph.add_edge(1, 2, 1, 0), 1);
        assert_eq!(graph.add_edge(0, 2, 2, 1), 2);
        assert_eq!(&graph.slope(0, 2, i64::MAX), &[(0, 0), (3, 3)]);
    }

    #[test]
    fn test_only_one_nonzero_cost_edge() {
        let mut graph = MinCostFlow::new(3);
        assert_eq!(graph.add_edge(0, 1, 1, 1), 0);
        assert_eq!(graph.add_edge(1, 2, 1, 0), 1);
        assert_eq!(graph.slope(0, 2, i64::MAX), &[(0, 0), (1, 1)]);
    }
}
