//! Dijkstra 法の最短路反復により、最小費用流問題を解きます。
//!
//! [See the document of `MinCostFlow`](MinCostFlow)

use std::{cmp::Reverse, collections::BinaryHeap, fmt::Debug, i64::MAX, mem::replace};

/// [`MinCostFlow::get_edge`] の戻り値型
#[derive(Clone, Default, Hash, PartialEq, Copy)]
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
            if x == MAX {
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

/// Dijkstra 法の最短路反復により、最小費用流問題を解きます。
///
/// # 使い方
///
/// - [`new()`](MinCostFlow::new) で空グラフを構築してき、
/// - [`add_edge()`](MinCostFlow::add_edge) で辺を挿入していき、
/// - [`flow()`](MinCostFlow::flow) または [`slope()`](MinCostFlow::slope) で答えを聞きます。
///
/// ```
/// # use mincost_flow::MinCostFlow;
/// let mut mcf = MinCostFlow::new(4);
/// mcf.add_edge(0, 1, 1, 20); // from, to, cap, cost
/// mcf.add_edge(0, 2, 1, 20);
/// mcf.add_edge(1, 2, 1, 10);
///
/// let slope = mcf.slope(0, 2, std::i64::MAX);
/// assert_eq!(slope, vec![(0, 0), (1, 20), (2, 50)]);
/// ```
///
///
/// また [`Debug`] トレイトを独自実装しています。
///
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
    /// 空グラフを構築します。
    pub fn new(n: usize) -> Self {
        Self {
            g: vec![Vec::new(); n],
            edge_position: Vec::new(),
        }
    }
    /// 辺を追加します。
    pub fn add_edge(&mut self, u: usize, v: usize, cap: i64, cost: i64) -> usize {
        let res = self.edge_position.len();
        let su = self.g[u].len();
        let sv = self.g[v].len();
        self.g[u].push(__InternalEdge {
            to: v,
            rev: sv,
            cap,
            cost,
        });
        self.g[v].push(__InternalEdge {
            to: u,
            rev: su,
            cap: 0,
            cost: -cost,
        });
        self.edge_position.push([u, su]);
        res
    }
    /// `i` 番目に挿入した辺を取得します。
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
    /// 解きます
    ///
    /// # 出力形式
    ///
    /// `(flow, cost)`
    ///
    pub fn flow(&mut self, source: usize, sink: usize, flow_limit: i64) -> (i64, i64) {
        self.slope(source, sink, flow_limit).pop().unwrap()
    }
    /// 解きます
    ///
    /// # 出力形式
    ///
    /// `(flow, cost)`
    ///
    pub fn slope(&mut self, source: usize, sink: usize, flow_limit: i64) -> Vec<(i64, i64)> {
        let n = self.g.len();
        let mut slope = vec![(0, 0)];
        let mut flow = 0;
        let mut cost = 0;
        let mut prev_price = MAX;
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
        let mut dist = vec![MAX; self.g.len()];
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
    use {super::MinCostFlow, std::i64::MAX};

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
        assert_eq!(&graph.slope(0, 2, MAX), &[(0, 0), (3, 3)]);
    }

    #[test]
    fn test_only_one_nonzero_cost_edge() {
        let mut graph = MinCostFlow::new(3);
        assert_eq!(graph.add_edge(0, 1, 1, 1), 0);
        assert_eq!(graph.add_edge(1, 2, 1, 0), 1);
        assert_eq!(graph.slope(0, 2, MAX), &[(0, 0), (1, 1)]);
    }
}
