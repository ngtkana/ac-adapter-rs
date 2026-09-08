//! フローネットワークの最大流を、highest-label 方式の push-relabel 法で求める。
//!
//! 各頂点に「高さ」ラベルを持たせ、余剰流量（excess）を持つ頂点のうち最も高いものから
//! 優先的に隣接辺へ push する。どの隣接辺にも push できなくなった頂点は、まだ残余容量の
//! ある隣接辺の中で最小の高さ + 1 までラベルを引き上げる（relabel）。この highest-label
//! 戦略により、素朴な FIFO 版よりよい $O(V^2 \sqrt E)$ の計算量を達成する。
//!
//! # 仕様
//!
//! - [`MaxFlow::new`][]: 空のネットワークを構築
//! - [`MaxFlow::add_edge`][]: 容量 `cap` の有向辺 `src -> tar` を追加（逆辺も内部で管理）
//! - [`MaxFlow::solve`][]: 頂点数 `n`、始点 `source`、終点 `sink` を指定し、最大流量と
//!   最小カット（各頂点が始点側に残るか）を返す
//! - [`MaxFlow::original_edges`][]: `add_edge` で追加した辺（逆辺を除く）を現在の流量込みで取得
//!
//! # 例
//!
//! ```
//! use max_flow::MaxFlow;
//!
//! let mut inst = MaxFlow::new();
//!
//! inst.add_edge(0, 1, 20);
//! inst.add_edge(0, 2, 10);
//! inst.add_edge(1, 2, 10);
//! inst.add_edge(1, 3, 10);
//! inst.add_edge(2, 3, 20);
//!
//! let (flow, cut) = inst.solve(4, 0, 3);
//! assert_eq!(flow, 30);
//! assert_eq!(cut, [true, false, false, false]); // 頂点 0 のみ始点側に残る
//! ```
//!
//! # 計算量
//!
//! - [`MaxFlow::add_edge`][]: $O(1)$
//! - [`MaxFlow::solve`][]: $O(V^2 \sqrt E)$（$V$: 頂点数、$E$: 辺数）

use std::collections::{BinaryHeap, VecDeque};

/// push-relabel 法で最大流を解くフローネットワーク。
#[derive(Default, Debug)]
pub struct MaxFlow {
    pub edges: Vec<Edge>,
}
impl MaxFlow {
    /// 空のネットワークを構築する。
    pub fn new() -> Self {
        Self::default()
    }

    /// 容量 `cap` の有向辺 `src -> tar` を追加する。
    ///
    /// 内部では容量 `cap`・初期流量 `cap`（残余容量 0）の逆辺も同時に追加し、
    /// [`solve`](Self::solve) はこの逆辺を通じて流量を押し戻す。
    ///
    /// # 例
    ///
    /// ```
    /// use max_flow::MaxFlow;
    /// let mut g = MaxFlow::new();
    /// g.add_edge(0, 1, 5);
    /// assert_eq!(g.original_edges()[0].cap, 5);
    /// ```
    pub fn add_edge(&mut self, src: usize, tar: usize, cap: u64) {
        self.edges.push(Edge {
            src,
            tar,
            cap,
            flow: 0,
        });
        self.edges.push(Edge {
            src: tar,
            tar: src,
            cap,
            flow: cap,
        });
    }
    /// `add_edge` で追加した辺（逆辺を除く）を、現在の流量込みで返す。
    ///
    /// # 例
    ///
    /// ```
    /// use max_flow::MaxFlow;
    /// let mut g = MaxFlow::new();
    /// g.add_edge(0, 1, 20);
    /// g.solve(2, 0, 1);
    /// assert_eq!(g.original_edges()[0].flow, 20);
    /// ```
    pub fn original_edges(&self) -> Vec<Edge> {
        self.edges.iter().step_by(2).copied().collect()
    }

    /// 頂点数 `n` のネットワークで `source` から `sink` への最大流を求め、
    /// （流量, 最小カット）を返す。
    ///
    /// 最小カットは長さ `n` の真偽値列で、`i` 番目が `true` なら頂点 `i` は
    /// 最大流確定後も `source` 側に残る（$s$-$t$ カットの $s$ 側）。
    ///
    /// # 例
    ///
    /// ```
    /// use max_flow::MaxFlow;
    /// let mut g = MaxFlow::new();
    /// g.add_edge(0, 1, 3);
    /// let (flow, cut) = g.solve(2, 0, 1);
    /// assert_eq!(flow, 3);
    /// assert_eq!(cut, [true, false]);
    /// ```
    pub fn solve(&mut self, n: usize, source: usize, sink: usize) -> (u64, Vec<bool>) {
        let Self { edges } = self;

        let mut g = vec![vec![]; n];
        for (i, &e) in edges.iter().enumerate() {
            g[e.src].push(i);
        }

        let mut excess = vec![0; n];
        for &i in &g[source] {
            let y = edges[i].tar;
            let f = edges[i].cap - edges[i].flow;
            if y == source || f == 0 {
                continue;
            }
            excess[y] += f;
            edges[i].flow += f;
            edges[i ^ 1].flow -= f;
        }

        let mut height = vec![n + 1; n];
        let mut queue = VecDeque::new();
        height[source] = n;
        height[sink] = 0;
        queue.push_back(sink);
        while let Some(x) = queue.pop_front() {
            for &i in &g[x] {
                let y = edges[i].tar;
                if y != sink && height[y] == n + 1 && edges[i].flow != 0 {
                    height[y] = height[x] + 1;
                    queue.push_back(y);
                }
            }
        }

        let mut heap = (0..n)
            .filter(|&x| x != source && x != sink && excess[x] != 0)
            .map(|x| (height[x], x))
            .collect::<BinaryHeap<_>>();
        'pop: while let Some((_, x)) = heap.pop() {
            for &i in &g[x] {
                let y = edges[i].tar;
                if edges[i].flow == edges[i].cap || height[x] <= height[y] {
                    continue;
                }
                let f = excess[x].min(edges[i].cap - edges[i].flow);
                if excess[y] == 0 && y != source && y != sink {
                    heap.push((height[y], y));
                }
                edges[i].flow += f;
                edges[i ^ 1].flow -= f;
                excess[x] -= f;
                excess[y] += f;
                if excess[x] == 0 {
                    continue 'pop;
                }
            }
            assert!(excess[x] > 0);
            height[x] = g[x]
                .iter()
                .filter(|&&i| edges[i].flow < edges[i].cap)
                .map(|&i| height[edges[i].tar])
                .min()
                .unwrap()
                + 1;
            heap.push((height[x], x));
        }

        let cut = height.iter().map(|&h| h >= n).collect();
        let flow = excess[sink];
        (flow, cut)
    }
}

/// [`MaxFlow`] が管理する有向辺（残余グラフ上の辺、逆辺を含む）。
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Edge {
    pub src: usize,
    pub tar: usize,
    pub cap: u64,
    pub flow: u64,
}
