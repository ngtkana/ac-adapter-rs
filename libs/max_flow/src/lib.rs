//! フローネットワークの最大流を求める
//!
//! # Usage
//!
//! ## 構築
//!
//! * [`MaxFlow::new`]
//! * [`MaxFlow::add_edge`]
//!
//!
//! ## 実行
//!
//! * [`MaxFlow::solve`]
//!
//! source, sink は複数指定できます。
//!
//!
//! ## 総流量以外の情報の取得
//!
//! [`MaxFlow::edges`] を public にしてあるのでそれでなんとか
//!
//! # Examples
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
//! assert_eq!(inst.solve(4, &[0], &[3]), 30);
//! ```

use std::collections::{BinaryHeap, VecDeque};

/// フローネットワーク
#[derive(Default, Debug)]
pub struct MaxFlow {
    pub edges: Vec<Edge>,
}
impl MaxFlow {
    pub fn new() -> Self {
        Self::default()
    }
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
    pub fn solve(&mut self, n: usize, sources: &[usize], sinks: &[usize]) -> u64 {
        let Self { edges } = self;
        if sources.is_empty() || sinks.is_empty() {
            return 0;
        }

        let mut kind = vec![NodeKind::Internal; n];
        for &x in sources {
            kind[x] = NodeKind::Source;
        }
        for &x in sinks {
            kind[x] = NodeKind::Sink;
        }

        let mut g = vec![vec![]; n];
        for (i, &e) in edges.iter().enumerate() {
            g[e.src].push(i);
        }

        let mut excess = vec![0; n];
        for &x in sources {
            for &i in &g[x] {
                let y = edges[i].tar;
                let f = edges[i].cap - edges[i].flow;
                if kind[y] == NodeKind::Source || f == 0 {
                    continue;
                }
                excess[y] += f;
                edges[i].flow += f;
                edges[i ^ 1].flow -= f;
            }
        }

        let mut height = vec![n + 1; n];
        let mut queue = VecDeque::new();
        for &x in sources {
            height[x] = n;
        }
        for &x in sinks {
            height[x] = 0;
            queue.push_back(x);
        }
        while let Some(x) = queue.pop_front() {
            for &i in &g[x] {
                let y = edges[i].tar;
                if kind[y] != NodeKind::Sink && height[y] == n + 1 && edges[i].flow != 0 {
                    height[y] = height[x] + 1;
                    queue.push_back(y);
                }
            }
        }

        let mut heap = (0..n)
            .filter(|&x| kind[x] == NodeKind::Internal && excess[x] != 0)
            .map(|x| (height[x], x))
            .collect::<BinaryHeap<_>>();
        'pop: while let Some((_, x)) = heap.pop() {
            for &i in &g[x] {
                let y = edges[i].tar;
                if edges[i].flow == edges[i].cap || height[x] <= height[y] {
                    continue;
                }
                let f = excess[x].min(edges[i].cap - edges[i].flow);
                if excess[y] == 0 && kind[y] == NodeKind::Internal {
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

        (0..n)
            .filter(|&x| kind[x] == NodeKind::Sink)
            .map(|x| excess[x])
            .sum()
    }
}

/// フロー辺
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Edge {
    pub src: usize,
    pub tar: usize,
    pub cap: u64,
    pub flow: u64,
}

#[derive(PartialEq, Clone, Copy)]
enum NodeKind {
    Source,
    Sink,
    Internal,
}
