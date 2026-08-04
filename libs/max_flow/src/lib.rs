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
//! assert_eq!(inst.solve([0], [3]), 30);
//! ```

use std::{collections::VecDeque, iter::Peekable, slice::Iter};

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
    pub fn solve(
        &mut self,
        sources: impl IntoIterator<Item = usize>,
        sinks: impl IntoIterator<Item = usize>,
    ) -> u64 {
        let Self { edges } = self;
        let sources = sources.into_iter().collect::<Vec<_>>();
        let sinks = sinks.into_iter().collect::<Vec<_>>();
        let n = edges
            .iter()
            .map(|e| e.src)
            .chain(sources.iter().copied())
            .chain(sinks.iter().copied())
            .max()
            .unwrap()
            + 1;
        let mut is_sink = vec![false; n];
        for &x in &sinks {
            is_sink[x] = true;
        }
        let mut g = vec![vec![]; n];
        for (i, &e) in edges.iter().enumerate() {
            g[e.src].push(i);
        }

        let mut flow = 0;
        loop {
            let mut label = vec![usize::MAX; n];
            let mut queue = VecDeque::new();
            for &x in &sources {
                label[x] = 0;
                queue.push_back(x);
            }
            while let Some(x) = queue.pop_front() {
                for &i in &g[x] {
                    let y = edges[i].tar;
                    if edges[i].flow < edges[i].cap && label[y] == usize::MAX {
                        label[y] = label[x] + 1;
                        queue.push_back(y);
                    }
                }
            }

            if sinks.iter().all(|&x| label[x] == usize::MAX) {
                return flow;
            }

            let mut iter = g.iter().map(|g| g.iter().peekable()).collect::<Vec<_>>();
            for &x in &sources {
                let f = primal(u64::MAX, x, edges, &mut iter, &mut label, &is_sink);
                flow += f;
            }
        }
    }
}

fn primal(
    mut quota: u64,
    x: usize,
    edges: &mut Vec<Edge>,
    iter: &mut [Peekable<Iter<usize>>],
    label: &mut [usize],
    is_sink: &[bool],
) -> u64 {
    if is_sink[x] {
        return quota;
    }
    let mut result = 0;
    while let Some(&&i) = iter[x].peek() {
        let y = edges[i].tar;
        if edges[i].flow < edges[i].cap && label[x] + 1 == label[y] {
            let f = primal(
                quota.min(edges[i].cap - edges[i].flow),
                y,
                edges,
                iter,
                label,
                is_sink,
            );
            result += f;
            quota -= f;
            edges[i].flow += f;
            edges[i ^ 1].flow -= f;
            if f == 0 {
                iter[x].next().unwrap();
            }
            if quota == 0 {
                return result;
            }
        } else {
            iter[x].next().unwrap();
        }
    }
    label[x] = usize::MAX;
    result
}

/// フロー辺
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Edge {
    pub src: usize,
    pub tar: usize,
    pub cap: u64,
    pub flow: u64,
}
