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
        let n = edges.iter().map(|e| e.src).max().map_or(0, |x| x + 1);
        let sources = sources.into_iter().filter(|&x| x < n).collect::<Vec<_>>();
        let sinks = sinks.into_iter().filter(|&x| x < n).collect::<Vec<_>>();
        let mut kind = vec![NodeKind::Internal; n];
        for &x in &sources {
            kind[x] = NodeKind::Source;
        }
        for &x in &sinks {
            kind[x] = NodeKind::Sink;
        }

        let mut g = vec![vec![]; n];
        for (i, &e) in edges.iter().enumerate() {
            g[e.src].push(i);
        }

        let mut excess = vec![0; n];
        let mut height = vec![0; n];
        let mut stacks = vec![vec![]; 2 * n];
        for &x in &sources {
            height[x] = n;
            for &i in &g[x] {
                let y = edges[i].tar;
                let f = edges[i].cap - edges[i].flow;
                if kind[y] == NodeKind::Source || f == 0 {
                    continue;
                }
                if excess[y] == 0 && kind[y] == NodeKind::Internal {
                    stacks[0].push(y);
                }
                excess[y] += f;
                edges[i].flow += f;
                edges[i ^ 1].flow -= f;
            }
        }

        let mut iter = g.iter().map(|g| g.iter().peekable()).collect::<Vec<_>>();
        let mut max_height = 0;
        if !stacks[0].is_empty() {
            'pop: loop {
                let x = stacks[max_height].pop().unwrap();
                assert_eq!(height[x], max_height);
                while let Some(&&i) = iter[x].peek() {
                    let y = edges[i].tar;
                    if edges[i].flow == edges[i].cap || height[x] != height[y] + 1 {
                        iter[x].next().unwrap();
                        continue;
                    }
                    let f = excess[x].min(edges[i].cap - edges[i].flow);
                    if excess[y] == 0 && kind[y] == NodeKind::Internal {
                        stacks[height[y]].push(y);
                    }
                    edges[i].flow += f;
                    edges[i ^ 1].flow -= f;
                    excess[x] -= f;
                    excess[y] += f;
                    if edges[i ^ 1].flow == 0 {
                        iter[x].next().unwrap();
                    }
                    if excess[x] == 0 {
                        while stacks[max_height].is_empty() {
                            if max_height == 0 {
                                break 'pop;
                            }
                            max_height -= 1;
                        }
                        continue 'pop;
                    }
                }
                assert!(excess[x] > 0);
                iter[x] = g[x].iter().peekable();
                height[x] += 1;
                max_height += 1;
                stacks[max_height].push(x);
            }
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
