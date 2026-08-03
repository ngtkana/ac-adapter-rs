use std::{collections::VecDeque, slice::Iter};

#[derive(Debug, Default)]
pub struct Recorder {
    pub bfs_count: Vec<usize>,
    pub call_primal_count: Vec<usize>,
}

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
        recorder: &mut Recorder,
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

            recorder.bfs_count.push(1);
            recorder.call_primal_count.push(0);

            let mut iter = g.iter().map(|g| g.iter()).collect::<Vec<_>>();
            for &x in &sources {
                let f = primal(
                    u64::MAX,
                    x,
                    edges,
                    &mut iter,
                    &mut label,
                    &is_sink,
                    recorder,
                );
                if f == 0 {
                    label[x] = usize::MAX;
                }
                flow += f;
            }
        }
    }
}

fn primal(
    f: u64,
    x: usize,
    edges: &mut Vec<Edge>,
    iter: &mut [Iter<usize>],
    label: &mut [usize],
    is_sink: &[bool],
    recorder: &mut Recorder,
) -> u64 {
    *recorder.call_primal_count.last_mut().unwrap() += 1;
    if is_sink[x] {
        return f;
    }
    let mut result = 0;
    while let Some(&i) = iter[x].next() {
        let y = edges[i].tar;
        if edges[i].flow < edges[i].cap && label[x] + 1 == label[y] {
            let g = primal(
                (f - result).min(edges[i].cap - edges[i].flow),
                y,
                edges,
                iter,
                label,
                is_sink,
                recorder,
            );
            if g == 0 {
                label[y] = usize::MAX;
                continue;
            }
            edges[i].flow += g;
            edges[i ^ 1].flow -= g;
            result += g;
            if result == f {
                break;
            }
        }
    }
    assert!(result <= f);
    result
}

#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Edge {
    pub src: usize,
    pub tar: usize,
    pub cap: u64,
    pub flow: u64,
}
