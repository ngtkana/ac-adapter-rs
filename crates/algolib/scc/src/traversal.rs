use std::mem;

/// pre-order, post-order が計算できます。
#[derive(Debug, Clone)]
pub struct Traversal {
    pub index: Vec<usize>,
    pub time: Vec<usize>,
}

impl Traversal {
    pub fn pre_order(graph: &[Vec<usize>]) -> Self {
        fn dfs(x: usize, graph: &[Vec<usize>], res: &mut PermutationBuilder) {
            res.visit(x);
            for &y in &graph[x] {
                if !res.on_stack(y) {
                    dfs(y, graph, res);
                }
            }
        }

        let mut res = PermutationBuilder::new(graph.len());
        for i in 0..graph.len() {
            if !res.on_stack(i) {
                dfs(i, graph, &mut res);
            }
        }
        res.build()
    }

    pub fn post_order(graph: &[Vec<usize>]) -> Self {
        fn dfs(x: usize, graph: &[Vec<usize>], ckd: &mut [bool], res: &mut PermutationBuilder) {
            for &y in &graph[x] {
                if !mem::replace(&mut ckd[y], true) {
                    dfs(y, graph, ckd, res);
                }
            }
            res.visit(x);
        }

        let n = graph.len();
        let mut ckd = vec![false; n];
        let mut res = PermutationBuilder::new(graph.len());
        for i in 0..graph.len() {
            if !mem::replace(&mut ckd[i], true) {
                dfs(i, graph, &mut ckd, &mut res);
            }
        }
        res.build()
    }
}

#[derive(Debug, Clone)]
struct PermutationBuilder {
    index: Vec<usize>,
    time: Vec<usize>,
}

impl PermutationBuilder {
    fn new(n: usize) -> Self {
        Self {
            index: Vec::with_capacity(n),
            time: vec![n; n],
        }
    }

    fn build(self) -> Traversal {
        Traversal {
            index: self.index,
            time: self.time,
        }
    }

    #[allow(dead_code)]
    fn is_empty(&self) -> bool {
        self.time.is_empty()
    }

    fn len(&self) -> usize {
        self.time.len()
    }

    fn time(&self) -> usize {
        self.index.len()
    }

    fn visit(&mut self, x: usize) {
        assert!(!self.on_stack(x));
        self.time[x] = self.time();
        self.index.push(x);
    }

    fn on_stack(&self, x: usize) -> bool {
        self.time[x] != self.len()
    }
}
