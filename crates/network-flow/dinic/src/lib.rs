use std::{
    collections::VecDeque,
    iter::Sum,
    ops::{AddAssign, SubAssign},
};

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Edge<T> {
    to: usize,
    cap: T,
    rev: usize,
}

pub trait Value: Copy + Ord + AddAssign + SubAssign + Sum {
    fn zero() -> Self;
}

#[derive(Debug, Clone, PartialEq)]
pub struct Dinic<T> {
    res: Vec<Vec<Edge<T>>>,
}

impl<T> Dinic<T>
where
    T: Value,
{
    pub fn new(n: usize) -> Self {
        Self {
            res: vec![Vec::new(); n],
        }
    }

    pub fn insert(&mut self, from: usize, to: usize, cap: T) {
        let size_from = self.res[from].len();
        let size_to = self.res[to].len();
        self.res[from].push(Edge {
            to,
            cap,
            rev: size_to,
        });
        self.res[to].push(Edge {
            to: from,
            cap: T::zero(),
            rev: size_from,
        });
    }

    pub fn build(self, s: usize, t: usize) -> DinicResult<T> {
        dinic_impl(s, t, self.res)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DinicResult<T> {
    res: Vec<Vec<Edge<T>>>, // residual network
    flow: T,
    minimum_cut: Vec<bool>,
}

impl<T> DinicResult<T>
where
    T: Value,
{
    pub fn flow(&self) -> T {
        self.flow
    }
}

fn dinic_impl<T>(s: usize, t: usize, mut res: Vec<Vec<Edge<T>>>) -> DinicResult<T>
where
    T: Value,
{
    assert_ne!(s, t);

    let mut flow = T::zero();

    loop {
        // calculate labels
        let mut label = vec![std::u32::MAX; res.len()];
        label[s] = 0;
        let mut queue = VecDeque::from(vec![s]);
        while let Some(from) = queue.pop_front() {
            for &Edge { to, cap, .. } in &res[from] {
                if cap == T::zero() || label[to] != std::u32::MAX {
                    continue;
                }
                label[to] = label[from] + 1;
                queue.push_back(to);
            }
        }
        if label[t] == std::u32::MAX {
            let minimum_cut = label
                .iter()
                .map(|&x| x == std::u32::MAX)
                .collect::<Vec<_>>();
            assert!(!minimum_cut[s]);
            assert!(minimum_cut[t]);
            return DinicResult {
                res,
                flow,
                minimum_cut,
            };
        }

        // make a current-dege data structure
        let mut cur = vec![0; res.len()];
        cur[t] = res[t].len();

        // find augumenting paths
        'PRIMAL_STEP: loop {
            // 1. let i = 0, v0 = s;
            let mut path = Vec::<(usize, usize)>::new();
            // depth-first search
            'FIND_AUGUMENTING_PATH: loop {
                let from = path.last().map_or(s, |&(x, i)| res[x][i].to);
                loop {
                    if let Some(&Edge { to, cap, .. }) = res[from].get(cur[from]) {
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

            path.push((t, std::usize::MAX)); // DEBUG
            path.windows(2).for_each(|v| {
                let (from, i) = v[0];
                let to = v[1].0;
                assert_eq!(res[from][i].to, to);
            });
            path.pop().unwrap();

            // augument the flow
            let aug = path.iter().map(|&(x, i)| res[x][i].cap).min().unwrap();
            flow += aug;
            for (from, i) in path {
                let Edge { to, rev, .. } = res[from][i];
                res[from][i].cap -= aug;
                res[to][rev].cap += aug;
            }
        }
    }
}

impl Value for u32 {
    fn zero() -> Self {
        0
    }
}
impl Value for u64 {
    fn zero() -> Self {
        0
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{Dinic, DinicResult},
        rand::prelude::*,
        randtools::{DistinctTwo, SimpleGraphEdges},
        test_case::test_case,
    };

    #[test_case(2, 1, 10; "trivially small graph")]
    #[test_case(5, 8, 1000; "small sparse graph")]
    #[test_case(50, 30, 100; "very sparse graph")]
    #[test_case(50, 200, 100; "sparse graph")]
    #[test_case(50, 1000, 50; "dense graph")]
    #[test_case(200, 1000, 10; "large graph")]
    fn test_rand(n: usize, m: usize, iter: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            let mut dinic = Dinic::new(n);
            let network = rng
                .sample(SimpleGraphEdges(n, m))
                .into_iter()
                .map(|(u, v)| (u, v, rng.gen_range(0..1u32 << 16)))
                .collect::<Vec<_>>();
            network
                .iter()
                .for_each(|&(u, v, cap)| dinic.insert(u, v, cap));
            let (s, t) = rng.sample(DistinctTwo(0..n));
            let result = dinic.build(s, t);
            validate_dinic(n, s, t, network, result);
        }
    }

    fn validate_dinic(
        n: usize,
        s: usize,
        t: usize,
        network: Vec<(usize, usize, u32)>,
        result: DinicResult<u32>,
    ) {
        let DinicResult {
            flow,
            minimum_cut,
            res: _,
        } = result;

        println!("Validating dinic..");
        println!("flow = {}", flow);
        println!("minimum_cut = {:?}", minimum_cut);
        println!();

        println!("s = {}, t = {}", s, t);
        let mut cap = vec![vec![0; n]; n];
        network.iter().for_each(|&(u, v, c)| cap[u][v] = c);
        print!("cap = ");
        for i in 0..n {
            print!("\t{} |", i);
            cap[i].iter().for_each(|x| print!(" {}", x));
            println!();
        }

        let minimum_cut_cap = cap
            .iter()
            .enumerate()
            .map(|(i, v)| v.iter().enumerate().map(move |(j, &c)| (i, j, c)))
            .flatten()
            .filter(|&(u, v, _)| !minimum_cut[u] && minimum_cut[v])
            .map(|(_, _, c)| c)
            .sum::<u32>();
        assert_eq!(minimum_cut_cap, flow);

        println!()
    }
}
