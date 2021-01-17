//! Solve a maximum flow problem with Dinic's algorithm. [See the struct level reference](Dinic)

use std::{
    collections::VecDeque,
    iter::Sum,
    ops::{AddAssign, SubAssign},
};

#[derive(Debug, Clone, PartialEq, Copy)]
struct Edge<T> {
    to: usize,
    cap: T,
    rev: usize,
}

/// An adapter trait of the capacity.
///
/// This trait is implementated for all the integer types.
///
pub trait Value: Copy + Ord + AddAssign + SubAssign + Sum {
    /// Returns the zero.
    fn zero() -> Self;
}

/// Solve a maximum flow problem with Dinic's algorithm.
///
/// # Basic usage
///
/// 1. First, initialize [`Dinic`] with the number of verticies.
/// 1. Insert edges with a method [`insert`](Dinic::insert).
/// 1. Execute the algorithm by calling a method [`build`](Dinic::build) with the source `s` and sink `t`.
///    It will return a new object of [`DinicResult`].
/// 1. Now, you can use methods of it to observe the results.
///
/// ```
/// use dinic::Dinic;
///
/// let mut dinic = Dinic::new(3);
/// dinic.insert(0, 1, 10);
/// dinic.insert(1, 2, 15);
/// dinic.insert(0, 2, 20);
///
/// let result = dinic.build(0, 2);
/// assert_eq!(result.flow(), 30);
/// assert_eq!(result.minimum_cut(), &[false, true, true]);
/// ```
///
///
/// # How to observe the results
///
/// 1. A method [`flow`](DinicResult:;flow) will tell you the value of the maximum flow.
/// 2. A method [`minimum_cut`](DinicResult::minimum_cut) will tell you the minimu cut, where
///    `false` is filled if reachable from `s`, while `true` if unreachable.
///
#[derive(Debug, Clone, PartialEq)]
pub struct Dinic<T> {
    res: Vec<Vec<Edge<T>>>,
}

impl<T> Dinic<T>
where
    T: Value,
{
    /// Creates a new instance of [`Dinic`]
    ///
    /// ```
    /// use dinic::Dinic;
    /// let dinic = Dinic::<u32>::new(3);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            res: vec![Vec::new(); n],
        }
    }

    /// Inserts a new edge to the network.
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.insert(0, 1, 10);
    /// dinic.insert(1, 2, 15);
    /// dinic.insert(0, 2, 20);
    /// ```
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

    /// Excecutes Dinic's algorithm and returns the result in [`DinicResult`]
    ///
    /// ```
    /// use dinic::{Dinic, DinicResult};
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.insert(0, 1, 10);
    /// dinic.insert(1, 2, 15);
    /// dinic.insert(0, 2, 20);
    ///
    /// let _: DinicResult<u32> = dinic.build(0, 2);
    /// ```
    pub fn build(self, s: usize, t: usize) -> DinicResult<T> {
        dinic_impl(s, t, self.res)
    }
}

/// A struct to store the result of the algorithm. [See the struct level reference](Dinic)
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
    /// Returns the value of the maximum flow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.insert(0, 1, 10);
    /// dinic.insert(1, 2, 15);
    /// dinic.insert(0, 2, 20);
    ///
    /// let result = dinic.build(0, 2);
    /// assert_eq!(result.flow(), 30);
    /// ```
    pub fn flow(&self) -> T {
        self.flow
    }

    /// Returns the minimum cut, where `false` is filled if reachable from `s`, while `true` if unreachable.
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.insert(0, 1, 10);
    /// dinic.insert(1, 2, 15);
    /// dinic.insert(0, 2, 20);
    ///
    /// let result = dinic.build(0, 2);
    /// assert_eq!(result.minimum_cut(), &[false, true, true]);
    /// ```
    pub fn minimum_cut(&self) -> &[bool] {
        &self.minimum_cut
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

macro_rules! impl_value {
    ($($T:ty),* $(,)?) => {$(
        impl Value for $T {
            fn zero() -> Self {
                0
            }
        }
    )*}
}

impl_value! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
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
            let network = rng
                .sample(SimpleGraphEdges(n, m))
                .into_iter()
                .map(|(u, v)| (u, v, rng.gen_range(0..1u32 << 16)))
                .collect::<Vec<_>>();
            let (s, t) = rng.sample(DistinctTwo(0..n));
            test_impl(n, s, t, network);
        }
    }

    #[test_case(10; "small hack")]
    #[test_case(100; "large hack")]
    fn test_hack(n: usize) {
        let (s, t, network) = generate_hack(n);
        test_impl(n, s, t, network);
    }

    fn test_impl(n: usize, s: usize, t: usize, network: Vec<(usize, usize, u32)>) {
        let mut dinic = Dinic::new(n);
        network
            .iter()
            .for_each(|&(u, v, cap)| dinic.insert(u, v, cap));
        let result = dinic.build(s, t);

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
        for (i, cap) in cap.iter().enumerate() {
            print!("\t{} |", i);
            cap.iter().for_each(|x| print!(" {}", x));
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

    // https://misawa.github.io/others/flow/dinic_time_complexity.html
    #[allow(clippy::many_single_char_names)]
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
}
