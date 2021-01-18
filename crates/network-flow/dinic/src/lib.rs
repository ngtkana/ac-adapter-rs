//! Solves maximum flow problem.
//!
//! TODO: tutorial
//!
//! # Basic usage
//!
//! 1. First, initialize [`Dinic`] with the number of vertices.
//! 1. Insert edges with a method [`add_edge`](Dinic::add_edge).
//! 1. Execute the algorithm by calling a method [`flow`](Dinic::flow) with the source `s` and sink `t`.
//!
//! ```
//! use dinic::Dinic;
//!
//! let mut dinic = Dinic::new(3);
//! dinic.add_edge(0, 1, 10);
//! dinic.add_edge(1, 2, 15);
//! dinic.add_edge(0, 2, 20);
//!
//! let flow = dinic.flow(0, 2);
//! assert_eq!(flow, 30);
//! ```
//!

use std::{
    collections::VecDeque,
    iter::Sum,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// A summary of the state of an edge, which is returned by [`Dinic::get_edge`].
#[derive(Debug, Clone, PartialEq, Copy, Eq)]
pub struct Edge<T> {
    /// The vertex-index of the source of an edge.
    pub from: usize,
    /// The vertex-index of the target of an edge.
    pub to: usize,
    /// The capacity of an edge.
    pub cap: T,
    /// The value of the flow of the network at this edge.
    pub flow: T,
}

/// A key object to query an edge.
///
/// Factually, this is a simple wrapper of `usize`.
/// This is returned by [`Dinic::add_edge`] and be used in
/// [`Dinic::get_edge`]
#[derive(Debug, Clone, PartialEq, Copy, Eq)]
pub struct EdgeKey(usize);

/// An adapter trait of the capacity.
///
/// This trait is implemented for all the integer types.
///
pub trait Value:
    Copy + Ord + std::fmt::Debug + Add<Output = Self> + AddAssign + Sub<Output = Self> + SubAssign + Sum
{
    /// Returns the zero.
    fn zero() -> Self;
    /// Returns the max value of `Self`.
    fn infinity() -> Self;
}

/// A struct to execute Dinic's algorithm.
///
/// [See the module level documentation](self)
#[derive(Debug, Clone, PartialEq)]
pub struct Dinic<T> {
    res: Vec<Vec<__ResidualEdge<T>>>,
    pos: Vec<__EdgeIndexer>,
}

impl<T> Dinic<T>
where
    T: Value,
{
    /// Creates a new instance of [`Dinic`]
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::<u32>::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    ///
    /// let flow = dinic.flow(0, 2);
    /// assert_eq!(flow, 30);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            res: vec![Vec::new(); n],
            pos: Vec::new(),
        }
    }

    /// Inserts a new edge to the network.
    ///
    /// # Constraints
    ///
    /// - `from, to < n`
    /// - `T::zero() <= cap`
    ///
    /// # Complexity
    ///
    /// O ( 1 ) amortized.
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    ///
    /// let flow = dinic.flow(0, 2);
    /// assert_eq!(flow, 30);
    /// ```
    pub fn add_edge(&mut self, from: usize, to: usize, cap: T) -> EdgeKey {
        assert!(
            from < self.res.len() || to < self.res.len(),
            "`Dinic::add_edge` is called with from = {}, to = {}, but the number of verticies is {}",
            from,
            to,
            self.res.len()
        );
        assert!(
            T::zero() <= cap,
            "`Dinic::add_edge` is called with a negative `cap`"
        );
        let size_from = self.res[from].len();
        let size_to = if from == to {
            self.res[to].len() + 1
        } else {
            self.res[to].len()
        };
        let edge_key = self.pos.len();
        self.pos.push(__EdgeIndexer {
            from,
            index: size_from,
        });
        self.res[from].push(__ResidualEdge {
            to,
            cap,
            rev: size_to,
        });
        self.res[to].push(__ResidualEdge {
            to: from,
            cap: T::zero(),
            rev: size_from,
        });
        EdgeKey(edge_key)
    }

    /// Auguments the flow from `s` to `t` as much as possible. It returns the amount of the
    /// flow augmented.
    ///
    /// You may call it multiple times. [See the module level documentation](self)
    ///
    ///
    /// # Constraints
    ///
    /// - `s != t`,
    /// - The answer should be in `T`.
    ///
    ///
    /// # Complexity
    ///
    /// - O ( min ( n^{2/3} m, m^{3/2} ) ) if all the capacities are 1
    /// - O ( n^2 m )
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    ///
    /// let flow = dinic.flow(0, 2);
    /// assert_eq!(flow, 30);
    /// ```
    pub fn flow(&mut self, s: usize, t: usize) -> T {
        assert!(
            s < self.res.len() && t < self.res.len(),
            "`Dinic::flow` is called with `s` = {}, `t` = {}, while the number of vertices is {}",
            s,
            t,
            self.res.len()
        );
        dinic_impl(&mut self.res, s, t, T::infinity())
    }

    /// Auguments the flow from `s` to `t` as much as possible as long as not exceeding
    /// `flow_limit`. It returns the amount of the flow augmented.
    ///
    /// You may call it multiple times. [See the module level documentation](self)
    ///
    ///
    /// # Constraints
    ///
    /// - `s != t`,
    /// - The answer should be in `T`.
    ///
    ///
    /// # Complexity
    ///
    /// - O ( min ( n^{2/3} m, m^{3/2} ) ) if all the capacities are 1
    /// - O ( n^2 m )
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    ///
    /// let flow = dinic.flow_with_limit(0, 2, 28);
    /// assert_eq!(flow, 28);
    /// ```
    pub fn flow_with_limit(&mut self, s: usize, t: usize, flow_with_limit: T) -> T {
        assert!(
            s < self.res.len() && t < self.res.len(),
            "`Dinic::flow_with_limit` is called with `s` = {}, `t` = {}, while the number of vertices is {}",
            s,
            t,
            self.res.len()
        );
        dinic_impl(&mut self.res, s, t, flow_with_limit)
    }

    /// Returns a vector of length `n`, such that the `i`-th element is `true` if and only if there
    /// is a directed path from `s` to `i` in the residual network. The returned vector correponds
    /// to a `s -- t` minimum cut after calling `self.flow(s, t)` exactly once.
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    ///
    /// dinic.flow(0, 2);
    /// assert_eq!(dinic.min_cut(0).as_slice(), &[true, false, false]);
    /// ```
    ///
    pub fn min_cut(&self, s: usize) -> Vec<bool> {
        let mut visited = vec![false; self.res.len()];
        let mut queue = VecDeque::from(vec![s]);
        while let Some(from) = queue.pop_front() {
            visited[from] = true;
            queue.extend(
                self.res[from]
                    .iter()
                    .copied()
                    .filter(|&__ResidualEdge { to, cap, .. }| {
                        cap != T::zero() && !std::mem::replace(&mut visited[to], true)
                    })
                    .map(|__ResidualEdge { to, .. }| to),
            )
        }
        visited
    }

    /// Returns the current internal state of the edges.
    ///
    /// # Complexity
    ///
    /// O ( 1 )
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(3);
    /// let edge_0 = dinic.add_edge(0, 1, 10);
    /// let edge_1 = dinic.add_edge(1, 2, 15);
    /// let edge_2 = dinic.add_edge(0, 2, 20);
    ///
    /// let flow = dinic.flow(0, 2);
    ///
    /// assert_eq!(dinic.get_edge(edge_0).flow, 10);
    /// assert_eq!(dinic.get_edge(edge_1).flow, 10);
    /// assert_eq!(dinic.get_edge(edge_2).flow, 20);
    /// assert_eq!(flow, 30);
    /// ```
    pub fn get_edge(&self, edge_key: EdgeKey) -> Edge<T> {
        let EdgeKey(edge_key) = edge_key;
        assert!(
            edge_key < self.pos.len(),
            "Called `Dinic::get_edge` with `edge_key` = {:?}, but the length of `Dinic::pos` is {}",
            edge_key,
            self.pos.len()
        );
        let __EdgeIndexer { from, index } = self.pos[edge_key];
        let __ResidualEdge { to, cap, rev } = self.res[from][index];
        let rev = self.res[to][rev];
        Edge {
            from,
            to,
            cap: cap + rev.cap,
            flow: rev.cap,
        }
    }

    /// Changes the capacity and the amount of the edge corresponding to `edge_key` to `new_cap` and
    /// `new_flow`, respectively. It does not change the capacity or the flow amount of other
    /// edges. [See the module level documentation](self)
    ///
    /// # Constraints
    ///
    /// - `T::zero() <= new_flow <= new_cap`
    ///
    /// # Complexity
    ///
    /// O ( 1 )
    ///
    /// # Examples
    ///
    /// Let us consider a bipartite matching problem on the graph `K _ 2`. Obviously this graph has
    /// a perfect matching.
    ///
    /// ```[no run]
    /// o--o
    ///  \/
    ///  /\
    /// o--o
    /// ```
    ///
    /// It can be solved as a maximum flow problem.
    ///
    /// ```
    /// use dinic::Dinic;
    ///
    /// let mut dinic = Dinic::new(6);
    /// let edge_0 = dinic.add_edge(0, 1, 1);
    /// let edge_1 = dinic.add_edge(0, 2, 1);
    /// let edge_2 = dinic.add_edge(1, 3, 1);
    /// let edge_3 = dinic.add_edge(1, 4, 1);
    /// let edge_4 = dinic.add_edge(2, 3, 1);
    /// let edge_5 = dinic.add_edge(2, 4, 1);
    /// let edge_6 = dinic.add_edge(3, 5, 1);
    /// let edge_7 = dinic.add_edge(4, 5, 1);
    ///
    /// let flow = dinic.flow(0, 5);
    /// assert_eq!(flow, 2);
    ///
    /// # // Actually, the "parallel" ones are the matching edges.
    /// # assert_eq!(dinic.get_edge(edge_2).flow, 1);
    /// # assert_eq!(dinic.get_edge(edge_3).flow, 0);
    /// # assert_eq!(dinic.get_edge(edge_4).flow, 0);
    /// # assert_eq!(dinic.get_edge(edge_5).flow, 1);
    /// ```
    ///
    /// Now, let us add another constraint. Forbid to match the top ones.
    /// In order to do this, we deminish the flow by `1` from the source to the sink, along this matching edge,
    /// and diminish the capacity of this matching edge to `0`, so that the maching is of size `1`
    /// and the `dinic` is also a feasible flow of value `1`.
    ///
    /// Now call [`Dinic::flow`] again with the same source and the same sink. So new matching will be of size `2` shaping like "X". So [`Dinic::flow`] will return the delta `1 = 2 - 1` of the flow.
    ///
    /// ```
    /// # use dinic::Dinic;
    /// #
    /// # let mut dinic = Dinic::new(6);
    /// # let edge_0 = dinic.add_edge(0, 1, 1);
    /// # let edge_1 = dinic.add_edge(0, 2, 1);
    /// # let edge_2 = dinic.add_edge(1, 3, 1);
    /// # let edge_3 = dinic.add_edge(1, 4, 1);
    /// # let edge_4 = dinic.add_edge(2, 3, 1);
    /// # let edge_5 = dinic.add_edge(2, 4, 1);
    /// # let edge_6 = dinic.add_edge(3, 5, 1);
    /// # let edge_7 = dinic.add_edge(4, 5, 1);
    ///
    /// # let flow = dinic.flow(0, 5);
    /// # assert_eq!(flow, 2);
    /// #
    /// # // Actually, the "parallel" ones are the matching edges.
    /// # assert_eq!(dinic.get_edge(edge_2).flow, 1);
    /// # assert_eq!(dinic.get_edge(edge_3).flow, 0);
    /// # assert_eq!(dinic.get_edge(edge_4).flow, 0);
    /// # assert_eq!(dinic.get_edge(edge_5).flow, 1);
    /// #
    /// dinic.change_edge(edge_0, 1, 0); // the edge from the source
    /// dinic.change_edge(edge_2, 0, 0); // the matching edge
    /// dinic.change_edge(edge_6, 1, 0); // the edge to the sink
    ///
    /// // now, `dinic` has a feasible flow of value `1`
    ///
    /// let augment = dinic.flow(0, 5);
    /// assert_eq!(augment, 1); // and augmented by `1` and became `2`.
    /// #
    /// # assert_eq!(dinic.get_edge(edge_2).flow, 0);
    /// # assert_eq!(dinic.get_edge(edge_3).flow, 1);
    /// # assert_eq!(dinic.get_edge(edge_4).flow, 1);
    /// # assert_eq!(dinic.get_edge(edge_5).flow, 0);
    /// #
    /// ```
    ///
    ///
    pub fn change_edge(&mut self, edge_key: EdgeKey, new_cap: T, new_flow: T) {
        let EdgeKey(edge_key) = edge_key;
        assert!(
            edge_key < self.pos.len(),
            "Called `Dinic::get_edge` with `edge_key` = {:?}, but the length of `Dinic::pos` is {}",
            edge_key,
            self.pos.len()
        );
        assert!(
            T::zero() <= new_flow && new_flow <= new_cap,
            "Called `Dinic::change_edge` by new_flow = {:?}, new_cap = {:?}",
            new_flow,
            new_cap
        );
        let __EdgeIndexer { from, index } = self.pos[edge_key];
        let __ResidualEdge { to, rev, cap } = &mut self.res[from][index];
        *cap = new_cap - new_flow;
        let to = *to;
        let rev = *rev;
        self.res[to][rev].cap = new_flow;
    }
}

fn dinic_impl<T>(res: &mut [Vec<__ResidualEdge<T>>], s: usize, t: usize, flow_limit: T) -> T
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
            for &__ResidualEdge { to, cap, .. } in &res[from] {
                if cap == T::zero() || label[to] != std::u32::MAX {
                    continue;
                }
                label[to] = label[from] + 1;
                queue.push_back(to);
            }
        }

        if label[t] == std::u32::MAX {
            // saturated
            return flow;
        }

        // make a current-dege data structure
        let mut cur = vec![0; res.len()];
        cur[t] = res[t].len();

        // find augmenting paths
        'PRIMAL_STEP: loop {
            let mut path = Vec::<(usize, usize)>::new();
            // depth-first search
            'FIND_AUGUMENTING_PATH: loop {
                let from = path.last().map_or(s, |&(x, i)| res[x][i].to);
                loop {
                    if let Some(&__ResidualEdge { to, cap, .. }) = res[from].get(cur[from]) {
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

            // augment the flow
            let aug = path
                .iter()
                .map(|&(x, i)| res[x][i].cap)
                .min()
                .unwrap()
                .min(flow_limit - flow);
            if aug == T::zero() {
                return flow;
            }
            flow += aug;
            for (from, i) in path {
                let __ResidualEdge { to, rev, .. } = res[from][i];
                res[from][i].cap -= aug;
                res[to][rev].cap += aug;
            }
        }
    }
}

macro_rules! impl_value {
    ($($T:ident),* $(,)?) => {$(
        impl Value for $T {
            fn zero() -> Self {
                0
            }
            fn infinity() -> Self {
                std::$T::MAX
            }
        }
    )*}
}

impl_value! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct __ResidualEdge<T> {
    to: usize,
    cap: T,
    rev: usize,
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct __EdgeIndexer {
    from: usize,
    index: usize,
}

#[cfg(test)]
mod tests {
    use {
        super::{Dinic, Edge, EdgeKey},
        rand::prelude::*,
        randtools::DistinctTwo,
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
            let network = std::iter::repeat_with(|| {
                (
                    rng.gen_range(0..n),
                    rng.gen_range(0..n),
                    rng.gen_range(0..1u32 << 16),
                )
            })
            .take(m)
            .collect::<Vec<_>>();
            let (s, t) = rng.sample(DistinctTwo(0..n));
            test_impl(n, s, t, &network);
        }
    }

    #[test_case(10; "small hack")]
    #[test_case(100; "large hack")]
    fn test_hack(n: usize) {
        let (s, t, network) = generate_hack(n);
        test_impl(n, s, t, &network);
    }

    #[test_case(5, 8, 10, 10; "small sparse graph")]
    #[test_case(50, 80, 10, 10; "medium sparse graph")]
    fn test_bipartite_matching_change_edge(
        n: usize,
        m: usize,
        iter: usize,
        change_edge_count: usize,
    ) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            // Initialize
            let mut dinic = Dinic::new(2 * n + 2);
            let s = 2 * n;
            let t = 2 * n + 1;
            let edge_ids = (0..2 * n)
                .map(|i| if i < n { (s, i, 1) } else { (i, t, 1) })
                .chain(
                    std::iter::repeat_with(|| (rng.gen_range(0..n), rng.gen_range(n..2 * n), 1))
                        .take(m),
                )
                .map(|(from, to, cap)| dinic.add_edge(from, to, cap))
                .collect::<Vec<_>>();
            let mut flow_of_network = dinic.flow(s, t);
            validate(2 * n + 2, s, t, &dinic, flow_of_network, &edge_ids);

            // Forbid or remove the ban of the edge.
            for _ in 0..change_edge_count {
                let edge_id = edge_ids[rng.gen_range(2 * n..2 * n + m)];
                let Edge {
                    from,
                    to,
                    cap,
                    flow,
                } = dinic.get_edge(edge_id);
                if cap == 0 {
                    println!("Remove the ban of {:?}", &dinic.get_edge(edge_id));
                    dinic.change_edge(edge_id, 1, 0);
                } else if flow == 1 {
                    println!("Forbid {:?}", &dinic.get_edge(edge_id));
                    dinic.change_edge(edge_ids[from], 1, 0);
                    dinic.change_edge(edge_ids[to], 1, 0);
                    dinic.change_edge(edge_id, 0, 0);
                    flow_of_network -= 1;
                }
                flow_of_network += dinic.flow(s, t);
                validate(2 * n + 2, s, t, &dinic, flow_of_network, &edge_ids);
            }
        }
    }

    fn test_impl(n: usize, s: usize, t: usize, network: &[(usize, usize, u32)]) {
        let mut dinic = Dinic::new(n);
        let edge_keys = network
            .iter()
            .map(|&(u, v, cap)| dinic.add_edge(u, v, cap))
            .collect::<Vec<_>>();
        let flow = dinic.flow(s, t);
        validate(n, s, t, &dinic, flow, &edge_keys);
    }

    fn validate(
        n: usize,
        s: usize,
        t: usize,
        dinic: &Dinic<u32>,
        flow: u32,
        edge_keys: &[EdgeKey],
    ) {
        let min_cut = dinic.min_cut(s);

        // print
        println!("Validating dinic..");
        println!("flow = {}", flow);
        println!("min_cut = {:?}", min_cut);
        println!("s = {}, t = {}", s, t);
        println!();

        // cut is feasible
        assert!(min_cut[s]);
        assert!(!min_cut[t]);

        // flow is feasible
        let mut excess = vec![0; n];
        for Edge {
            from,
            to,
            cap,
            flow,
        } in edge_keys.iter().map(|&edge| dinic.get_edge(edge))
        {
            excess[from] -= flow as i64;
            excess[to] += flow as i64;
            assert!(flow <= cap);
        }
        let mut excess_expected = vec![0; n];
        excess_expected[s] -= flow as i64;
        excess_expected[t] += flow as i64;
        assert_eq!(excess, excess_expected);

        // max-flow min-cut theorem
        let min_cut_cap = edge_keys
            .iter()
            .map(|&edge_key| dinic.get_edge(edge_key))
            .filter(|&edge| min_cut[edge.from] && !min_cut[edge.to])
            .map(|edge| edge.flow)
            .sum::<u32>();
        assert_eq!(min_cut_cap, flow);
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
