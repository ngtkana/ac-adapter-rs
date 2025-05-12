//! Solves maximum flow problem.
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
//! # Restore the minimum cut
//!
//! If [`flow`](Dinic::flow) has called exactly once before, [`min_cut`](Dinic::min_cut) will
//! return the minimum cut. [See the API document to detailed specs.](Dinic::min_cut)
//!
//! ```
//! use dinic::Dinic;
//!
//! let mut dinic = Dinic::new(3);
//! dinic.add_edge(0, 1, 10);
//! dinic.add_edge(1, 2, 15);
//! dinic.add_edge(0, 2, 20);
//! dinic.flow(0, 2);
//!
//! assert_eq!(dinic.min_cut(0).as_slice(), &[true, false, false]);
//! ```
//!
//!
//! # Get the state of an edge or a vertex
//!
//! You can query the state of an edge via [`get_edge`](`Dinic::get_edge`). An [`EdgeKey`] object returned
//! by [`add_edge`](Dinic::add_edge`) is necessary to query it.
//!
//! ```
//! use dinic::Dinic;
//! use dinic::Edge;
//!
//! let mut dinic = Dinic::new(3);
//! dinic.add_edge(0, 1, 10);
//! let key = dinic.add_edge(1, 2, 15);
//! dinic.add_edge(0, 2, 20);
//! dinic.flow(0, 2);
//!
//! assert_eq!(dinic.get_edge(key), Edge {
//!     from: 1,
//!     to: 2,
//!     cap: 15,
//!     flow: 10
//! });
//! ```
//!
//! Moreover [`get_edges`](Dinic::get_edges), [`get_network`](Dinic::get_network) will summarize the
//! whole network.
//!
//! ```
//! use dinic::Dinic;
//! use dinic::Edge;
//!
//! let mut dinic = Dinic::new(3);
//! dinic.add_edge(0, 1, 10);
//! let key = dinic.add_edge(1, 2, 15);
//! dinic.add_edge(0, 2, 20);
//! dinic.flow(0, 2);
//!
//! let edges = dinic.get_edges();
//! let network = dinic.get_network();
//!
//! // 0th edge
//! assert_eq!(network[0][0], edges[0]);
//! assert_eq!(edges[0], Edge {
//!     from: 0,
//!     to: 1,
//!     cap: 10,
//!     flow: 10
//! });
//!
//! // 1st edge
//! assert_eq!(network[1][0], edges[1]);
//! assert_eq!(edges[1], Edge {
//!     from: 1,
//!     to: 2,
//!     cap: 15,
//!     flow: 10
//! });
//!
//! // 2nd edge
//! assert_eq!(network[0][1], edges[2]);
//! assert_eq!(edges[2], Edge {
//!     from: 0,
//!     to: 2,
//!     cap: 20,
//!     flow: 20
//! });
//! ```
//!
//! You also can get the excess of vertices, but we do not provide an interface to get the excess of *a vertex* because
//! it will take O ( m ) time.
//!
//! ```
//! use dinic::Dinic;
//! use dinic::Edge;
//!
//! let mut dinic = Dinic::new(3);
//! dinic.add_edge(0, 1, 10);
//! let key = dinic.add_edge(1, 2, 15);
//! dinic.add_edge(0, 2, 20);
//! dinic.flow(0, 2);
//!
//! assert_eq!(dinic.get_excess().as_slice(), &[-30, 0, 30]);
//! ```
//!
//! If you use an unsigned type, [`get_excess`](Dinic::get_excess) will surely overflow because the
//! excess of the source is almost always negative.
//!
//! ```should_panic
//! use dinic::Dinic;
//! use dinic::Edge;
//!
//! let mut dinic = Dinic::<u32>::new(2); // Force to use `u32` instead of `i32`.
//! dinic.add_edge(0, 1, 10);
//! dinic.flow(0, 1);
//!
//! dinic.get_excess(); // panics
//! ```
//!
//! # Call `flow` more than once
//!
//! You can call [`flow`](Dinic::flow) more than once. `flow(s, t)` will augment the flow from `s`
//! to `t` as much as possible. If [`flow`](Dinic::flow) is called with different `s` or `t` from
//! the previous ones, it may yield non-zero excess at more than two points.
//!
//! ```
//! use dinic::Dinic;
//!
//! let mut dinic = Dinic::new(3);
//! dinic.add_edge(0, 1, 10);
//! dinic.add_edge(1, 2, 15);
//! dinic.add_edge(0, 2, 20);
//!
//! dinic.flow(0, 2);
//! let aug = dinic.flow(1, 2);
//! assert_eq!(aug, 5);
//! assert_eq!(dinic.get_excess().as_slice(), &[-30, -5, 35]);
//! ```
//!
//! # Change the capacity or the amount of flow. (dangerous operation)
//!
//! [`change_edge`](Dinic::change_edge) changes the capacity and the amount of flow of an edge.
//! While it is so dangerous operation (safe variant wanted!), it is sometimes useful, for example,
//! when solve a *maximum flow problem with lower limit*. [See the API document for detailed
//! specs.](Dinic::change_edge)

use std::collections::VecDeque;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::{self};
use std::iter::Sum;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Sub;
use std::ops::SubAssign;

/// An adapter trait of the capacity.
///
/// This trait is implemented for all the integer types.
pub trait Value:
    Copy + Ord + Debug + Add<Output = Self> + AddAssign + Sub<Output = Self> + SubAssign + Sum
{
    /// Returns the zero.
    fn zero() -> Self;
    /// Returns the max value of `Self`.
    fn infinity() -> Self;
}

/// A struct to execute Dinic's algorithm.
///
/// [See the module level documentation.](self)
#[derive(Clone, PartialEq)]
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
            "`Dinic::add_edge` is called with from = {}, to = {}, but the number of verticies is \
             {}",
            from,
            to,
            self.res.len()
        );
        assert!(
            T::zero() <= cap,
            "`Dinic::add_edge` is called with a negative `cap`"
        );
        let size_from = self.res[from].len();
        let size_to = if from == to { self.res[to].len() + 1 } else { self.res[to].len() };
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
    /// You may call it multiple times. [See the module level documentation.](self)
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
    /// You may call it multiple times. [See the module level documentation.](self)
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
            "`Dinic::flow_with_limit` is called with `s` = {}, `t` = {}, while the number of \
             vertices is {}",
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
            );
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
        self.restore_edge(self.pos[edge_key])
    }

    /// Collects all the edges.
    ///
    /// Edges are sorted in order of addition.
    ///
    /// # Complexity
    ///
    /// O ( m )
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    /// use dinic::Edge;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    /// dinic.flow(0, 2);
    ///
    /// let edges = dinic.get_edges();
    /// assert_eq!(edges[0], Edge {
    ///     from: 0,
    ///     to: 1,
    ///     cap: 10,
    ///     flow: 10
    /// });
    /// assert_eq!(edges[1], Edge {
    ///     from: 1,
    ///     to: 2,
    ///     cap: 15,
    ///     flow: 10
    /// });
    /// assert_eq!(edges[2], Edge {
    ///     from: 0,
    ///     to: 2,
    ///     cap: 20,
    ///     flow: 20
    /// });
    /// ```
    pub fn get_edges(&self) -> Vec<Edge<T>> {
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .collect::<Vec<_>>()
    }

    /// Collects all the edges and arrange it in adjacent-list style.
    ///
    /// In each row, edges are sorted in order of addition.
    ///
    /// # Complexity
    ///
    /// O ( n + m )
    ///
    /// # Examples
    ///
    /// ```
    /// use dinic::Dinic;
    /// use dinic::Edge;
    ///
    /// let mut dinic = Dinic::new(3);
    /// dinic.add_edge(0, 1, 10);
    /// dinic.add_edge(1, 2, 15);
    /// dinic.add_edge(0, 2, 20);
    /// dinic.flow(0, 2);
    ///
    /// let network = dinic.get_network();
    /// assert_eq!(network[0][0], Edge {
    ///     from: 0,
    ///     to: 1,
    ///     cap: 10,
    ///     flow: 10
    /// });
    /// assert_eq!(network[0][1], Edge {
    ///     from: 0,
    ///     to: 2,
    ///     cap: 20,
    ///     flow: 20
    /// });
    /// assert_eq!(network[1][0], Edge {
    ///     from: 1,
    ///     to: 2,
    ///     cap: 15,
    ///     flow: 10
    /// });
    /// ```
    pub fn get_network(&self) -> Vec<Vec<Edge<T>>> {
        let mut network = vec![Vec::new(); self.res.len()];
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .for_each(|edge| network[edge.from].push(edge));
        network
    }

    /// Returens the `Vec` of excess of all the vertices.
    ///
    /// `i`-th entry is the excess of vertex `i`.
    ///
    /// # Complexity
    ///
    /// O ( n + m )
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
    /// dinic.flow(0, 2);
    ///
    /// let excess = dinic.get_excess();
    /// assert_eq!(excess.as_slice(), &[-30, 0, 30]);
    /// ```
    pub fn get_excess(&self) -> Vec<T> {
        let mut excess = vec![T::zero(); self.res.len()];
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .for_each(|Edge { to, flow, .. }| excess[to] += flow);
        self.pos
            .iter()
            .map(|&edge_indexer| self.restore_edge(edge_indexer))
            .for_each(|Edge { from, flow, .. }| excess[from] -= flow);
        excess
    }

    /// For internal use.
    ///
    /// # Constraints
    ///
    /// `edge_indexer` is taken from `self.pos`
    fn restore_edge(&self, edge_indexer: __EdgeIndexer) -> Edge<T> {
        let __EdgeIndexer { from, index } = edge_indexer;
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
    /// edges. [See the module level documentation.](self)
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
    /// Let us consider a bipartite matching problem on the graph `K _ 2`.
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
    /// ```
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
            "Called `Dinic::change_edge` by new_flow = {new_flow:?}, new_cap = {new_cap:?}"
        );
        let __EdgeIndexer { from, index } = self.pos[edge_key];
        let __ResidualEdge { to, rev, cap } = &mut self.res[from][index];
        *cap = new_cap - new_flow;
        let to = *to;
        let rev = *rev;
        self.res[to][rev].cap = new_flow;
    }
}
impl<T: Value> Debug for Dinic<T> {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        write!(w, "{:?}", self.get_network())
    }
}

/// A summary of the state of an edge, which is returned by [`Dinic::get_edge`].
#[derive(Clone, PartialEq, Copy, Eq)]
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
impl<T: Debug> Debug for Edge<T> {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        let Self {
            from,
            to,
            cap,
            flow,
        } = self;
        write!(
            w,
            // \x1b[1m: bold, \1b[m: cancel
            "{from}->{to}(\x1b[01m{flow:?}\x1b[m/\x1b[01m{cap:?}\x1b[m)",
        )
    }
}

/// A key object to query an edge.
///
/// Factually, this is a simple wrapper of `usize`.
/// This is returned by [`Dinic::add_edge`] and be used in
/// [`Dinic::get_edge`]
#[derive(Debug, Clone, PartialEq, Copy, Eq)]
pub struct EdgeKey(usize);

fn dinic_impl<T>(res: &mut [Vec<__ResidualEdge<T>>], s: usize, t: usize, flow_limit: T) -> T
where
    T: Value,
{
    assert_ne!(s, t);

    let mut flow = T::zero();

    loop {
        // calculate labels
        let mut label = vec![u32::MAX; res.len()];
        label[s] = 0;
        let mut queue = VecDeque::from(vec![s]);
        while let Some(from) = queue.pop_front() {
            for &__ResidualEdge { to, cap, .. } in &res[from] {
                if cap == T::zero() || label[to] != u32::MAX {
                    continue;
                }
                label[to] = label[from] + 1;
                queue.push_back(to);
            }
        }

        if label[t] == u32::MAX {
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
                $T::MAX
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
    use super::Dinic;
    use super::Edge;
    use super::EdgeKey;
    use rand::prelude::*;
    use randtools::DistinctTwo;
    use std::collections::HashSet;
    use test_case::test_case;

    ////////////////////////////////////////////////////////////////////////////////
    // Max-flow min-cut theorem test
    ////////////////////////////////////////////////////////////////////////////////

    #[allow(clippy::unused_unit)]
    #[test_case(2, 1, 10; "trivially small graph")]
    #[test_case(5, 8, 1000; "small sparse graph")]
    #[test_case(10, 8, 100; "very sparse graph")]
    #[test_case(10, 20, 100; "sparse graph")]
    #[test_case(10, 80, 50; "dense graph")]
    fn test_max_flow_min_cut(n: usize, m: usize, iter: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            let network = std::iter::repeat_with(|| {
                (
                    rng.gen_range(0..n),
                    rng.gen_range(0..n),
                    rng.gen_range(0..1_u32 << 16),
                )
            })
            .take(m)
            .collect::<Vec<_>>();
            let (s, t) = rng.sample(DistinctTwo(0..n));
            test_max_flow_min_cut_impl(n, s, t, &network);
        }
    }

    #[allow(clippy::unused_unit)]
    #[test_case(10; "small hack")]
    #[test_case(100; "large hack")]
    fn test_hack(n: usize) {
        let (s, t, network) = generate_hack(n);
        test_max_flow_min_cut_impl(n, s, t, &network);
    }

    fn test_max_flow_min_cut_impl(n: usize, s: usize, t: usize, network: &[(usize, usize, u32)]) {
        let mut dinic = Dinic::new(n);
        let edge_keys = network
            .iter()
            .map(|&(u, v, cap)| dinic.add_edge(u, v, cap))
            .collect::<Vec<_>>();
        let flow = dinic.flow(s, t);
        validate_max_flow_min_cut(n, s, t, &dinic, flow, &edge_keys);
    }

    fn validate_max_flow_min_cut(
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
        println!("flow = {flow}");
        println!("min_cut = {min_cut:?}");
        println!("s = {s}, t = {t}");
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
            excess[from] -= i64::from(flow);
            excess[to] += i64::from(flow);
            assert!(flow <= cap);
        }
        let mut excess_expected = vec![0; n];
        excess_expected[s] -= i64::from(flow);
        excess_expected[t] += i64::from(flow);
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

    ////////////////////////////////////////////////////////////////////////////////
    // Kőnig's theorem test
    ////////////////////////////////////////////////////////////////////////////////

    #[allow(clippy::unused_unit)]
    #[test_case(3, 5, 10, 10; "small graph")]
    #[test_case(5, 8, 10, 10; "medium graph")]
    #[test_case(10, 20, 10, 10; "large graph")]
    fn test_konig(n: usize, m: usize, iter: usize, change_edge_count: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            // Initialize
            let mut dinic = Dinic::new(2 * n + 2);
            let s = 2 * n;
            let t = 2 * n + 1;
            let mut edges = HashSet::new();
            while edges.len() < m {
                edges.insert([rng.gen_range(0..n), rng.gen_range(n..2 * n)]);
            }
            let edge_keys = (0..2 * n)
                .map(|i| if i < n { (s, i, 1) } else { (i, t, 1) })
                .chain(edges.iter().map(|&[from, to]| (from, to, 0)))
                .map(|(from, to, cap)| dinic.add_edge(from, to, cap))
                .collect::<Vec<_>>();
            let mut cnt = dinic.flow(s, t);
            println!("Initial flow = {cnt}");
            validate_konig(n, cnt, &dinic, &edge_keys);

            for _ in 0..change_edge_count {
                let edge_key = edge_keys[rng.gen_range(2 * n..2 * n + m)];
                let Edge {
                    from,
                    to,
                    flow,
                    cap,
                    ..
                } = dinic.get_edge(edge_key);
                if cap == 1 {
                    println!("Forbid ({from}, {to})");
                    // Forbid this match.
                    dinic.change_edge(edge_key, 0, 0);
                    if flow == 1 {
                        dinic.change_edge(edge_keys[from], 1, 0);
                        dinic.change_edge(edge_keys[to], 1, 0);
                        cnt -= 1;
                    }
                } else if cap == 0 {
                    println!("Remove the ban of ({from}, {to})");
                    // Remove the ban of this edge.
                    dinic.change_edge(edge_key, 1, 0);
                }
                cnt += dinic.flow(s, t);
                validate_konig(n, cnt, &dinic, &edge_keys);
            }
        }
    }

    fn validate_konig(n: usize, cnt: u32, dinic: &Dinic<u32>, edge_keys: &[EdgeKey]) {
        let s = 2 * n;

        println!("dinic: {:?}", &dinic);
        println!("dinic:");
        dinic
            .get_network()
            .iter()
            .enumerate()
            .for_each(|(i, v)| println!("{} {:?}", i, &v));
        println!("n = {n}, cnt = {cnt}");
        let edges = edge_keys
            .iter()
            .map(|&edge_key| dinic.get_edge(edge_key))
            .filter(|&Edge { from, to, cap, .. }| {
                cap == 1 && (0..n).contains(&from) && (n..2 * n).contains(&to)
            })
            .map(|Edge { from, to, .. }| (from, to))
            .collect::<Vec<_>>();
        println!("edges = {:?}", &edges);

        // matching is feasible
        let matching = edge_keys
            .iter()
            .map(|&edge_key| dinic.get_edge(edge_key))
            .filter(|&Edge { flow, from, to, .. }| {
                flow == 1 && (0..n).contains(&from) && (n..2 * n).contains(&to)
            })
            .map(|edge| [edge.from, edge.to])
            .collect::<Vec<_>>();
        println!("matching = {} ({:?})", matching.len(), &matching);
        assert_eq!(matching.len() as u32, cnt);
        let mut ckd = vec![false; 2 * n];
        matching.iter().flatten().for_each(|&x| {
            assert!(!ckd[x]);
            ckd[x] = true;
        });

        // maximum stable set is feasible
        let mut max_stable_set = dinic.min_cut(s);
        max_stable_set.truncate(2 * n);
        max_stable_set[n..].iter_mut().for_each(|x| *x = !*x);
        let max_stable_set_size = max_stable_set.iter().filter(|&&b| b).count();
        println!(
            "max_stable_set = {} ({:?})",
            max_stable_set_size, &max_stable_set
        );
        for &(from, to) in &edges {
            assert!(!max_stable_set[from] || !max_stable_set[to]);
        }
        assert_eq!(max_stable_set_size, 2 * n - cnt as usize);

        println!();
    }
}
