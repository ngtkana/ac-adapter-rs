//! Kosaraju's algorithm for strongly connected components
//!
//! # Note: CSR (Compressed Sparse Row)
//!
//! Graphs and set partitions are represented in CSR format [`Csr`].
//!
//!
//! # Examples
//! ```
//! use graph::kosaraju;
//! let n = 6;
//! let edges = [ (1, 4), (5, 2), (3, 0), (5, 5), (4, 1), (0, 3), (4, 2)];
//! let scc = kosaraju(n, &edges);
//! assert_eq!(scc.len(), 4);
//! assert_eq!(scc[0], [5]);
//! assert_eq!(scc[1], [1, 4]);
//! assert_eq!(scc[2], [2]);
//! assert_eq!(scc[3], [0, 3]);
//! ```
mod csr;

pub use csr::Csr;
pub use csr::Iter;
pub use csr::LastMut;

/// Returns the strongly connected components of a directed graph.
///
/// # Examples
/// ```
/// use graph::kosaraju;
/// let n = 6;
/// let edges = [ (1, 4), (5, 2), (3, 0), (5, 5), (4, 1), (0, 3), (4, 2)];
/// let scc = kosaraju(n, &edges);
/// assert_eq!(scc.len(), 4);
/// assert_eq!(scc[0], [5]);
/// assert_eq!(scc[1], [1, 4]);
/// assert_eq!(scc[2], [2]);
/// assert_eq!(scc[3], [0, 3]);
/// ```
pub fn kosaraju(n: usize, edges: &[(usize, usize)]) -> Csr<usize> {
    let (g, rg) = Csr::from_edges_and_rev(n, edges);
    let mut sorted = Vec::with_capacity(n);
    let mut cmp = vec![0; n];
    for i in 0..n {
        if cmp[i] == 0 {
            dfs1(i, &g, &mut sorted, &mut cmp);
        }
    }
    let mut out = Csr::with_capacity(n, n);
    for &i in sorted.iter().rev() {
        if cmp[i] == usize::MAX {
            out.push_empty();
            dfs2(i, &rg, &mut out, &mut cmp);
        }
    }
    out
}

fn dfs1(i: usize, g: &Csr<usize>, sorted: &mut Vec<usize>, cmp: &mut [usize]) {
    cmp[i] = usize::MAX;
    for &y in &g[i] {
        if cmp[y] == 0 {
            dfs1(y, g, sorted, cmp);
        }
    }
    sorted.push(i);
}

fn dfs2(i: usize, rg: &Csr<usize>, out: &mut Csr<usize>, cmp: &mut [usize]) {
    cmp[i] = out.len();
    out.last_mut().push(i);
    for &y in &rg[i] {
        if cmp[y] == usize::MAX {
            dfs2(y, rg, out, cmp);
        }
    }
}
