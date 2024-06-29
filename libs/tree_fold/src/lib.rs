//! 2-way tree DP
//!
//! # Notation
//!
//! - $V$: vertex type
//! - $T$: (rooted) tree type
//! - $F$: (rooted) forest type (with ordering of the trees)
//!
//! # Forest Operations
//!
//! | | type | description |
//! | - | - | - |
//! | `up` | $F \times V \to T \to F$ | join by a root |
//! | `mul` | $F \times F \to F$ | concatenate two forests |
//! | `identity` | $* \to F$ | empty forest |
//!
//! # Parameters
//!
//! - `g[i]`: children of `i`
//! - `sorted`: a permutation of the vertices with "parent-first" condition
//!
//! # Return value
//!
//! | | description |
//! | - | - |
//! | `upper` | $f(\phi(T_i^\triangle))$ |
//! | `lower` | $\prod_{j \lessdot i} f(\phi(T_j^\blacktriangledown))$ |
//! | `branch` | $f(\phi(T_i^\blacktriangledown))$ |
//!
//! where
//!
//! $$
//! \phi(T_i^\triangle) = g\left( \prod_{j \lessdot i} f(T_j^\triangle) \right)
//! $$

/// Operations
///
/// # Notation
///
/// - $V$: vertex type
/// - $T$: (rooted) tree type
/// - $F$: (rooted) forest type (with ordering of the trees)
pub trait Op: Sized {
    /// A monoid $M$.
    type Value: Clone;

    /// $F \times V \to T \to F$: join by a root
    fn up(&self, value: &Self::Value, root: usize) -> Self::Value;

    /// $F \times F \to F$: concatenate two forests
    fn mul(&self, lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    /// $* \to F$: empty forest
    fn identity(&self) -> Self::Value;

    /// Performs 2-way tree DP
    fn two_way_tree_fold(
        &self,
        g: &[Vec<usize>],
        sorted: &[usize],
    ) -> TwoWayTreeFoldResult<Self::Value> {
        two_way_tree_fold(self, g, sorted)
    }
}

/// The return value of [`Op::two_way_tree_fold()`] ans [`two_way_tree_fold()`]
pub struct TwoWayTreeFoldResult<T> {
    /// $f(\phi(T_i^\triangle))$
    pub upper: Vec<T>,
    /// $\prod_{j \lessdot i} f(\phi(T_j^\blacktriangledown))$
    pub lower: Vec<T>,
    /// $f(\phi(T_i^\blacktriangledown))$
    pub branch: Vec<T>,
}

/// Performs 2-way tree DP
///
/// # Parameters
///
/// - `g[i]`: children of `i`
/// - `sorted`: a permutation of the vertices with "parent-first" condition
///
/// # Return value
///
/// | | description |
/// | - | - |
/// | `upper` | $f(\phi(T_i^\triangle))$ |
/// | `lower` | $\prod_{j \lessdot i} f(\phi(T_j^\blacktriangledown))$ |
/// | `branch` | $f(\phi(T_i^\blacktriangledown))$ |
///
/// where
///
/// $$
/// \phi(T_i^\triangle) = g\left( \prod_{j \lessdot i} f(T_j^\triangle) \right)
/// $$
pub fn two_way_tree_fold<O: Op>(
    o: &O,
    g: &[Vec<usize>],
    sorted: &[usize],
) -> TwoWayTreeFoldResult<O::Value> {
    let n = g.len();
    let mut lower = vec![o.identity(); n];
    let mut branch = vec![o.identity(); n];
    for &i in sorted.iter().rev() {
        for &j in &g[i] {
            lower[i] = o.mul(&lower[i], &branch[j]);
        }
        branch[i] = o.up(&lower[i], i);
    }
    let mut upper = vec![o.identity(); n];
    for &i in sorted {
        let mut suffix = upper[i].clone();
        for &j in g[i].iter().rev() {
            upper[j] = suffix.clone();
            suffix = o.mul(&branch[j], &suffix);
        }
        let mut prefix = o.identity();
        for &j in &g[i] {
            upper[j] = o.up(&o.mul(&upper[j], &prefix), i);
            prefix = o.mul(&prefix, &branch[j]);
        }
    }
    TwoWayTreeFoldResult {
        lower,
        branch,
        upper,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::BinaryHeap;

    struct GenratedTree {
        g: Vec<Vec<usize>>,
        sorted: Vec<usize>,
        parent: Vec<usize>,
    }

    fn gen_tree(rng: &mut StdRng, n: usize) -> GenratedTree {
        let mut g = vec![Vec::new(); n];
        let rev_prufer = (0..n - 1)
            .map(|i| if i == n - 2 { 0 } else { rng.gen_range(0..n) })
            .collect::<Vec<_>>();
        let mut count = vec![0; n];
        for &y in &rev_prufer {
            count[y] += 1;
        }
        let mut heap = (0..n).filter(|&y| count[y] == 0).collect::<BinaryHeap<_>>();
        for &y in &rev_prufer {
            let x = heap.pop().unwrap();
            g[x].push(y);
            g[y].push(x);
            count[y] -= 1;
            if count[y] == 0 {
                heap.push(y);
            }
        }
        let root = rng.gen_range(0..n);
        let mut stack = vec![root];
        let mut parent = vec![usize::MAX; n];
        let mut sorted = Vec::new();
        parent[root] = root;
        while let Some(i) = stack.pop() {
            sorted.push(i);
            g[i].retain(|&j| parent[i] != j);
            for &j in &g[i] {
                stack.push(j);
                parent[j] = i;
            }
        }
        GenratedTree { g, sorted, parent }
    }

    #[test]
    fn test_subtree() {
        struct O;
        #[derive(Clone, PartialEq)]
        struct Tree {
            root: usize,
            child: Vec<Self>,
        }
        impl std::fmt::Debug for Tree {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple("")
                    .field(&self.root)
                    .field(&self.child)
                    .finish()
            }
        }
        impl Op for O {
            type Value = Vec<Tree>;

            fn up(&self, value: &Self::Value, root: usize) -> Self::Value {
                vec![Tree {
                    root,
                    child: value.clone(),
                }]
            }

            fn identity(&self) -> Self::Value {
                Vec::new()
            }

            fn mul(&self, lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                lhs.iter().cloned().chain(rhs.iter().cloned()).collect()
            }
        }

        fn subtree(i: usize, p: usize, g: &[Vec<usize>]) -> Tree {
            Tree {
                root: i,
                child: match g[i].iter().position(|&j| j == p) {
                    None => g[i].iter().map(|&j| subtree(j, i, g)).collect(),
                    Some(e) => g[i][e + 1..]
                        .iter()
                        .chain(&g[i][..e])
                        .map(|&j| subtree(j, i, g))
                        .collect(),
                },
            }
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=30);
            let GenratedTree {
                g, sorted, parent, ..
            } = gen_tree(&mut rng, n);
            let TwoWayTreeFoldResult {
                lower,
                branch,
                upper,
            } = O.two_way_tree_fold(&g, &sorted);
            let mut g1 = g.clone();
            for (i, &p) in parent.iter().enumerate() {
                if i != p {
                    g1[i].push(p);
                }
            }
            for (i, &p) in parent.iter().enumerate() {
                assert_eq!(
                    lower[i],
                    g[i].iter().map(|&j| subtree(j, i, &g)).collect::<Vec<_>>()
                );
                assert_eq!(branch[i], vec![subtree(i, p, &g)]);
                assert_eq!(
                    upper[i],
                    if i == p { Vec::new() } else { vec![subtree(p, i, &g1)] }
                );
            }
        }
    }
}
