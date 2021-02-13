//! Finds a maximum cardinality bipartite matching by Hopcroft―Karp's algorithm.
//!
//! # Basic usage
//!
//! Use a function [`hopkarp`] and get results via [`HopkarpResult`].
//!
//!
//! # Example
//!
//! ```
//! use hopkarp::hopkarp;
//!
//! let g = vec![vec![0, 1], vec![0]];
//! let result = hopkarp(2, &g);
//! assert_eq!(result.count, 2);
//! ```
//!
use std::collections::VecDeque;

/// Summary of the result of Hopcroft―Karp's algorithm.
///
/// # Maximum cardinality matching
///
/// For all `i < h` and `j < w`, it holds that `forward[i] == Some(j)` and
/// `Some(i) == backward[j]` if `(i, j)` is an edge of the resulting matching,
/// while `forward[i].is_none()` if `i` is not in match and `backward[j].is_none()` if `j` is not
/// in match.
///
///
/// # Minimum cut
///
/// The set of `i < h` s.t. `left[i]` is `true` and `j < w` s.t. `right[j]` is `true` consists the
/// set of vertices which are reachable from the source in the resulting residual graph.
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct HopkarpResult {
    /// Cardinality of a maximum cardinality bipartite matching.
    pub count: usize,
    pub forward: Box<[Option<usize>]>,
    pub backward: Box<[Option<usize>]>,
    pub left: Box<[bool]>,
    pub right: Box<[bool]>,
}

/// Takes a *forward* adjacency list and the length of the right side, and returns a maximum
/// cardinality bipartite matching.
///
/// # Complexity
///
/// O ( √V E ) in worst.
pub fn hopkarp(w: usize, graph: &[Vec<usize>]) -> HopkarpResult {
    let h = graph.len();
    let mut forward = vec![None; h].into_boxed_slice();
    let mut backward = vec![None; w].into_boxed_slice();
    let (left, right) = loop {
        let dist = bfs(graph, &forward, &backward);
        if !dfs(&graph, &dist, &mut forward, &mut backward) {
            break construct_minimum_cut(graph, &dist, &backward);
        }
    };
    let count = forward.iter().filter(|b| b.is_some()).count();
    HopkarpResult {
        count,
        forward,
        backward,
        left,
        right,
    }
}

fn construct_minimum_cut(
    graph: &[Vec<usize>],
    dist: &[u32],
    backward: &[Option<usize>],
) -> (Box<[bool]>, Box<[bool]>) {
    use std::u32::MAX;
    let left = dist
        .iter()
        .map(|&x| x != MAX)
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let mut right = vec![false; backward.len()].into_boxed_slice();
    for x in left.iter().enumerate().filter(|&(_, &b)| b).map(|(x, _)| x) {
        graph[x]
            .iter()
            .copied()
            .filter(|&y| backward[y] != Some(x))
            .for_each(|y| right[y] = true);
    }
    (left, right)
}

fn dfs(
    graph: &[Vec<usize>],
    dist: &[u32],
    forward: &mut [Option<usize>],
    backward: &mut [Option<usize>],
) -> bool {
    fn rec(
        x: usize,
        graph: &[Vec<usize>],
        dist: &[u32],
        used: &mut [bool],
        forward: &mut [Option<usize>],
        backward: &mut [Option<usize>],
    ) -> bool {
        used[x] = true;
        for &y in &graph[x] {
            let found = if let Some(z) = backward[y] {
                !used[z] && dist[x] + 1 == dist[z] && rec(z, graph, dist, used, forward, backward)
            } else {
                true
            };
            if found {
                backward[y] = Some(x);
                forward[x] = Some(y);
                return true;
            }
        }
        false
    }
    let mut has_aug = false;
    let mut used = vec![false; forward.len()];
    for x in 0..used.len() {
        if forward[x].is_none() {
            has_aug |= rec(x, graph, dist, &mut used, forward, backward);
        }
    }
    has_aug
}

fn bfs(graph: &[Vec<usize>], forward: &[Option<usize>], backward: &[Option<usize>]) -> Vec<u32> {
    use std::u32::MAX;
    let mut dist = vec![MAX; forward.len()];
    let mut queue = forward
        .iter()
        .enumerate()
        .filter(|&(_, b)| b.is_none())
        .map(|(i, _)| i)
        .inspect(|&i| dist[i] = 0)
        .collect::<VecDeque<_>>();
    while let Some(x) = queue.pop_front() {
        for &y in &graph[x] {
            if let Some(z) = backward[y] {
                if dist[z] == MAX {
                    dist[z] = dist[x] + 1;
                    queue.push_back(z);
                }
            }
        }
    }
    dist
}

#[cfg(test)]
mod tests {
    use {
        super::{hopkarp, HopkarpResult},
        itertools::Itertools as _,
        rand::{distributions::Bernoulli, prelude::StdRng, Rng, SeedableRng},
        std::iter::repeat_with,
        test_case::test_case,
    };

    #[test]
    fn test_hopkarp_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let h = rng.gen_range(1..8);
            let w = rng.gen_range(1..8);
            let graph = repeat_with(|| {
                (&mut rng)
                    .sample_iter(Bernoulli::new(0.5).unwrap())
                    .take(w)
                    .enumerate()
                    .filter(|&(_, b)| b)
                    .map(|(y, _)| y)
                    .collect_vec()
            })
            .take(h)
            .collect_vec();
            let result = hopkarp(w, &graph);
            hopkarp_validate(&graph, &result);
        }
    }

    fn hopkarp_validate(graph: &[Vec<usize>], result: &HopkarpResult) {
        let HopkarpResult {
            count,
            forward,
            backward,
            left,
            right,
        } = result;

        // Check consistency among fields.
        forward
            .iter()
            .enumerate()
            .filter_map(|(x, y)| y.map(|y| (x, y)))
            .for_each(|(x, y)| assert_eq!(backward[y], Some(x)));
        backward
            .iter()
            .enumerate()
            .filter_map(|(y, x)| x.map(|x| (x, y)))
            .for_each(|(x, y)| assert_eq!(forward[x], Some(y)));
        assert_eq!(forward.iter().filter(|b| b.is_some()).count(), *count,);
        assert_eq!(backward.iter().filter(|b| b.is_some()).count(), *count,);

        // Collect edges
        let match_edges = backward
            .iter()
            .enumerate()
            .filter_map(|(y, x)| x.map(|x| (x, y)))
            .collect::<Vec<_>>();
        let unmach_edges = graph
            .iter()
            .enumerate()
            .map(|(x, v)| v.iter().map(move |&y| (x, y)))
            .flatten()
            .filter(|&(x, y)| backward[y] != Some(x))
            .collect::<Vec<_>>();

        // Check that the residual capacity of the cut is zero.
        match_edges
            .iter()
            .for_each(|&(x, y)| assert!(left[x] || !right[y]));
        unmach_edges
            .iter()
            .for_each(|&(x, y)| assert!(!left[x] || right[y]));

        // Check that the capacity of the cut equals count.
        let capacity = left
            .iter()
            .filter(|&&b| !b)
            .chain(right.iter().filter(|&&b| b))
            .count();
        assert_eq!(*count, capacity);
    }

    #[test_case(3, "000000" => 0)]
    #[test_case(3, "000001" => 1)]
    #[test_case(3, "000010" => 1)]
    #[test_case(3, "000011" => 1)]
    #[test_case(3, "000100" => 1)]
    #[test_case(3, "000101" => 1)]
    #[test_case(3, "000110" => 1)]
    #[test_case(3, "000111" => 1)]
    #[test_case(3, "001000" => 1)]
    #[test_case(3, "001001" => 1)]
    #[test_case(3, "001010" => 2)]
    #[test_case(3, "001011" => 2)]
    #[test_case(3, "001100" => 2)]
    #[test_case(3, "001101" => 2)]
    #[test_case(3, "001110" => 2)]
    #[test_case(3, "001111" => 2)]
    #[test_case(3, "010000" => 1)]
    #[test_case(3, "010001" => 2)]
    #[test_case(3, "010010" => 1)]
    #[test_case(3, "010011" => 2)]
    #[test_case(3, "010100" => 2)]
    #[test_case(3, "010101" => 2)]
    #[test_case(3, "010110" => 2)]
    #[test_case(3, "010111" => 2)]
    #[test_case(3, "011000" => 1)]
    #[test_case(3, "011001" => 2)]
    #[test_case(3, "011010" => 2)]
    #[test_case(3, "011011" => 2)]
    #[test_case(3, "011100" => 2)]
    #[test_case(3, "011101" => 2)]
    #[test_case(3, "011110" => 2)]
    #[test_case(3, "011111" => 2)]
    #[test_case(3, "100000" => 1)]
    #[test_case(3, "100001" => 2)]
    #[test_case(3, "100010" => 2)]
    #[test_case(3, "100011" => 2)]
    #[test_case(3, "100100" => 1)]
    #[test_case(3, "100101" => 2)]
    #[test_case(3, "100110" => 2)]
    #[test_case(3, "100111" => 2)]
    #[test_case(3, "101000" => 1)]
    #[test_case(3, "101001" => 2)]
    #[test_case(3, "101010" => 2)]
    #[test_case(3, "101011" => 2)]
    #[test_case(3, "101100" => 2)]
    #[test_case(3, "101101" => 2)]
    #[test_case(3, "101110" => 2)]
    #[test_case(3, "101111" => 2)]
    #[test_case(3, "110000" => 1)]
    #[test_case(3, "110001" => 2)]
    #[test_case(3, "110010" => 2)]
    #[test_case(3, "110011" => 2)]
    #[test_case(3, "110100" => 2)]
    #[test_case(3, "110101" => 2)]
    #[test_case(3, "110110" => 2)]
    #[test_case(3, "110111" => 2)]
    #[test_case(3, "111000" => 1)]
    #[test_case(3, "111001" => 2)]
    #[test_case(3, "111010" => 2)]
    #[test_case(3, "111011" => 2)]
    #[test_case(3, "111100" => 2)]
    #[test_case(3, "111101" => 2)]
    #[test_case(3, "111110" => 2)]
    #[test_case(3, "111111" => 2)]
    fn test_hopkarp_hand_exhaustive(w: usize, adj: &str) -> usize {
        let adj = adj
            .chars()
            .map(|c| match c {
                '0' => false,
                '1' => true,
                _ => panic!(),
            })
            .collect_vec();
        let graph = adj
            .chunks_exact(w)
            .map(|v| {
                v.iter()
                    .enumerate()
                    .filter(|&(_, &b)| b)
                    .map(|(i, _)| i)
                    .collect_vec()
            })
            .collect_vec();
        let result = hopkarp(w, &graph);
        hopkarp_validate(&graph, &result);
        result.count
    }
}
