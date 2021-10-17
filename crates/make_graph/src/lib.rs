//! 辺全体のスライスから、グラフの隣接リストを作ります。
//!

/// `(u, v)` の形の辺から無向グラフを構築します。
pub fn tuple_make_undirected(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
    make_undirected_by(n, edges, |&(u, v)| [u, v])
}
/// `[u, v]` の形の辺から無向グラフを構築します。
pub fn array_make_undirected(n: usize, edges: &[[usize; 2]]) -> Vec<Vec<usize>> {
    make_undirected_by(n, edges, |&[u, v]| [u, v])
}
/// 一般の形の辺から（重みなし）無向グラフを構築します。
pub fn make_undirected_by<E>(
    n: usize,
    edges: &[E],
    f: impl Fn(&E) -> [usize; 2],
) -> Vec<Vec<usize>> {
    let mut g = vec![Vec::new(); n];
    for [u, v] in edges.iter().map(f) {
        g[u].push(v);
        g[v].push(u);
    }
    g
}

/// `(u, v)` の形の辺から有向グラフを構築します。
pub fn tuple_make_directed(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
    make_directed_by(n, edges, |&(u, v)| [u, v])
}
/// `[u, v]` の形の辺から有向グラフを構築します。
pub fn array_make_directed(n: usize, edges: &[[usize; 2]]) -> Vec<Vec<usize>> {
    make_directed_by(n, edges, |&[u, v]| [u, v])
}
/// 一般の形の辺から（重みなし）有向グラフを構築します。
pub fn make_directed_by<E>(n: usize, edges: &[E], f: impl Fn(&E) -> [usize; 2]) -> Vec<Vec<usize>> {
    let mut g = vec![Vec::new(); n];
    edges.iter().map(f).for_each(|[u, v]| g[u].push(v));
    g
}

/// `(u, v, w)` の形の辺から重み付き無向グラフを構築します。
pub fn tuple_make_undirected_weighted<T: Copy>(
    n: usize,
    edges: &[(usize, usize, T)],
) -> Vec<Vec<(usize, T)>> {
    make_undirected_weighted_by(n, edges, |&(u, v, x)| ([u, v], x))
}
/// `([u, v], w)` の形の辺から重み付き無向グラフを構築します。
pub fn array_make_undirected_weighted<T: Copy>(
    n: usize,
    edges: &[([usize; 2], T)],
) -> Vec<Vec<(usize, T)>> {
    make_undirected_weighted_by(n, edges, |&([u, v], x)| ([u, v], x))
}
/// 一般の形の辺から重みつき無向グラフを構築します。
pub fn make_undirected_weighted_by<E, T: Copy>(
    n: usize,
    edges: &[E],
    f: impl Fn(&E) -> ([usize; 2], T),
) -> Vec<Vec<(usize, T)>> {
    let mut g = vec![Vec::new(); n];
    for ([u, v], x) in edges.iter().map(f) {
        g[u].push((v, x));
        g[v].push((u, x));
    }
    g
}

/// `(u, v, w)` の形の辺から重み付き有向グラフを構築します。
pub fn tuple_make_directed_weighted<T: Copy>(
    n: usize,
    edges: &[(usize, usize, T)],
) -> Vec<Vec<(usize, T)>> {
    make_directed_weighted_by(n, edges, |&(u, v, x)| ([u, v], x))
}
/// `([u, v], w)` の形の辺から重み付き有向グラフを構築します。
pub fn array_make_directed_weighted<T: Copy>(
    n: usize,
    edges: &[([usize; 2], T)],
) -> Vec<Vec<(usize, T)>> {
    make_directed_weighted_by(n, edges, |&([u, v], x)| ([u, v], x))
}
/// 一般の形の辺から重み付き有向グラフを構築します。
pub fn make_directed_weighted_by<E, T: Copy>(
    n: usize,
    edges: &[E],
    f: impl Fn(&E) -> ([usize; 2], T),
) -> Vec<Vec<(usize, T)>> {
    let mut g = vec![Vec::new(); n];
    edges
        .iter()
        .map(f)
        .for_each(|([u, v], w)| g[u].push((v, w)));
    g
}

#[cfg(test)]
mod tests {
    use super::{
        array_make_directed, array_make_directed_weighted, array_make_undirected,
        array_make_undirected_weighted, tuple_make_directed, tuple_make_directed_weighted,
        tuple_make_undirected, tuple_make_undirected_weighted,
    };

    #[test]
    fn test_array_make_undirected() {
        let g = array_make_undirected(4, &[[0, 1], [0, 2], [2, 3]]);
        assert_eq!(g.as_slice(), &[vec![1, 2], vec![0], vec![0, 3], vec![2],]);
    }

    #[test]
    fn test_tuple_make_undirected() {
        let g = tuple_make_undirected(4, &[(0, 1), (0, 2), (2, 3)]);
        assert_eq!(g.as_slice(), &[vec![1, 2], vec![0], vec![0, 3], vec![2],]);
    }

    #[test]
    fn test_array_make_directed() {
        let g = array_make_directed(4, &[[0, 1], [0, 2], [2, 3]]);
        assert_eq!(
            g.as_slice(),
            &[vec![1, 2], Vec::new(), vec![3], Vec::new(),]
        );
    }

    #[test]
    fn test_tuple_make_directed() {
        let g = tuple_make_directed(4, &[(0, 1), (0, 2), (2, 3)]);
        assert_eq!(
            g.as_slice(),
            &[vec![1, 2], Vec::new(), vec![3], Vec::new(),]
        );
    }

    #[test]
    fn test_array_make_undirected_weighted() {
        let g = array_make_undirected_weighted(4, &[([0, 1], 10), ([0, 2], 20), ([2, 3], 30)]);
        assert_eq!(
            g.as_slice(),
            &[
                vec![(1, 10), (2, 20)],
                vec![(0, 10)],
                vec![(0, 20), (3, 30)],
                vec![(2, 30)],
            ]
        );
    }

    #[test]
    fn test_tuple_make_undirected_weighted() {
        let g = tuple_make_undirected_weighted(4, &[(0, 1, 10), (0, 2, 20), (2, 3, 30)]);
        assert_eq!(
            g.as_slice(),
            &[
                vec![(1, 10), (2, 20)],
                vec![(0, 10)],
                vec![(0, 20), (3, 30)],
                vec![(2, 30)],
            ]
        );
    }

    #[test]
    fn test_array_make_directed_weighted() {
        let g = array_make_directed_weighted(4, &[([0, 1], 10), ([0, 2], 20), ([2, 3], 30)]);
        assert_eq!(
            g.as_slice(),
            &[
                vec![(1, 10), (2, 20)],
                Vec::new(),
                vec![(3, 30)],
                Vec::new(),
            ]
        );
    }

    #[test]
    fn test_tuple_make_directed_weighted() {
        let g = tuple_make_directed_weighted(4, &[(0, 1, 10), (0, 2, 20), (2, 3, 30)]);
        assert_eq!(
            g.as_slice(),
            &[
                vec![(1, 10), (2, 20)],
                Vec::new(),
                vec![(3, 30)],
                Vec::new(),
            ]
        );
    }
}
