//! 根付き木をトポロジカルソートします。

/// 親を消します
pub fn remove_parent(g: &mut [Vec<usize>], parent: &[usize]) {
    g.iter_mut().enumerate().for_each(|(x, gx)| {
        if let Some(i) = gx.iter().position(|&y| y == parent[x]) {
            gx.swap_remove(i);
        };
    });
}

/// 根付き木をトポロジカルソートして、親を消します。
pub fn sort_tree_remove_parent(root: usize, g: &mut [Vec<usize>]) -> [Vec<usize>; 2] {
    let [ord, parent] = sort_tree(root, g);
    remove_parent(g, &parent);
    [ord, parent]
}

/// 根付き木をトポロジカルソートします。
pub fn sort_tree(root: usize, g: &[Vec<usize>]) -> [Vec<usize>; 2] { sort_tree_by(root, g, |x| *x) }

/// 根付き木をトポロジカルソートします。
pub fn sort_tree_by<E>(root: usize, g: &[Vec<E>], to: impl Fn(&E) -> usize) -> [Vec<usize>; 2] {
    let mut ord = Vec::new();
    let mut parent = vec![root; g.len()];
    sort_tree_impl(root, root, g, &to, &mut parent, &mut ord);
    [ord, parent]
}

fn sort_tree_impl<E>(
    x: usize,
    p: usize,
    g: &[Vec<E>],
    to: &impl Fn(&E) -> usize,
    parent: &mut [usize],
    ord: &mut Vec<usize>,
) {
    ord.push(x);
    parent[x] = p;
    g[x].iter()
        .map(to)
        .filter(|&y| y != p)
        .for_each(|y| sort_tree_impl(y, x, g, to, parent, ord))
}

#[cfg(test)]
mod tests {
    use super::sort_tree_remove_parent;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use randtools::Tree;
    use std::usize::MAX;

    #[test]
    fn test_sort_tree_remove_parent() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=5);
            let g = rng.sample(Tree(n));
            for root in 0..n {
                let mut g = g.clone();
                let [ord, parent] = sort_tree_remove_parent(root, &mut g);
                assert_eq!(ord.len(), n);
                assert_eq!(parent.len(), n);
                assert_eq!(root, parent[root]);
                assert_eq!(ord[0], root);
                let mut pos = vec![MAX; n];
                for (i, &o) in ord.iter().enumerate() {
                    pos[o] = i;
                }
                assert!(pos.iter().all(|&x| x != MAX));
                for (x, y) in g
                    .iter()
                    .enumerate()
                    .flat_map(|(x, gx)| gx.iter().map(move |&y| (x, y)))
                {
                    assert!(pos[x] < pos[y]);
                    assert_eq!(x, parent[y]);
                }
            }
        }
    }
}
