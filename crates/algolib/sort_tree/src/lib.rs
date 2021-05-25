pub fn sort_tree(root: usize, g: &[Vec<usize>]) -> [Vec<usize>; 2] {
    sort_tree_by(root, g, |x| *x)
}

pub fn sort_tree_by<E>(root: usize, g: &[Vec<E>], to: impl Fn(&E) -> usize) -> [Vec<usize>; 2] {
    let mut ord = Vec::new();
    let mut parent = vec![root; g.len()];
    sort_tree_impl(root, root, g, &to, &mut parent, &mut ord);
    [parent, ord]
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
    for y in g[x].iter().map(to).filter(|&y| y != p) {
        sort_tree_impl(y, x, g, to, parent, ord);
    }
}

#[cfg(test)]
mod tests {
    use super::sort_tree;
    use test_case::test_case;

    #[test_case(1, &[] => [vec![0], vec![0]])]
    #[test_case(2, &[[0, 1]] => [vec![0, 0], vec![0, 1]])]
    #[test_case(3, &[[0, 1], [1, 2]] => [vec![0, 0, 1], vec![0, 1, 2]])]
    #[test_case(3, &[[0, 2], [1, 2]] => [vec![0, 2, 0], vec![0, 2, 1]])]
    #[test_case(4, &[[0, 1], [1, 2], [2, 3]] => [vec![0, 0, 1, 2], vec![0, 1, 2, 3]])]
    #[test_case(4, &[[0, 1], [1, 2], [1, 3]] => [vec![0, 0, 1, 1], vec![0, 1, 2, 3]])]
    #[test_case(4, &[[0, 1], [1, 2], [0, 3]] => [vec![0, 0, 1, 0], vec![0, 1, 2, 3]])]
    #[test_case(4, &[[0, 1], [0, 2], [1, 3]] => [vec![0, 0, 0, 1], vec![0, 1, 3, 2]])]
    #[test_case(4, &[[0, 1], [0, 2], [0, 3]] => [vec![0, 0, 0, 0], vec![0, 1, 2, 3]])]
    #[test_case(4, &[[0, 2], [1, 2], [1, 3]] => [vec![0, 2, 0, 1], vec![0, 2, 1, 3]])]
    fn test_sort_tree(n: usize, edges: &[[usize; 2]]) -> [Vec<usize>; 2] {
        let mut g = vec![Vec::new(); n];
        for &[u, v] in edges {
            g[u].push(v);
            g[v].push(u);
        }
        sort_tree(0, &g)
    }
}
