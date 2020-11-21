use std::collections::VecDeque;

pub fn calc_dist(s: usize, g: &[Vec<usize>]) -> Vec<u32> {
    let mut dist = vec![std::u32::MAX; g.len()];
    dist[s] = 0;
    let mut queue = VecDeque::from(vec![s]);
    while let Some(x) = queue.pop_front() {
        for &y in &g[x] {
            if dist[y] == std::u32::MAX {
                dist[y] = dist[x] + 1;
                queue.push_back(y);
            }
        }
    }
    dist
}

pub fn tree_diamter(g: &[Vec<usize>]) -> ([usize; 2], u32) {
    assert_eq!(g.iter().flatten().count(), (g.len() - 1) * 2);
    let dist = calc_dist(0, &g);
    let &diam = dist.iter().max().unwrap();
    let x = dist.iter().position(|&d| d == diam).unwrap();
    let dist = calc_dist(x, &g);
    let &diam = dist.iter().max().unwrap();
    let y = dist.iter().position(|&d| d == diam).unwrap();
    ([x, y], diam)
}

pub fn calc_dist_restore(s: usize, g: &[Vec<usize>]) -> (Vec<u32>, Vec<usize>) {
    let mut dist = vec![std::u32::MAX; g.len()];
    let mut prv = vec![std::usize::MAX; g.len()];
    dist[s] = 0;
    prv[s] = s;
    let mut queue = VecDeque::from(vec![s]);
    while let Some(x) = queue.pop_front() {
        for &y in &g[x] {
            if dist[y] == std::u32::MAX {
                dist[y] = dist[x] + 1;
                prv[y] = x;
                queue.push_back(y);
            }
        }
    }
    (dist, prv)
}

pub fn find_path(s: usize, t: usize, g: &[Vec<usize>]) -> Option<Vec<usize>> {
    let (dist, prv) = calc_dist_restore(s, &g);
    if dist[t] == std::u32::MAX {
        None
    } else {
        let mut res = vec![t];
        loop {
            let x = *res.last().unwrap();
            if x == s {
                res.reverse();
                return Some(res);
            }
            res.push(prv[x]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{calc_dist, calc_dist_restore, find_path};
    use rand::prelude::*;
    use randtools::{LogUniform, SimpleGraph, Tree};

    // -- graph
    #[test]
    fn test_graph() {
        let mut rng = StdRng::seed_from_u64(42);
        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2, 3000));
            let m = rng.sample(LogUniform(n - 1, (n * (n - 1) / 2 + 1).min(3000)));
            println!("Test {}, n = {}, m = {}", test_id, n, m);
            let g = rng.sample(SimpleGraph(n, m));
            let s = rng.gen_range(0, n);
            let t = rng.gen_range(0, n);

            // calc_dist
            let dist = calc_dist(s, &g);
            validate_dist(&g, &dist, s);

            // calc_dist_restore
            let prv = {
                let (dist1, prv) = calc_dist_restore(s, &g);
                assert_eq!(dist, dist1);
                prv
            };
            validate_prv(&dist, &prv, s);

            // find_path
            let path = find_path(s, t, &g);
            if let Some(path) = path {
                validate_path(&dist, &path, s, t);
            } else {
                assert_eq!(dist[t], std::u32::MAX);
            }
        }
    }

    fn validate_dist(g: &[Vec<usize>], dist: &[u32], s: usize) {
        assert_eq!(dist[s], 0);
        for (u, v) in g
            .iter()
            .enumerate()
            .map(|(i, v)| v.iter().map(move |&j| (i, j)))
            .flatten()
        {
            assert!(dist[u] == dist[v] || dist[u] + 1 == dist[v] || dist[u] == dist[v] + 1);
        }
    }

    fn validate_prv(dist: &[u32], prv: &[usize], s: usize) {
        assert_eq!(prv[s], s);
        (0..dist.len())
            .filter(|&i| i != s && prv[i] != std::usize::MAX)
            .for_each(|i| assert_eq!(dist[prv[i]] + 1, dist[i]))
    }

    fn validate_path(dist: &[u32], path: &[usize], s: usize, t: usize) {
        assert_eq!(*path.first().unwrap(), s);
        assert_eq!(*path.last().unwrap(), t);
        path.iter()
            .enumerate()
            .for_each(|(i, &x)| assert_eq!(dist[x], i as u32));
    }

    // -- tree
    #[test]
    fn test_tree() {
        let mut rng = StdRng::seed_from_u64(42);
        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2, 20));
            println!("Test {}, n = {}", test_id, n);
            let g = rng.sample(Tree(n));
            let (_, result) = super::tree_diamter(&g);
            let (_, expected) = brute_tree_diameter(&g);
            assert_eq!(result, expected);
        }
    }

    fn brute_tree_diameter(g: &[Vec<usize>]) -> ([usize; 2], u32) {
        let n = g.len();
        let mut dist = vec![vec![std::u32::MAX; n]; n];
        (0..n).for_each(|i| dist[i][i] = 0);
        g.iter()
            .enumerate()
            .map(|(i, v)| v.iter().copied().map(move |j| (i, j)))
            .flatten()
            .for_each(|(i, j)| {
                dist[i][j] = 1;
                dist[j][i] = 1
            });
        for k in 0..n {
            for i in 0..n {
                for j in 0..n {
                    let x = dist[i][k].saturating_add(dist[k][j]).min(dist[i][j]);
                    dist[i][j] = x;
                }
            }
        }
        assert!(dist.iter().flatten().all(|&x| x != u32::MAX));
        dist.iter()
            .enumerate()
            .map(|(i, v)| v.iter().copied().enumerate().map(move |(j, x)| (i, j, x)))
            .flatten()
            .map(|(i, j, x)| ([i, j], x))
            .max_by_key(|&(_, x)| x)
            .unwrap()
    }
}
