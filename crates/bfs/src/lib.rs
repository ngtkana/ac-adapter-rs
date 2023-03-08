use std::collections::VecDeque;

/// 木の直径を一つ探し、その両端点とその間の距離を返します。
pub fn tree_diamter(g: &[Vec<usize>]) -> ([usize; 2], u32) {
    assert_eq!(g.iter().flatten().count(), (g.len() - 1) * 2);
    let dist = calc_dist(0, g);
    let &diam = dist.iter().max().unwrap();
    let x = dist.iter().position(|&d| d == diam).unwrap();
    let dist = calc_dist(x, g);
    let &diam = dist.iter().max().unwrap();
    let y = dist.iter().position(|&d| d == diam).unwrap();
    ([x, y], diam)
}

/// 木の直径を一つ探し、頂点列とパスの長さ（辺の個数）を返します。
pub fn tree_diamter_restore(g: &[Vec<usize>]) -> (Vec<usize>, u32) {
    assert_eq!(g.iter().flatten().count(), (g.len() - 1) * 2);
    let dist = calc_dist(0, g);
    let &diam = dist.iter().max().unwrap();
    let x = dist.iter().position(|&d| d == diam).unwrap();
    let (dist, prv) = calc_dist_restore(x, g);
    let &diam = dist.iter().max().unwrap();
    let mut res = vec![dist.iter().position(|&d| d == diam).unwrap()];
    loop {
        let x = *res.last().unwrap();
        if dist[x] == 0 {
            break;
        }
        res.push(prv[x]);
    }
    (res, diam)
}

/// 一点からの距離配列を作ります。
pub fn calc_dist(start: usize, g: &[Vec<usize>]) -> Vec<u32> {
    let mut dist = vec![std::u32::MAX; g.len()];
    dist[start] = 0;
    let mut queue = VecDeque::from(vec![start]);
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

/// 一点からの距離配列と、前者配列を作ります。始点の前者は自分自身です。
pub fn calc_dist_restore(start: usize, g: &[Vec<usize>]) -> (Vec<u32>, Vec<usize>) {
    let mut dist = vec![std::u32::MAX; g.len()];
    let mut prv = vec![std::usize::MAX; g.len()];
    dist[start] = 0;
    prv[start] = start;
    let mut queue = VecDeque::from(vec![start]);
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

/// start から end が到達可能ならば最短経路の頂点列を返し、不能ならば `None` を返します。
pub fn find_path(start: usize, end: usize, g: &[Vec<usize>]) -> Option<Vec<usize>> {
    let (dist, prv) = calc_dist_restore(start, g);
    if dist[end] == std::u32::MAX {
        None
    } else {
        let mut res = vec![end];
        loop {
            let x = *res.last().unwrap();
            if x == start {
                res.reverse();
                return Some(res);
            }
            res.push(prv[x]);
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{calc_dist, calc_dist_restore, find_path},
        rand::prelude::*,
        randtools::{LogUniform, SimpleGraph, Tree},
        std::collections::HashSet,
    };

    // -- graph
    #[test]
    fn test_graph() {
        let mut rng = StdRng::seed_from_u64(42);
        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2..3000));
            let m = rng.sample(LogUniform(n - 1..(n * (n - 1) / 2 + 1).min(3000)));
            println!("Test {}, n = {}, m = {}", test_id, n, m);
            let g = rng.sample(SimpleGraph(n, m));
            let start = rng.gen_range(0..n);
            let end = rng.gen_range(0..n);

            // calc_dist
            let dist = calc_dist(start, &g);
            validate_dist(&g, &dist, start);

            // calc_dist_restore
            let prv = {
                let (dist1, prv) = calc_dist_restore(start, &g);
                assert_eq!(dist, dist1);
                prv
            };
            validate_prv(&dist, &prv, start);

            // find_path
            let path = find_path(start, end, &g);
            if let Some(path) = path {
                validate_path(&dist, &path, start, end);
            } else {
                assert_eq!(dist[end], std::u32::MAX);
            }
        }
    }

    fn validate_dist(g: &[Vec<usize>], dist: &[u32], start: usize) {
        assert_eq!(dist[start], 0);
        for (u, v) in g
            .iter()
            .enumerate()
            .flat_map(|(i, v)| v.iter().map(move |&j| (i, j)))
        {
            assert!(dist[u] == dist[v] || dist[u] + 1 == dist[v] || dist[u] == dist[v] + 1);
        }
    }

    fn validate_prv(dist: &[u32], prv: &[usize], start: usize) {
        assert_eq!(prv[start], start);
        (0..dist.len())
            .filter(|&i| i != start && prv[i] != std::usize::MAX)
            .for_each(|i| assert_eq!(dist[prv[i]] + 1, dist[i]))
    }

    fn validate_path(dist: &[u32], path: &[usize], start: usize, end: usize) {
        assert_eq!(*path.first().unwrap(), start);
        assert_eq!(*path.last().unwrap(), end);
        path.iter()
            .enumerate()
            .for_each(|(i, &x)| assert_eq!(dist[x], i as u32));
    }

    // -- tree
    #[test]
    fn test_tree() {
        let mut rng = StdRng::seed_from_u64(42);
        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2..20));
            println!("Test {}, n = {}", test_id, n);
            let g = rng.sample(Tree(n));

            // 直径
            let (_, diam) = super::tree_diamter(&g);
            let (_, expected) = brute_tree_diameter(&g);
            assert_eq!(diam, expected);

            // 復元
            let (path, _) = super::tree_diamter_restore(&g);
            assert_eq!(path.len(), diam as usize + 1);
            let edges = g
                .iter()
                .enumerate()
                .flat_map(|(i, v)| v.iter().map(move |&j| (i, j)))
                .collect::<HashSet<_>>();
            for i in 1..path.len() {
                debug_assert!(edges.contains(&(path[i - 1], path[i])));
            }
        }
    }

    fn brute_tree_diameter(g: &[Vec<usize>]) -> ([usize; 2], u32) {
        let n = g.len();
        let mut dist = vec![vec![std::u32::MAX; n]; n];
        (0..n).for_each(|i| dist[i][i] = 0);
        g.iter()
            .enumerate()
            .flat_map(|(i, v)| v.iter().copied().map(move |j| (i, j)))
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
        assert!(dist.iter().flatten().all(|&x| x != std::u32::MAX));
        dist.iter()
            .enumerate()
            .flat_map(|(i, v)| v.iter().copied().enumerate().map(move |(j, x)| (i, j, x)))
            .map(|(i, j, x)| ([i, j], x))
            .max_by_key(|&(_, x)| x)
            .unwrap()
    }
}
