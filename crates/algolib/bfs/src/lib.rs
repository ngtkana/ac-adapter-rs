use std::collections::VecDeque;

pub fn sssp(g: &[Vec<usize>], s: usize) -> Vec<u32> {
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

pub fn sssp_restore(g: &[Vec<usize>], s: usize) -> (Vec<u32>, Vec<usize>) {
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

pub fn psp_path(g: &[Vec<usize>], s: usize, t: usize) -> Option<Vec<usize>> {
    let (dist, prv) = sssp_restore(&g, s);
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
    use super::{psp_path, sssp, sssp_restore};
    use rand::prelude::*;
    use randtools::{LogUniform, SimpleGraph};

    #[test]
    fn test_sssp() {
        let mut rng = StdRng::seed_from_u64(42);
        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2, 3000));
            let m = rng.sample(LogUniform(n - 1, (n * (n - 1) / 2 + 1).min(3000)));
            println!("Test {}, n = {}, m = {}", test_id, n, m);
            let g = rng.sample(SimpleGraph(n, m));
            let s = rng.gen_range(0, n);
            let t = rng.gen_range(0, n);

            // sssp
            let dist = sssp(&g, s);
            validate_dist(&g, &dist, s);

            // sssp_restore
            let prv = {
                let (dist1, prv) = sssp_restore(&g, s);
                assert_eq!(dist, dist1);
                prv
            };
            validate_prv(&dist, &prv, s);

            // psp_path
            let path = psp_path(&g, s, t);
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
}
