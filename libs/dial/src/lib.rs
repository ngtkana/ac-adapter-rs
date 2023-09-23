use std::collections::VecDeque;

/// 一点からの距離配列を作ります。
pub fn calc_dist(s: usize, g: &[Vec<(usize, u32)>]) -> Vec<u32> {
    let mut dist = vec![std::u32::MAX; g.len()];
    dist[s] = 0;
    let mut chain = VecDeque::from(vec![vec![s]]);
    while let Some(mut stack) = chain.pop_front() {
        while let Some(x) = stack.pop() {
            let dx = dist[x];
            for &(y, w) in &g[x] {
                let dy = dx + w;
                if dy < dist[y] {
                    dist[y] = dy;
                    if w == 0 {
                        stack.push(y);
                    } else {
                        let offset = w as usize - 1;
                        while chain.len() < w as usize {
                            chain.push_back(Vec::new());
                        }
                        chain[offset].push(y);
                    }
                }
            }
        }
    }
    dist
}

/// 一点からの距離配列を作ります。
pub fn calc_dist_restore(s: usize, g: &[Vec<(usize, u32)>]) -> (Vec<u32>, Vec<usize>) {
    let mut dist = vec![std::u32::MAX; g.len()];
    let mut prv = vec![std::usize::MAX; g.len()];
    prv[s] = s;
    dist[s] = 0;
    let mut chain = VecDeque::from(vec![vec![s]]);
    while let Some(mut stack) = chain.pop_front() {
        while let Some(x) = stack.pop() {
            let dx = dist[x]; // TODO: ここで適宜 continue; をしないと壊れる気がします。
            for &(y, w) in &g[x] {
                let dy = dx + w;
                if dy < dist[y] {
                    dist[y] = dy;
                    prv[y] = x;
                    if w == 0 {
                        stack.push(y);
                    } else {
                        let offset = w as usize - 1;
                        while chain.len() < w as usize {
                            chain.push_back(Vec::new());
                        }
                        chain[offset].push(y);
                    }
                }
            }
        }
    }
    (dist, prv)
}

#[cfg(test)]
mod tests {
    use {
        rand::prelude::*,
        randtools::{LogUniform, SimpleDigraph},
        std::collections::HashMap,
    };

    #[test]
    fn test_graph() {
        let mut rng = StdRng::seed_from_u64(42);
        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2..1000));
            let m = rng.sample(LogUniform(n - 1..(n * (n - 1) / 2 + 1).min(1000)));
            println!("Test {}, n = {}, m = {}", test_id, n, m);
            // 重みなしの木を生成して……
            let g = rng.sample(SimpleDigraph(n, m));
            // 重みをつけます。
            let g = g
                .iter()
                .map(|v| {
                    v.iter()
                        .map(|&j| (j, rng.gen_range(0..30)))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let s = rng.gen_range(0..n);

            // calc_dist
            let dist = super::calc_dist(s, &g);
            validate_dist(&g, &dist, s);

            // calc_dist_restore
            let (dist_, prv) = super::calc_dist_restore(s, &g);
            assert_eq!(dist, dist_);
            let edges = g
                .iter()
                .enumerate()
                .flat_map(|(i, v)| v.iter().map(move |&(j, w)| ((i, j), w)))
                .collect::<HashMap<_, _>>();
            validate_dist_prv(&prv, &dist, &edges);
        }
    }

    fn validate_dist(g: &[Vec<(usize, u32)>], dist: &[u32], s: usize) {
        assert_eq!(dist[s], 0);
        for (u, v, w) in g
            .iter()
            .enumerate()
            .flat_map(|(i, v)| v.iter().map(move |&(j, w)| (i, j, w)))
        {
            assert!(dist[u].saturating_add(w) >= dist[v]);
        }
    }

    fn validate_dist_prv(prv: &[usize], dist: &[u32], edges: &HashMap<(usize, usize), u32>) {
        prv.iter().copied().enumerate().for_each(|(x, p)| {
            let expected = if x == p {
                0
            } else if p == std::usize::MAX {
                std::u32::MAX
            } else {
                dist[p] + edges.get(&(p, x)).unwrap()
            };
            assert_eq!(expected, dist[x]);
        });
    }
}
