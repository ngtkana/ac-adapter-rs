//! CAUTION: `RadixHeap` fails in testst!
#![allow(deprecated)]

#[deprecated]
/// 一点からの距離配列を作ります。
pub fn calc_dist(s: usize, g: &[Vec<(usize, u32)>]) -> Vec<u32> {
    let mut dist = vec![u32::MAX; g.len()];
    dist[s] = 0;
    let mut heap = radix_heap::RadixHeap::new();
    heap.push(0, s);
    while let Some((dx, x)) = heap.pop() {
        if dx <= dist[x] {
            for &(y, w) in &g[x] {
                let dy = dx + w;
                if dy < dist[y] {
                    dist[y] = dy;
                    heap.push(dy, y);
                }
            }
        }
    }
    dist
}

/// 一点からの距離配列を作ります。
pub fn calc_dist_restore(s: usize, g: &[Vec<(usize, u32)>]) -> (Vec<u32>, Vec<usize>) {
    let mut dist = vec![u32::MAX; g.len()];
    let mut prv = vec![usize::MAX; g.len()];
    prv[s] = s;
    dist[s] = 0;
    let mut heap = radix_heap::RadixHeap::new();
    heap.push(0, s);
    while let Some((dx, x)) = heap.pop() {
        if dx <= dist[x] {
            for &(y, w) in &g[x] {
                let dy = dx + w;
                if dy < dist[y] {
                    prv[y] = x;
                    dist[y] = dy;
                    heap.push(dy, y);
                }
            }
        }
    }
    (dist, prv)
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;
    use randtools::LogUniform;
    use randtools::SimpleDigraph;
    use std::collections::HashMap;

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
            } else if p == usize::MAX {
                u32::MAX
            } else {
                dist[p] + edges.get(&(p, x)).unwrap()
            };
            assert_eq!(expected, dist[x]);
        });
    }
}
