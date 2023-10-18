use std::collections::VecDeque;

#[derive(Debug, Clone, PartialEq, Copy, Eq, Hash)]
pub enum Weight {
    Zero,
    One,
}

/// 一点からの距離配列を作ります。
pub fn calc_dist(s: usize, g: &[Vec<(usize, Weight)>]) -> Vec<u32> {
    let mut dist = vec![std::u32::MAX; g.len()];
    dist[s] = 0;
    let mut queue = VecDeque::from(vec![s]);
    while let Some(x) = queue.pop_front() {
        let dx = dist[x];
        for &(y, w) in &g[x] {
            let dy = match w {
                Weight::One => dx + 1,
                Weight::Zero => dx,
            };
            if dy < dist[y] {
                dist[y] = dy;
                match w {
                    Weight::One => queue.push_back(y),
                    Weight::Zero => queue.push_front(y),
                }
            }
        }
    }
    dist
}

/// 一点からの距離配列と、前者配列を作ります。始点の前者は自分自身です。
pub fn calc_dist_restore(s: usize, g: &[Vec<(usize, Weight)>]) -> (Vec<u32>, Vec<usize>) {
    let mut dist = vec![std::u32::MAX; g.len()];
    let mut prv = vec![std::usize::MAX; g.len()];
    prv[s] = s;
    dist[s] = 0;
    let mut queue = VecDeque::from(vec![s]);
    while let Some(x) = queue.pop_front() {
        let dx = dist[x];
        for &(y, w) in &g[x] {
            let dy = match w {
                Weight::One => dx + 1,
                Weight::Zero => dx,
            };
            if dy < dist[y] {
                dist[y] = dy;
                prv[y] = x;
                match w {
                    Weight::One => queue.push_back(y),
                    Weight::Zero => queue.push_front(y),
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

    #[test]
    fn test_graph() {
        let mut rng = StdRng::seed_from_u64(42);
        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2..3000));
            let m = rng.sample(LogUniform(n - 1..(n * (n - 1) / 2 + 1).min(3000)));
            println!("Test {}, n = {}, m = {}", test_id, n, m);
            // 重みなしの木を生成して……
            let g = rng.sample(SimpleDigraph(n, m));
            // 重みをつけます。
            let g = g
                .iter()
                .map(|v| {
                    v.iter()
                        .map(|&j| {
                            (
                                j,
                                if rng.gen_ratio(1, 2) {
                                    super::Weight::Zero
                                } else {
                                    super::Weight::One
                                },
                            )
                        })
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
            validate_dist_prv(&dist, &prv, s);
        }
    }

    fn validate_dist(g: &[Vec<(usize, super::Weight)>], dist: &[u32], s: usize) {
        assert_eq!(dist[s], 0);
        for (u, v, w) in g
            .iter()
            .enumerate()
            .flat_map(|(i, v)| v.iter().map(move |&(j, w)| (i, j, w)))
        {
            match w {
                super::Weight::Zero => {
                    assert!(dist[u] >= dist[v]);
                }
                super::Weight::One => {
                    assert!(dist[u].saturating_add(1) >= dist[v]);
                }
            }
        }
    }

    fn validate_dist_prv(dist: &[u32], prv: &[usize], s: usize) {
        assert_eq!(prv[s], s);
        prv.iter().copied().enumerate().for_each(|(x, p)| {
            if p == std::usize::MAX {
                assert_eq!(dist[x], std::u32::MAX);
            } else {
                assert!(dist[p] == dist[x] || dist[p] + 1 == dist[x])
            }
        });
    }
}
