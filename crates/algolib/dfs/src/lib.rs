use std::mem::replace;

/// 一点からの到達可能性配列を返します。
pub fn calc_reachability(s: usize, g: &[Vec<usize>]) -> Vec<bool> {
    let mut ckd = vec![false; g.len()];
    ckd[s] = true;
    let mut queue = vec![s];
    while let Some(x) = queue.pop() {
        for &y in &g[x] {
            if !replace(&mut ckd[y], true) {
                queue.push(y);
            }
        }
    }
    ckd
}

#[cfg(test)]
mod tests {
    use {
        super::calc_reachability,
        rand::prelude::*,
        randtools::{LogUniform, SimpleGraph},
    };

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

            // calc_reachability
            let ckd = calc_reachability(s, &g);
            g.iter()
                .enumerate()
                .map(|(i, v)| v.iter().map(move |&j| (i, j)))
                .flatten()
                .for_each(|(i, j)| assert_eq!(ckd[i], ckd[j]));
        }
    }
}
