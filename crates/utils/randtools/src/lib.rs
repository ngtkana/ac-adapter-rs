mod algo;

use rand::prelude::*;
use std::{collections::HashSet, iter, mem};

#[derive(Debug)]
pub struct LogUniform(pub usize, pub usize);
impl Distribution<usize> for LogUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        let &Self(l, r) = self;
        assert!(l < r);
        assert!(l != 0);
        let ln = rng.gen_range((l as f64).ln(), (r as f64).ln());
        (ln.exp().floor() as usize).max(l).min(r - 1)
    }
}

#[derive(Debug)]
pub struct Open(pub usize, pub usize);
impl Distribution<(usize, usize)> for Open {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (usize, usize) {
        let &Self(l, r) = self;
        assert!(l + 1 < r);
        let mut x = rng.gen_range(l, r - 1);
        let mut y = rng.gen_range(l, r);
        if x >= y {
            mem::swap(&mut x, &mut y);
            y += 1;
        }
        (x, y)
    }
}

#[derive(Debug)]
pub struct Tree(pub usize);
impl Distribution<Vec<Vec<usize>>> for Tree {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let n = self.0;
        assert!(1 <= n);
        if n == 1 {
            vec![Vec::new()]
        } else {
            let prufer = iter::repeat_with(|| rng.gen_range(0, n))
                .take(n - 2)
                .collect::<Vec<_>>();
            algo::prufer2tree(&prufer)
        }
    }
}

#[derive(Debug)]
pub struct SimpleGraph(pub usize, pub usize);
impl Distribution<Vec<Vec<usize>>> for SimpleGraph {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let &Self(n, m) = self;
        let mut g = vec![Vec::new(); n];
        for (u, v) in rng.sample(SimpleGraphEdges(n, m)) {
            g[u].push(v);
            g[v].push(u);
        }
        g
    }
}

#[derive(Debug)]
pub struct SimpleGraphEdges(pub usize, pub usize);
impl Distribution<Vec<(usize, usize)>> for SimpleGraphEdges {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<(usize, usize)> {
        let &Self(n, m) = self;
        assert!(m <= n * (n - 1) / 2);
        let mut set = HashSet::new();
        Open(0, n)
            .sample_iter(rng)
            .filter(|&(u, v)| {
                let found = set.contains(&(u, v));
                set.insert((u, v));
                set.insert((v, u));
                !found
            })
            .take(m)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{LogUniform, Open, Tree};
    use rand::prelude::*;
    mod algo;

    #[test]
    fn test_log_uniform() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let (l, r) = rng.sample(Open(1, 20));
            let x = rng.sample(LogUniform(l, r));
            assert!((l..r).contains(&x));
        }
    }

    #[test]
    fn test_open() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let d = rng.gen_range(2, 8);
            let l = rng.gen_range(0, 40);
            let r = l + d;
            let (x, y) = rng.sample(Open(l, r));
            assert!(l <= x && x < y && y < r);
        }
    }

    #[test]
    fn test_tree() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1, 1_000);
            let g = rng.sample(Tree(n));
            println!("g = {:?}", &g);
            assert!(algo::is_tree(&g));
        }
    }
}
