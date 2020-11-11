mod algo;

use rand::prelude::*;
use std::iter;

#[derive(Debug)]
pub struct Tree(usize);
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

#[cfg(test)]
mod tests {
    use super::Tree;
    use rand::prelude::*;
    mod algo;

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
