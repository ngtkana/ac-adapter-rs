pub trait Advance<T> {
    fn advance_until(&self, i: &mut usize, f: impl FnMut(&T) -> bool);
    fn advance_while(&self, i: &mut usize, f: impl FnMut(&T) -> bool);
}
impl<T> Advance<T> for [T] {
    fn advance_until(&self, i: &mut usize, f: impl FnMut(&T) -> bool) {
        *i = self[*i..].iter().position(f).map_or(self.len(), |d| *i + d);
    }
    fn advance_while(&self, i: &mut usize, mut f: impl FnMut(&T) -> bool) {
        self.advance_until(i, |x| !f(x))
    }
}

#[cfg(test)]
mod tests {
    use {
        super::Advance,
        galvanic_assert::{assert_that, matchers},
        itertools::Itertools,
        rand::{
            distributions::Uniform,
            prelude::{Distribution, StdRng},
            Rng, SeedableRng,
        },
        std::ops::Range,
        test_case::test_case,
    };

    #[test_case(&[], 0 => 0)]
    #[test_case(&[0], 0 => 1)]
    #[test_case(&[0], 1 => 1)]
    #[test_case(&[1], 0 => 0)]
    #[test_case(&[1], 1 => 1)]
    #[test_case(&[0, 0], 0 => 2)]
    #[test_case(&[0, 0], 1 => 2)]
    #[test_case(&[0, 0], 2 => 2)]
    #[test_case(&[0, 1], 0 => 1)]
    #[test_case(&[0, 1], 1 => 1)]
    #[test_case(&[0, 1], 2 => 2)]
    #[test_case(&[1, 0], 0 => 0)]
    #[test_case(&[1, 0], 1 => 2)]
    #[test_case(&[1, 0], 2 => 2)]
    #[test_case(&[1, 1], 0 => 0)]
    #[test_case(&[1, 1], 1 => 1)]
    #[test_case(&[1, 1], 2 => 2)]
    fn test_advance_until(a: &[u8], mut i: usize) -> usize {
        a.advance_until(&mut i, |&b| b == 1);
        i
    }

    #[test_case(&[], 0 => 0)]
    #[test_case(&[0], 0 => 0)]
    #[test_case(&[0], 1 => 1)]
    #[test_case(&[1], 0 => 1)]
    #[test_case(&[1], 1 => 1)]
    #[test_case(&[0, 0], 0 => 0)]
    #[test_case(&[0, 0], 1 => 1)]
    #[test_case(&[0, 0], 2 => 2)]
    #[test_case(&[0, 1], 0 => 0)]
    #[test_case(&[0, 1], 1 => 2)]
    #[test_case(&[0, 1], 2 => 2)]
    #[test_case(&[1, 0], 0 => 1)]
    #[test_case(&[1, 0], 1 => 1)]
    #[test_case(&[1, 0], 2 => 2)]
    #[test_case(&[1, 1], 0 => 2)]
    #[test_case(&[1, 1], 1 => 2)]
    #[test_case(&[1, 1], 2 => 2)]
    fn test_advance_while(a: &[u8], mut i: usize) -> usize {
        a.advance_while(&mut i, |&b| b == 1);
        i
    }

    fn test_advance_until_diff_impl(a: &[u32], k: u32) {
        let mut cnt = 0;
        let window_end = a
            .iter()
            .scan(0, |r, &x| {
                a.advance_until(r, |&y| {
                    cnt += 1;
                    x + k < y
                });
                Some(*r)
            })
            .collect_vec();

        // Check the results.
        for Range { start, end } in window_end.iter().enumerate().map(|(l, &r)| l..r) {
            assert_that!(&(a[end - 1] - a[start]), matchers::leq(k));
            if end != a.len() {
                assert_that!(&(a[end] - a[start]), matchers::gt(k));
            }
        }

        // Every call of `advance_until` calls `f` constant times amortized.
        assert_that!(&cnt, matchers::lt(2 * a.len()));
    }

    #[test]
    fn test_advance_until_diff() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..10);
            let mut a = Uniform::from(0..10)
                .sample_iter(&mut rng)
                .take(n)
                .collect_vec();
            for i in 0..n - 1 {
                a[i + 1] += a[i];
            }
            let k = rng.gen_range(0..=a[n - 1]);
            test_advance_until_diff_impl(&a, k);
        }
    }
}
