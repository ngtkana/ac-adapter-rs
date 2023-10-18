use super::Signed;

/// Returns an integer `res2, mod2` such that (res0 + mod0 ℤ) ∩(res1 + mod1ℤ) = res2 + mod2ℤ
///
/// # Examples
///
/// Basic usage:
/// ```
/// use euclid::crt;
///
/// assert_eq!(crt(5, 6, 3, 8), Some((11, 24)));
/// ```
pub fn crt<T: Signed>(res0: T, mod0: T, res1: T, mod1: T) -> Option<(T, T)> {
    assert!(T::zero() < mod0);
    assert!(T::zero() < mod1);
    let (a, _b, g) = super::ext_gcd(mod0, mod1);
    if g.divides(res1 - res0) {
        let quot = mod1 / g;
        let a = ((res1 - res0) / g * a) % quot;
        let a = if a < T::zero() { a + quot } else { a };
        assert!(T::zero() <= a && a < quot);
        Some((res0 + a * mod0, mod0 * quot))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::crt;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[test]
    fn test_crt_impl_rand_validate() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let l = rng.gen_range(1..=100);
            let m = rng.gen_range(1..=100);
            validate(rng.gen_range(0..l), l, rng.gen_range(0..m), m);
        }
    }

    #[test]
    fn test_crt_impl_rand_no_overflow() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let l = rng.gen_range(1..=1_000_000);
            let m = rng.gen_range(1..=1_000_000 / l);
            let n = l * m;
            let z = rng.gen_range(0..n);
            crt(z % l, l, z % m, m);
        }
    }

    fn validate(x: i32, l: i32, y: i32, m: i32) {
        if let Some((z, n)) = crt(x, l, y, m) {
            (0..l * m).for_each(|i| {
                assert_eq!(
                    i.rem_euclid(l) == x && i.rem_euclid(m) == y,
                    i.rem_euclid(n) == z
                )
            });
        } else {
            (0..l * m).for_each(|i| assert!(i.rem_euclid(l) != x || i.rem_euclid(m) != y));
        }
    }
}
