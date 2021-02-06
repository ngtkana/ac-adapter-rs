use super::Signed;

/// Returns an integer `z, n` such that (x + lℤ) ∩(y + mℤ) = z + nℤ
///
/// # Examples
///
/// Basic usage:
/// ```
/// use euclid::crt;
///
/// assert_eq!(crt(5, 6, 3, 8), Some((11, 24)));
/// ```
pub fn crt<T: Signed>(x: T, l: T, y: T, m: T) -> Option<(T, T)> {
    assert!(T::zero() < l);
    assert!(T::zero() < m);
    let (a, _b, g) = super::ext_gcd(l, m);
    if g.divides(y - x) {
        let mdivg = m / g;
        let a = ((y - x) / g * a) % mdivg;
        let a = if a < T::zero() { a + mdivg } else { a };
        assert!(T::zero() <= a && a < mdivg);
        Some((x + a * l, l * mdivg))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use {
        super::crt,
        rand::{prelude::StdRng, Rng, SeedableRng},
    };

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
