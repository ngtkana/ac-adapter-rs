pub fn triangular_root(y: u64) -> u64 {
    if y == 0 {
        0
    } else {
        // `y.next_power_of_two().trailing_zeros()` overflows for `y > 1 << 63`, so we compute
        // the same value (`ceil(log2(y))`) via `leading_zeros` instead.
        let bits = u64::BITS - (y - 1).leading_zeros();
        let mut x = 1 << u32::midpoint(bits, 2);
        loop {
            // Widen to `u128` to avoid overflow of `2 * y` for `y > u64::MAX / 2`.
            let next_x = u64::midpoint(x - 1, (2 * u128::from(y) / u128::from(x)) as u64);
            if x <= next_x {
                return x;
            }
            x = next_x;
        }
    }
}

pub fn sqrt(y: u64) -> u64 {
    if y == 0 {
        0
    } else {
        // `y.next_power_of_two().trailing_zeros()` overflows for `y > 1 << 63`, so we compute
        // the same value (`ceil(log2(y))`) via `leading_zeros` instead.
        let bits = u64::BITS - (y - 1).leading_zeros();
        let mut x = 1 << bits.div_ceil(2);
        loop {
            let next_x = u64::midpoint(x, y / x);
            if x <= next_x {
                return x;
            }
            x = next_x;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::sqrt;
    use super::triangular_root;
    use rand::prelude::*;

    #[test]
    fn test_sqrt() {
        fn square(x: u64) -> u64 {
            x * x
        }
        let mut rng = StdRng::seed_from_u64(42);
        for y in 0..100 {
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
        for y in (0..100).map(square) {
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
        for y in (0..100).map(|x| square(x) + 1) {
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
        for y in (1..100).map(|x| square(x) - 1) {
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
        for &y in &[u64::MAX / 2, u64::MAX / 2 + 1] {
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
        for _ in 0..100 {
            let y = rng.gen_range(0..u64::MAX / 2);
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
    }

    #[test]
    fn test_triangular_root() {
        fn triangular(x: u64) -> u64 {
            x * (x + 1) / 2
        }
        let mut rng = StdRng::seed_from_u64(42);
        for y in 0..100 {
            let x = triangular_root(y);
            assert!(triangular(x) <= y);
            assert!(y < triangular(x + 1));
        }
        for y in (0..100).map(triangular) {
            let x = triangular_root(y);
            assert!(triangular(x) <= y);
            assert!(y < triangular(x + 1));
        }
        for y in (0..100).map(|x| triangular(x) + 1) {
            let x = triangular_root(y);
            assert!(triangular(x) <= y);
            assert!(y < triangular(x + 1));
        }
        for y in (1..100).map(|x| triangular(x) - 1) {
            let x = triangular_root(y);
            assert!(triangular(x) <= y);
            assert!(y < triangular(x + 1));
        }
        for _ in 0..100 {
            let y = rng.gen_range(0..u64::MAX / 4);
            let x = triangular_root(y);
            assert!(triangular(x) <= y);
            assert!(y < triangular(x + 1));
        }
    }
}
