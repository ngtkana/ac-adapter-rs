pub fn triangular_root(y: u64) -> u64 {
    if y == 0 {
        0
    } else {
        let mut x = 1 << ((y.next_power_of_two().trailing_zeros() + 2) / 2);
        loop {
            let next_x = (x - 1 + 2 * y / x) / 2;
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
        let mut x = 1 << ((y.next_power_of_two().trailing_zeros() + 1) / 2);
        loop {
            let next_x = (x + y / x) / 2;
            if x <= next_x {
                return x;
            }
            x = next_x;
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{sqrt, triangular_root},
        rand::prelude::*,
    };

    #[test]
    fn test_sqrt() {
        let mut rng = StdRng::seed_from_u64(42);
        fn square(x: u64) -> u64 {
            x * x
        }
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
        for &y in &[std::u64::MAX / 2, std::u64::MAX / 2 + 1] {
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
        for _ in 0..100 {
            let y = rng.gen_range(0..std::u64::MAX / 2);
            let x = sqrt(y);
            assert!(square(x) <= y);
            assert!(y < square(x + 1));
        }
    }

    #[test]
    fn test_triangular_root() {
        let mut rng = StdRng::seed_from_u64(42);
        fn triangular(x: u64) -> u64 {
            x * (x + 1) / 2
        }
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
            let y = rng.gen_range(0..std::u64::MAX / 4);
            let x = triangular_root(y);
            assert!(triangular(x) <= y);
            assert!(y < triangular(x + 1));
        }
    }
}
