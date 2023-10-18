use super::Int;
use std::mem::swap;

/// Returns the greatest common divisor of `x` and `y`.
pub fn gcd<T: Int>(mut x: T, mut y: T) -> T {
    while x != T::zero() {
        y = y.rem_euclid(x);
        swap(&mut x, &mut y);
    }
    y.abs()
}

#[cfg(test)]
mod tests {
    use super::gcd;
    use test_case::test_case;

    #[test_case(0, 0 => 0)]
    #[test_case(0, 1 => 1)]
    #[test_case(1, 0 => 1)]
    #[test_case(1, 1 => 1)]
    #[test_case(0, 18 => 18)]
    #[test_case(1, 18 => 1)]
    #[test_case(18, 0 => 18)]
    #[test_case(18, 1 => 1)]
    #[test_case(42, 48 => 6)]
    #[test_case(55, 89 => 1)]
    fn test_gcd(x: i32, y: i32) -> i32 {
        let g = gcd(x, y);
        assert_eq!(g, gcd(-x, y));
        assert_eq!(g, gcd(x, -y));
        assert_eq!(g, gcd(-x, -y));
        g
    }
}
