use std::mem::swap;

pub fn gcd(mut x: u64, mut y: u64) -> u64 {
    loop {
        if x == 0 {
            return y;
        } else {
            y %= x;
            swap(&mut x, &mut y);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::gcd;
    use test_case::test_case;

    #[test_case(2, 3 => 1)]
    #[test_case(4, 6 => 2)]
    #[test_case(55, 89 => 1)]
    #[test_case(42, 48 => 6)]
    fn test_hand(x: u64, y: u64) -> u64 {
        gcd(x, y)
    }

    #[test]
    fn test_gcd_zero() {
        for i in 0..20 {
            assert_eq!(gcd(0, i), i);
            assert_eq!(gcd(i, 0), i);
        }
    }

    #[test]
    fn test_gcd_one() {
        for i in 0..20 {
            assert_eq!(gcd(1, i), 1);
            assert_eq!(gcd(i, 1), 1);
        }
    }

    #[test]
    fn test_gcd_identical() {
        for i in 0..20 {
            assert_eq!(gcd(i, i), i);
        }
    }

    #[test]
    fn test_gcd_divisible() {
        for i in 0..20 {
            for j in 0..20 {
                assert_eq!(gcd(i, i * j), i);
                assert_eq!(gcd(i * j, i), i);
            }
        }
    }
}
