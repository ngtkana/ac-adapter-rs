use super::Int;
use std::mem::swap;

/// 最大公約数 $\gcd(x, y)$ を返す。符号は無視し、$\gcd(0, 0) = 0$。
///
/// ユークリッドの互除法で $O(\log \min(|x|, |y|))$ で計算する。
///
/// # 例
///
/// ```
/// use euclid::gcd;
/// assert_eq!(gcd(42, 48), 6);
/// assert_eq!(gcd(-42, 48), 6); // 符号は無視
/// assert_eq!(gcd(0, 0), 0);
/// ```
///
/// # 計算量
///
/// $O(\log \min(|x|, |y|))$
pub fn gcd<T: Int>(mut x: T, mut y: T) -> T {
    while x != T::ZERO {
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
