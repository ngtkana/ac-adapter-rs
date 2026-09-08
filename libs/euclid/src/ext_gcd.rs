use super::Signed;
use std::mem::swap;

/// 拡張ユークリッドの互除法。$ax + by = \gcd(x, y)$ を満たす $(a, b, g)$（$g = \gcd(x, y) > 0$）を返す。
///
/// 通常のユークリッドの互除法で商を求めながら、その商で係数 $a, b$ を同時に更新することで、
/// $\gcd$ とベズー係数を同じ $O(\log \min(|x|, |y|))$ 回のループで求める。
///
/// # 仕様
///
/// - 前提: $x \neq 0$ かつ $y \neq 0$
/// - 戻り値: $ax + by = g$, $g > 0$ を満たす $(a, b, g)$
///
/// # 例
///
/// ```
/// use euclid::ext_gcd;
/// let (a, b, g) = ext_gcd(42, 48);
/// assert_eq!(g, 6); // gcd(42, 48) = 6
/// assert_eq!(a * 42 + b * 48, g);
/// ```
///
/// # 計算量
///
/// $O(\log \min(|x|, |y|))$
///
/// # Panics
///
/// `x == 0` または `y == 0` のとき
pub fn ext_gcd<T: Signed>(x: T, y: T) -> (T, T, T) {
    assert_ne!(x, T::zero());
    assert_ne!(y, T::zero());
    let (a, g) = {
        let mut x = x;
        let mut y = y;
        let mut u = T::one();
        let mut v = T::zero();
        while x != T::zero() {
            let q = y / x;
            y -= q * x;
            v -= q * u;
            swap(&mut x, &mut y);
            swap(&mut u, &mut v);
        }
        if y < T::zero() {
            (-v, -y)
        } else {
            (v, y)
        }
    };
    assert_eq!((g - a * x) % y, T::zero());
    let b = (g - a * x) / y;
    (a, b, g)
}

#[cfg(test)]
mod tests {
    use crate::ext_gcd;
    use crate::gcd;
    use test_case::test_case;

    #[allow(clippy::unused_unit)]
    #[test_case(1, 1)]
    #[test_case(1, 18)]
    #[test_case(18, 1)]
    #[test_case(42, 48)]
    #[test_case(55, 89)]
    #[test_case(420, 1200)]
    fn test_gcd(x: i32, y: i32) {
        let gcd = gcd(x, y);
        for (x, y) in [x, -x].iter().copied().zip([y, -y].iter().copied()) {
            let (a, b, ext_gcd) = ext_gcd(x, y);
            assert_eq!(ext_gcd, gcd);
            assert_eq!(a * x + b * y, gcd);
        }
    }
}
