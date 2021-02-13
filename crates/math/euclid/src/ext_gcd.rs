use {super::Signed, std::mem::swap};

/// Takes two integers `x, y` and returns `a, b, g` satisfying `ax + by = g, 0 < g`
///
/// # Panics
///
/// Panics if `x == 0 || y == 0`
#[allow(clippy::many_single_char_names)]
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
    use {crate::ext_gcd, crate::gcd, test_case::test_case};

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
