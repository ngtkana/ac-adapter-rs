use super::Signed;

/// 中国剰余定理（CRT）。$2$ つの合同式の共通解を求める。
///
/// $(r_0 + m_0\mathbb{Z}) \cap (r_1 + m_1\mathbb{Z})$ は空集合か、ある $(r_2, m_2)$ を用いて
/// $r_2 + m_2\mathbb{Z}$ と書ける。空集合なら `None`、そうでなければ $(r_2, m_2)$ を返す。
/// 内部では拡張ユークリッドの互除法（[`ext_gcd`](super::ext_gcd)）で $\gcd(m_0, m_1)$ の
/// 線形結合を求め、解が存在する条件 $\gcd(m_0, m_1) \mid (r_1 - r_0)$ を判定する。
///
/// # 仕様
///
/// - 前提: $m_0 > 0$, $m_1 > 0$（`res0`, `mod0`, `res1`, `mod1` の順に対応）
/// - 戻り値: 解があれば `Some((r2, m2))`、なければ `None`
///
/// # 例
///
/// ```
/// use euclid::crt;
///
/// // x ≡ 5 (mod 6) かつ x ≡ 3 (mod 8) の解は x ≡ 11 (mod 24)
/// assert_eq!(crt(5, 6, 3, 8), Some((11, 24)));
/// ```
///
/// # 計算量
///
/// $O(\log \min(m_0, m_1))$
pub fn crt<T: Signed>(res0: T, mod0: T, res1: T, mod1: T) -> Option<(T, T)> {
    assert!(T::ZERO < mod0);
    assert!(T::ZERO < mod1);
    let (a, _b, g) = super::ext_gcd(mod0, mod1);
    if g.divides(res1 - res0) {
        let quot = mod1 / g;
        let a = ((res1 - res0) / g * a) % quot;
        let a = if a < T::ZERO { a + quot } else { a };
        assert!(T::ZERO <= a && a < quot);
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
                );
            });
        } else {
            (0..l * m).for_each(|i| assert!(i.rem_euclid(l) != x || i.rem_euclid(m) != y));
        }
    }
}
