/// Return the multiplicative inverse of `x` modulo `P`.
/// # Requirements
/// - $P$ is odd and prime ($P ≥ 2³¹$)
/// - $x < P$
/// # Returns
/// $x⁻¹ \mod P$
/// # Postconditions
/// - $0 ≤ \text{result} < P$
pub(crate) fn mod_inv<const P: u64>(x: u64) -> u64 {
    debug_assert!(P % 2 == 1);
    debug_assert!(P < 1 << 31);
    debug_assert!(x < P);
    mod_inv_signed(x as i64, P as i64) as u64
}
/// Returns $a⁻¹ \mod m$.
/// # Requirements
/// - $m > 0, 0 < a < m$
fn mod_inv_signed(a: i64, m: i64) -> i64 {
    debug_assert!(a > 0);
    debug_assert!(m > 0);
    if a == 1 {
        return 1;
    }
    m + (1 - m * mod_inv_signed(m % a, a)) / a
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[test]
    fn test_mod_inverse() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let m = rng.gen_range(2..256);
            let a = rng.gen_range(1..m);
            if num::integer::gcd(a, m) != 1 {
                continue;
            }
            let c = mod_inv_signed(a, m);
            assert_eq!(a * c % m, 1, "a = {a}, c = {c}, ");
            assert!((0..m).contains(&c));
        }
    }
}
