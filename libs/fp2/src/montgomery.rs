/// Returns the Montgomery representation of `x`.
/// # Requirements
/// - $P$ is odd and prime ($P \gt 2^{31}$)
/// - $x < 2^{32}$
/// # Returns
/// $x 2^{32} \mod P$
/// # Postconditions
/// - $0 \le \text{result} < P$
pub const fn oxidate<const P: u64>(x: u64) -> u64 { reduce::<P>(<() as Consts<P>>::M * x) }
/// Return the implicit value of a Montgomery representation.
/// # Requirements
/// - $P$ is odd and prime ($P \ge 2^{31}$)
/// - $x < 2^{32}P$
/// # Returns
/// $x 2^{-32} \mod P$
/// # Postconditions
/// - $0 \le \text{result} < P$
pub const fn reduce<const P: u64>(x: u64) -> u64 {
    assert!(P < 1 << 31);
    assert!(x < P << 32);
    let mut result = (x + lower_32_bits(lower_32_bits(x) * <() as Consts<P>>::K) * P) >> 32;
    if result >= P {
        result -= P;
    }
    debug_assert!(result < P);
    result
}
const LOWER_32_BITS: u64 = (1 << 32) - 1;
const fn lower_32_bits(x: u64) -> u64 { x & LOWER_32_BITS }
trait Consts<const P: u64> {
    /// $-P^{-1} \mod 2^{32}$
    const K: u64 = inv_mod_u32(P.wrapping_neg());
    /// $2^{64} \mod P$
    const M: u64 = P.wrapping_neg() % P;
}
impl<const P: u64> Consts<P> for () {}
/// Returns the multiplicative inverse of `x` modulo `2^32`.
const fn inv_mod_u32(x: u64) -> u64 {
    let mut y = x;
    y = lower_32_bits(y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y))));
    y = lower_32_bits(y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y))));
    y = lower_32_bits(y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y))));
    y = lower_32_bits(y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y))));
    y
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[test]
    fn test_inv_mod_u32() {
        let mut rand = StdRng::seed_from_u64(42);
        assert_eq!(inv_mod_u32(1), 1);
        assert_eq!(inv_mod_u32(3), 2863311531);
        assert_eq!(inv_mod_u32(5), 3435973837);
        for _ in 0..256 {
            let x = rand.gen::<u64>();
            if x % 2 == 0 {
                continue;
            }
            let y = inv_mod_u32(x);
            assert_eq!(x.wrapping_mul(y) & u32::MAX as u64, 1, "x = {x}, y = {y}");
        }
    }
    #[test]
    fn test_reduce_fp7() {
        let mut rand = StdRng::seed_from_u64(42);
        const P: u64 = 7;
        for _ in 0..256 {
            let x = rand.gen_range(0..P << 32);
            let y = reduce::<P>(x);
            assert_eq!(x % P, (y << 32) % P, "x = {x}, y = {y}");
        }
    }
    #[test]
    fn test_reduce_fp998244353() {
        let mut rng = StdRng::seed_from_u64(42);
        const P: u64 = 998244353;
        for _ in 0..256 {
            let x = rng.gen_range(0..P << 32);
            let y = reduce::<P>(x);
            assert_eq!(x % P, (y << 32) % P, "x = {x}, y = {y}");
        }
    }
}
