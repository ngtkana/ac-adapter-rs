//! Arithmetic of formal power series.
//!
//! # Data representation
//!
//! In fact a formal power series $f = f_0 x + f_1 x + f_2 x^2 + \dots \in \mathbb{F}\_p\[\[x\]\]$ has an infinite number of coefficients, but it is too hard for computers to handle it.
//! Therefore, we represent a formal power series $f$ as a finite sequence $f_0, f_1, \dots, f_{d-1}$ of length $d$.
//! This $d$ is called precision.
//! Trailing zeros are also allowed in this representation.
//!
//! Furthermore, higher-degree coefficients are regarded as zero.
//!
//! In conclution, the set of values that `Vec<Fp<P>>` can represent is exactly the same as the
//! following set:
//!
//! $$
//! \bigsqcup_{d=0}^\infty \mathbb{F}_p\[x\] / (x^d)
//! $$
//!
//! Especially, any two intances of different precisions are assumed not to be equal to each other.
//!
//! # Note on complexity
//! *We only consider cases where the precision is a power of 2.
//! If the precision is not a power of 2, the complexity is twice as bad as otherwise.*
//!
//! We may assume the complexity $\mathcal{M}(d)$ of multiplication of two polynomials of degree $d$ and
//! the complexity $\mathcal{F}(d)$ of FFT/IFFT of length $d$ satisfies the following property:
//!
//! $$
//! \begin{aligned}
//! \mathcal{M}(d) &= \Theta(d\log d) , \mathcal{F}(d) = \Theta(d\log d), \\\\
//! \mathcal{M}(d) &= 3 \mathcal{F}(2d) + O(d) \ \left( = 6 \mathcal{F}(d) + O(d) \right).
//! \end{aligned}
//! $$
//!
//! If each step in Newton's method is performed in $a\mathcal{M}(d)$ time (where $d$ is the resulting precision of each iteration),
//! then the total complexity is $2a\mathcal{M}(d) + O(d)$.
//!
//! We omit $O(d)$ terms when it is not important.
//!
//! # Table of contents
//! $O(d)$ is omitted here.
//!
//! | Name | Complexity |
//! | ---- | ---------- |
//! | [`fps_inv`] | $2\mathcal{M}(d)$ |
//! | [`fps_sqrt`] | $6\mathcal{M}(d)$ |
//! | [`fps_deriv`] | $O(d)$ |
//! | [`fps_int`] | $O(d)$ |
//! | [`fps_log`] | $3\mathcal{M}(d)$ |
//! | [`fps_exp`] | $(10+2/3)\mathcal{M}(d)$ |

use fp2::fft;
use fp2::fps_mul;
use fp2::ifft;
use fp2::Fp;
use fp2::PrimitiveRoot;
use std::iter::repeat;

/// Define a formal power series in the same way as `vec!`.
///
/// This calls [`Fp::from`] for each element.
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fp2::Fp;
/// use fps::fps;
/// let f: Vec<Fp<998244353>> = fps![1, 2, 3];
/// assert_eq!(f, vec![fp!(1), fp!(2), fp!(3)]);
/// ```
#[macro_export]
macro_rules! fps {
    () => (
        vec![]
    );
    ($elem:expr; $n:expr) => (
        vec![fp!($elem); $n]
    );
    ($($x:expr),+ $(,)?) => (
        vec![$(fp!($x)),+]
    );
}

/// Returns the multiplicative inverse of a formal power series.
///
/// # Requirements
/// $f_0 \ne 0$
///
/// # Complexity
/// It takes $2\mathcal{M}(d) + O(d)$ time because it performs
/// three double-precision FFTs $(\mathcal{M}(d))$ in each iteration.
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fps::fps_inv;
/// let g = fps_inv::<998244353>(&[fp!(1), fp!(2)], 4);
/// assert_eq!(g, vec![fp!(1), fp!(-2), fp!(4), fp!(-8)]);
/// ```
pub fn fps_inv<const P: u64>(f: impl AsRef<[Fp<P>]>, precision: usize) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    let f = f.as_ref();
    assert_ne!(
        f.first(),
        Some(&Fp::new(0)),
        "The constant term must be nonzero."
    );
    let mut g = vec![f[0].inv()];
    while g.len() < precision {
        g = {
            let precision = g.len() * 2;
            let fft_size = precision * 2;
            let mut f = f
                .iter()
                .copied()
                .take(precision)
                .chain(repeat(Fp::new(0)))
                .take(fft_size)
                .collect::<Vec<_>>();
            g.resize(fft_size, Fp::new(0));
            fft(&mut f);
            fft(&mut g);
            let mut result = f
                .iter()
                .zip(&g)
                .map(|(&f, &g)| g * (-f * g + 2))
                .collect::<Vec<_>>();
            ifft(&mut result);
            result.truncate(precision);
            result
        };
    }
    g.truncate(precision);
    g
}
/// Returns the square root of a formal power series.
///
/// # Requirements
/// $f_0 = 1$
///
/// # Complexity
/// It takes $6\mathcal{M}(d) + O(d)$ time because it performs
/// a multiplication $(\mathcal{M}(d))$, an inversion $(2\mathcal{M}(d))$ in each iteration.
///
/// and the sum of the above is $3\mathcal{M}(d)$.
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fps::fps_sqrt;
/// let g = fps_sqrt::<998244353>(&[fp!(1), fp!(2)], 4);
/// assert_eq!(g, vec![fp!(1), fp!(1), -fp!(2).inv(), fp!(2).inv()]);
/// ```
pub fn fps_sqrt<const P: u64>(f: impl AsRef<[Fp<P>]>, precision: usize) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    let f = f.as_ref();
    assert_eq!(f.first(), Some(&Fp::new(1)), "The constant term must be 1.");
    let mut g = vec![f[0].inv()];
    let inv2 = Fp::new(2).inv();
    while g.len() < precision {
        g = {
            let precision = g.len() * 2;
            let fft_size = precision * 2;
            let f = f
                .iter()
                .copied()
                .take(precision)
                .chain(repeat(Fp::new(0)))
                .take(fft_size)
                .collect::<Vec<_>>();
            let mut g_inv = fps_inv(&g, precision);
            g_inv.resize(fft_size, Fp::new(0));
            let mut f_div_g = fps_mul(&f, &g_inv);
            f_div_g.truncate(precision);
            f_div_g
                .iter()
                .zip(g.iter().copied().chain(repeat(Fp::new(0))))
                .map(|(&f_div_g, g)| (f_div_g + g) * inv2)
                .collect()
        };
    }
    g.truncate(precision);
    g
}
/// Returns the derivative of a formal power series.
///
/// # Complexity
/// $O(d)$
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fps::fps;
/// let g = fps::fps_deriv::<998244353>(fps![1, 2], 4);
/// assert_eq!(g, fps![2, 0, 0, 0]);
/// ```
pub fn fps_deriv<const P: u64>(f: impl AsRef<[Fp<P>]>, precision: usize) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    let f = f.as_ref();
    let mut g = vec![Fp::new(0); precision];
    for (g, (i, &f)) in g.iter_mut().zip(f.iter().enumerate().skip(1)) {
        *g = f * Fp::from(i);
    }
    g
}
/// Returns the integral of a formal power series with zero constant term.
///
/// # Complexity
/// $O(d)$
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fps::fps;
/// let g = fps::fps_int::<998244353>(&fps![1, 2], 4);
/// assert_eq!(g, fps![0, 1, 1, 0]);
/// ```
pub fn fps_int<const P: u64>(f: impl AsRef<[Fp<P>]>, precision: usize) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    let f = f.as_ref();
    let mut g = vec![Fp::new(0); precision];
    let mut invs = vec![0i64];
    for ((i, g), f) in g.iter_mut().enumerate().skip(1).zip(f) {
        let inv_i = if i == 1 {
            1
        } else {
            let q = P as usize / i;
            let r = P as usize - q * i;
            -(q as i64) * invs[r] % P as i64
        };
        invs.push(inv_i);
        *g = f * Fp::from(inv_i);
    }
    g
}
/// Returns the logarithm of a formal power series.
///
/// Note that
///
/// $$
/// \log (1 + g) = g - \frac{1}{2}g^2 + \frac{1}{3}g^3 - \dots
/// $$
///
/// In fact, log in $F\[\[x\]\]$ is undefined because the fractions that appear in this expression are not guaranteed to exist.
/// However, we take advantage of the fact that precision is usually smaller than $P$ and assume that it is defined by mod $x^P$.
///
/// # Requirements
/// $f_0 = 1$, $d \le P$
///
/// # Complexity
/// It takes $3\mathcal{M}(d) + O(d)$ time because it performs
/// a multiplication $(\mathcal{M}(d))$, a derivation ($O(d)$), and an inversion $(2\mathcal{M}(d))$.
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fps::fps_log;
/// let g = fps_log::<998244353>(&[fp!(1), fp!(2)], 4);
/// assert_eq!(g, vec![fp!(0), fp!(2), fp!(-2), fp!(8) / fp!(3)]);
/// ```
pub fn fps_log<const P: u64>(f: impl AsRef<[Fp<P>]>, precision: usize) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    let f = f.as_ref();
    assert_eq!(f.first(), Some(&Fp::new(1)), "The constant term must be 1.");
    assert!(
        precision <= P as usize,
        "The precision must be less than P."
    );
    if precision == 0 {
        return Vec::new();
    }
    fps_int(
        fps_mul(fps_deriv(f, precision - 1), fps_inv(f, precision - 1)),
        precision,
    )
}
/// Returns the exponential of a formal power series.
///
/// Note that
/// $$
/// \exp g = 1 + g + \frac{1}{2!}g^2 + \frac{1}{3!}g^3 + \dots
/// $$
///
/// # Requirements
/// $f_0 = 0$, $d \le P$
///
/// # Complexity
/// It takes $\left(10+2/3\right)\mathcal{M}(d) + O(d)$ time because it performs
/// a logarithm $(4\mathcal{M}(d))$ and four double-precision FFTs$(\frac{4}{3}\mathcal{M}(d))$ in each iteration.
pub fn fps_exp<const P: u64>(f: impl AsRef<[Fp<P>]>, precision: usize) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    let f = f.as_ref();
    assert_eq!(
        f.first().copied().unwrap_or(Fp::new(0)),
        Fp::new(0),
        "The constant term must be zero."
    );
    assert!(precision <= P as usize,);
    let mut g = vec![Fp::new(1)];
    while g.len() < precision {
        g = {
            let precision = g.len() * 2;
            let fft_size = precision * 2;
            let mut f = f
                .iter()
                .copied()
                .take(precision)
                .chain(repeat(Fp::new(0)))
                .take(fft_size)
                .collect::<Vec<_>>();
            let mut log_g = fps_log(&g, precision);
            log_g.resize(fft_size, Fp::new(0));
            g.resize(fft_size, Fp::new(0));
            fft(&mut f);
            fft(&mut g);
            fft(&mut log_g);
            let mut result = f
                .iter()
                .zip(&g)
                .zip(&log_g)
                .map(|((&f, &g), &log_g)| g * (f - log_g + 1))
                .collect::<Vec<_>>();
            ifft(&mut result);
            result.truncate(precision);
            result
        };
    }
    g.truncate(precision);
    g
}
/// Resutns the $n$-th power of a formal power series.
///
/// Note that
///
/// $$
/// f^a = \exp (a \log f)
/// $$
///
/// # Requirements
/// $d \le P$
///
/// # Complexity
/// It takes $(13+2/3)\mathcal{M}(d) + O(d + \log P)$ time because it performs
/// a logarithm $(3\mathcal{M}(d))$ and a exponentiation $((10+2/3)\mathcal{M}(d))$.
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fps::fps;
/// use fps::fps_pow;
/// let g = fps_pow::<998244353>([fp!(1), fp!(2)], 3, 4);
/// assert_eq!(g, fps![1, 6, 12, 8]);
/// ```
pub fn fps_pow<const P: u64>(f: impl AsRef<[Fp<P>]>, pow: usize, precision: usize) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    if pow == 0 {
        let mut result = vec![Fp::new(0); precision];
        if precision > 0 {
            result[0] = Fp::new(1);
        }
        return result;
    }
    let f = f.as_ref();
    assert!(
        precision <= P as usize,
        "The precision must be less than P."
    );
    let leading_zeros = f.iter().take_while(|&&f| f == Fp::new(0)).count();
    let (Some(&head), Some(precision)) = (
        f.get(leading_zeros),
        precision.checked_sub(leading_zeros.saturating_mul(pow)),
    ) else {
        return vec![Fp::new(0); precision];
    };
    let head_inv = head.inv();
    let head_pow = head.pow(pow as u64);
    let log = fps_log(
        f[leading_zeros..]
            .iter()
            .map(|&f| f * head_inv)
            .collect::<Vec<_>>(),
        precision,
    );
    let mul_log = log.into_iter().map(|log_f| log_f * pow).collect::<Vec<_>>();
    let exp_mul_log = fps_exp(mul_log, precision);
    repeat(Fp::new(0))
        .take(leading_zeros * pow)
        .chain(exp_mul_log.into_iter().map(|result| result * head_pow))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use fp2::fp;
    use fp2::fps_mul;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter;
    use std::iter::repeat_with;

    const P: u64 = 998244353;
    type Fp = fp2::Fp<P>;

    fn random_fps(rng: &mut StdRng, head: Fp, precision: usize) -> Vec<Fp> {
        iter::once(head)
            .chain(iter::repeat_with(|| Fp::new(rng.gen_range(0..100))))
            .take(precision)
            .collect()
    }

    #[test]
    fn test_fps_inv_hand() {
        let fps_inv = fps_inv::<P>;
        let inv2 = Fp::new(2).inv().value() as i32;
        assert_eq!(fps_inv(fps![2], 0), fps![]);
        assert_eq!(fps_inv(fps![2], 1), fps![inv2]);
        assert_eq!(fps_inv(fps![2], 2), fps![inv2, 0]);
        assert_eq!(fps_inv(fps![2, 0], 0), fps![]);
        assert_eq!(fps_inv(fps![2, 0], 1), fps![inv2]);
        assert_eq!(fps_inv(fps![2, 0], 2), fps![inv2, 0]);
        assert_eq!(fps_inv(fps![2, 0], 3), fps![inv2, 0, 0]);
        assert_eq!(fps_inv(fps![1, 2], 1), fps![1]);
        assert_eq!(fps_inv(fps![1, 2], 2), fps![1, -2]);
        assert_eq!(fps_inv(fps![1, 2], 3), fps![1, -2, 4]);
    }

    #[test]
    fn test_fps_inv_random() {
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps(&mut rng, fp!(1), PRECISION);
            let g = fps_inv(&f, PRECISION);
            assert_eq!(g.len(), PRECISION);
            let mut result = fps_mul(&f, &g);
            result.truncate(PRECISION);
            let mut expected = vec![Fp::new(0); PRECISION];
            expected[0] = Fp::new(1);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_fps_sqrt_hand() {
        let fps_sqrt = fps_sqrt::<P>;
        assert_eq!(fps_sqrt(fps![1], 0), fps![]);
        assert_eq!(fps_sqrt(fps![1], 1), fps![1]);
        assert_eq!(fps_sqrt(fps![1], 2), fps![1, 0]);
        assert_eq!(fps_sqrt(fps![1, 4], 0), fps![]);
        assert_eq!(fps_sqrt(fps![1, 4], 1), fps![1]);
        assert_eq!(fps_sqrt(fps![1, 4], 2), fps![1, 2]);
        assert_eq!(fps_sqrt(fps![1, 4], 3), fps![1, 2, -2]);
    }

    #[test]
    fn test_fps_sqrt_random() {
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps(&mut rng, fp!(1), PRECISION);
            let g = fps_sqrt(&f, PRECISION);
            assert_eq!(g.len(), PRECISION);
            let mut result = fps_mul(&g, &g);
            result.truncate(PRECISION);
            assert_eq!(result, f);
        }
    }

    #[test]
    fn test_fps_deriv_hand() {
        let fps_deriv = fps_deriv::<P>;
        assert_eq!(fps_deriv(fps![1], 0), fps![]);
        assert_eq!(fps_deriv(fps![1], 1), fps![0]);
        assert_eq!(fps_deriv(fps![1], 2), fps![0, 0]);
        assert_eq!(fps_deriv(fps![1, 2], 0), fps![]);
        assert_eq!(fps_deriv(fps![1, 2], 1), fps![2]);
        assert_eq!(fps_deriv(fps![1, 2], 2), fps![2, 0]);
        assert_eq!(fps_deriv(fps![1, 2], 3), fps![2, 0, 0]);
        assert_eq!(fps_deriv(fps![1, 2], 8), fps![2, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(fps_deriv(fps![1, 2, 3, 4], 4), fps![2, 6, 12, 0]);
        assert_eq!(fps_deriv(fps![1, 2, 3, 4, 5, 6], 1), fps![2]);
    }

    #[test]
    fn test_fps_deriv_random() {
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps(&mut rng, fp!(1), PRECISION);
            let g = fps_deriv(&f, PRECISION);
            for i in 1..PRECISION {
                assert_eq!(g[i - 1], f[i] * Fp::from(i));
            }
            assert_eq!(g.len(), PRECISION);
        }
    }

    #[test]
    fn test_fps_int_hand() {
        let fps_int = fps_int::<P>;
        assert_eq!(fps_int(fps![1], 0), fps![]);
        assert_eq!(fps_int(fps![1], 1), fps![0]);
        assert_eq!(fps_int(fps![1], 2), fps![0, 1]);
        assert_eq!(fps_int(fps![1, 2], 0), fps![]);
        assert_eq!(fps_int(fps![1, 2], 1), fps![0]);
        assert_eq!(fps_int(fps![1, 2], 2), fps![0, 1]);
        assert_eq!(fps_int(fps![1, 2], 3), fps![0, 1, 1]);
        assert_eq!(fps_int(fps![1, 2], 8), fps![0, 1, 1, 0, 0, 0, 0, 0]);
        assert_eq!(fps_int(fps![1, 2, 3, 4], 4), fps![0, 1, 1, 1]);
        assert_eq!(fps_int(fps![1, 2, 3, 4, 5, 6], 1), fps![0]);
    }

    #[test]
    fn test_fps_int_random() {
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps(&mut rng, fp!(1), PRECISION);
            let g = fps_int(&f, PRECISION);
            assert_eq!(g.len(), PRECISION);
            let result = fps_deriv(&g, PRECISION);
            assert_eq!(result[..PRECISION - 1], f[..PRECISION - 1]);
            assert_eq!(result[PRECISION - 1], Fp::new(0));
        }
    }

    #[test]
    fn test_fps_log_hand() {
        let fps_log = fps_log::<P>;
        assert_eq!(fps_log(fps![1], 0), fps![]);
        assert_eq!(fps_log(fps![1], 1), fps![0]);
        assert_eq!(fps_log(fps![1], 2), fps![0, 0]);
        assert_eq!(fps_log(fps![1, 2], 0), fps![]);
        assert_eq!(fps_log(fps![1, 2], 1), fps![0]);
        assert_eq!(fps_log(fps![1, 2], 2), fps![0, 2]);
        assert_eq!(fps_log(fps![1, 2], 3), fps![0, 2, -2]);
        assert_eq!(fps_log(fps![1, 2], 8), vec![
            fp!(0),
            fp!(2),
            fp!(-4) / 2,
            fp!(8) / 3,
            fp!(-16) / 4,
            fp!(32) / 5,
            fp!(-64) / 6,
            fp!(128) / 7,
        ]);
        assert_eq!(fps_log(fps![1, 2, 3, 4, 5, 6], 1), fps![0]);
    }

    #[test]
    fn test_fps_log_random() {
        fn log_naive(f: &[Fp]) -> Vec<Fp> {
            let precision = f.len();
            let mut f = f.to_vec();
            f[0] = Fp::new(0);
            let mut g = vec![Fp::new(0); precision];
            let mut cum = f.clone();
            for p in 1..precision {
                for (g, cum) in g.iter_mut().zip(&cum) {
                    *g += cum * Fp::from(p).inv() * Fp::sign(p - 1);
                }
                cum = fps_mul(&cum, &f);
            }
            g
        }
        const PRECISION: usize = 10;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps(&mut rng, fp!(1), PRECISION);
            let g = fps_log(&f, PRECISION);
            assert_eq!(g.len(), PRECISION);
            let expected = log_naive(&f);
            assert_eq!(g, expected);
        }
    }

    #[test]
    fn test_fps_exp_hand() {
        let fps_exp = fps_exp::<P>;
        assert_eq!(fps_exp(fps![], 0), fps![]);
        assert_eq!(fps_exp(fps![], 1), fps![1]);
        assert_eq!(fps_exp(fps![], 2), fps![1, 0]);
        assert_eq!(fps_exp(fps![], 3), fps![1, 0, 0]);
        assert_eq!(fps_exp(fps![0], 1), fps![1]);
        assert_eq!(fps_exp(fps![0], 2), fps![1, 0]);
        assert_eq!(fps_exp(fps![0, 2], 0), fps![]);
        assert_eq!(fps_exp(fps![0, 2], 1), fps![1]);
        assert_eq!(fps_exp(fps![0, 2], 2), fps![1, 2]);
        assert_eq!(fps_exp(fps![0, 2], 3), fps![1, 2, 2]);
        assert_eq!(fps_exp(fps![0, 2], 8), vec![
            fp!(1),
            fp!(2),
            fp!(4) / 2,
            fp!(8) / 6,
            fp!(16) / 24,
            fp!(32) / 120,
            fp!(64) / 720,
            fp!(128) / 5040,
        ]);
        assert_eq!(fps_exp(fps![0, 2, 3, 4, 5, 6], 1), fps![1]);
    }

    #[test]
    fn test_fps_exp_random() {
        fn exp_naive(f: &[Fp]) -> Vec<Fp> {
            let precision = f.len();
            let mut g = vec![Fp::new(0); precision];
            g[0] = Fp::new(1);
            let mut cum = f.to_vec();
            let mut coeff = Fp::new(1);
            for p in 1..precision {
                coeff /= fp!(p);
                for (g, cum) in g.iter_mut().zip(&cum) {
                    *g += cum * coeff;
                }
                cum = fps_mul(cum, f);
            }
            g
        }
        const PRECISION: usize = 10;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps(&mut rng, fp!(0), PRECISION);
            let g = fps_exp(&f, PRECISION);
            assert_eq!(g.len(), PRECISION);
            let expected = exp_naive(&f);
            assert_eq!(g, expected);
        }
    }

    #[test]
    fn test_fps_pow_hand() {
        let fps_pow = fps_pow::<P>;
        assert_eq!(fps_pow(fps![1], 0, 0), fps![]);
        assert_eq!(fps_pow(fps![1], 0, 1), fps![1]);
        assert_eq!(fps_pow(fps![1], 0, 2), fps![1, 0]);
        assert_eq!(fps_pow(fps![1, 1], 2, 4), fps![1, 2, 1, 0]);
        assert_eq!(fps_pow(fps![1, 1], 3, 4), fps![1, 3, 3, 1]);
        assert_eq!(fps_pow(fps![1, 1], 4, 4), fps![1, 4, 6, 4]);
        assert_eq!(fps_pow(fps![0, 2], 2, 4), fps![0, 0, 4, 0]);
        assert_eq!(fps_pow(fps![0, 2], 3, 4), fps![0, 0, 0, 8]);
        assert_eq!(fps_pow(fps![0, 2], 4, 4), fps![0, 0, 0, 0]);
        assert_eq!(fps_pow(fps![0, 0, 0], 12, 3), fps![0, 0, 0]);
        assert_eq!(fps_pow(fps![0, 0, 0], 0, 3), fps![1, 0, 0]);
    }

    #[test]
    fn test_fps_pow_random() {
        fn pow_naive(f: &[Fp], pow: usize) -> Vec<Fp> {
            let precision = f.len();
            let mut result = vec![Fp::new(0); precision];
            result[0] = fp!(1);
            for _ in 0..pow {
                result = fps_mul(result, f);
                result.truncate(precision);
            }
            result
        }
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let leading_zeros = rng.gen_range(0..4);
            let f = repeat(fp!(0))
                .take(leading_zeros)
                .chain(repeat_with(|| Fp::new(rng.gen_range(0..100))))
                .take(PRECISION)
                .collect::<Vec<_>>();
            let pow = rng.gen_range(0..10);
            let g = fps_pow(&f, pow, PRECISION);
            assert_eq!(g.len(), PRECISION);
            let expected = pow_naive(&f, pow);
            assert_eq!(g, expected);
        }
    }
}
