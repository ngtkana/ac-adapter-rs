use super::mod_inv;
use super::Fp;
use super::PrimitiveRoot;

const P1: u64 = 924844033;
const P2: u64 = 998244353;
const P3: u64 = 1012924417;
type F1 = Fp<P1>;
type F2 = Fp<P2>;
type F3 = Fp<P3>;

/// Multiplies two polynomials.
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fp2::fps_mul;
/// use fp2::Fp;
/// type F = Fp<998244353>;
/// let a: Vec<F> = vec![fp!(1), fp!(2), fp!(3)];
/// let b: Vec<F> = vec![fp!(4), fp!(5), fp!(6)];
/// let c = fps_mul(&a, &b);
/// assert_eq!(c, vec![fp!(4), fp!(13), fp!(28), fp!(27), fp!(18)]);
/// ```
pub fn fps_mul<const P: u64>(a: &[Fp<P>], b: &[Fp<P>]) -> Vec<Fp<P>>
where
    (): PrimitiveRoot<P>,
{
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut a = a.to_vec();
    let mut b = b.to_vec();
    let n = a.len() + b.len() - 1;
    let len = n.next_power_of_two();
    a.resize(len, Fp::new(0));
    b.resize(len, Fp::new(0));
    fft(&mut a);
    fft(&mut b);
    for (a, b) in a.iter_mut().zip(b.iter()) {
        *a *= *b;
    }
    ifft(&mut a);
    a.truncate(n);
    a
}

/// Multiplies two polynomials.
pub fn any_mod_fps_mul<const P: u64>(a: &[Fp<P>], b: &[Fp<P>]) -> Vec<Fp<P>> {
    let v1 = fps_mul(
        &a.iter().map(|&x| F1::new(x.value())).collect::<Vec<_>>(),
        &b.iter().map(|&x| F1::new(x.value())).collect::<Vec<_>>(),
    );
    let v2 = fps_mul(
        &a.iter().map(|&x| F2::new(x.value())).collect::<Vec<_>>(),
        &b.iter().map(|&x| F2::new(x.value())).collect::<Vec<_>>(),
    );
    let v3 = fps_mul(
        &a.iter().map(|&x| F3::new(x.value())).collect::<Vec<_>>(),
        &b.iter().map(|&x| F3::new(x.value())).collect::<Vec<_>>(),
    );
    v1.into_iter()
        .zip(v2)
        .zip(v3)
        .map(|((e1, e2), e3)| garner(e1, e2, e3))
        .collect::<Vec<_>>()
}

/// Fast Fourier transform.
/// # Requirements
///
/// - The length $n$ of $f$ is a power of two.
/// - $n | (p - 1)$
///
/// Especially, if $p = 998244353$, $n \leq 2^{23}$ must hold.
///
/// # Replaced by
///
/// $f(1), f(-1), f(i), f(-i), f(e^{\pi/2}), f(e^{5\pi/2}), \dots$
///
/// # Examples
///
/// ```
/// use fp2::fft;
/// use fp2::fp;
/// use fp2::Fp;
/// type F = Fp<998244353>;
/// let mut f: Vec<F> = vec![fp!(1000), fp!(100), fp!(10), fp!(1)];
/// fft(&mut f);
/// let i = fp!(3).pow(998244352 / 4);
/// assert_eq!(f, vec![
///     fp!(1111),
///     fp!(909),
///     fp!(990) + i * fp!(99),
///     fp!(990) - i * fp!(99)
/// ]);
/// ```
pub fn fft<const P: u64>(f: &mut [Fp<P>])
where
    (): PrimitiveRoot<P>,
{
    let n = f.len();
    assert!(n.is_power_of_two());
    assert!((P - 1) % n as u64 == 0);
    let mut root = <() as PrimitiveRoot<P>>::VALUE.pow((P - 1) / f.len() as u64);
    let fourth = <() as PrimitiveRoot<P>>::VALUE.pow((P - 1) / 4);
    let mut fft_len = n;
    while 4 <= fft_len {
        let quarter = fft_len / 4;
        for f in f.chunks_mut(fft_len) {
            let mut c = Fp::new(1);
            for (((i, j), k), l) in (0..)
                .zip(quarter..)
                .zip(quarter * 2..)
                .zip(quarter * 3..)
                .take(quarter)
            {
                let c2 = c * c;
                let x = f[i] + f[k];
                let y = f[j] + f[l];
                let z = f[i] - f[k];
                let w = fourth * (f[j] - f[l]);
                f[i] = x + y;
                f[j] = c2 * (x - y);
                f[k] = c * (z + w);
                f[l] = c2 * c * (z - w);
                c *= root;
            }
        }
        root *= root;
        root *= root;
        fft_len = quarter;
    }
    if fft_len == 2 {
        for f in f.chunks_mut(2) {
            let x = f[0];
            let y = f[1];
            f[0] = x + y;
            f[1] = x - y;
        }
    }
}
/// Inverse fast Fourier transform.
///
/// # Requirements
///
/// - The length $n$ of $f$ is a power of two.
/// - $n | (p - 1)$
///
/// Especially, if $p = 998244353$, $n \leq 2^{23}$ must hold.
///
/// # Replaced by
///
/// Exacly the inverse of [`fft`].
///
/// # Examples
/// ```
/// use fp2::fp;
/// use fp2::ifft;
/// use fp2::Fp;
/// type F = Fp<998244353>;
/// let i = fp!(3).pow(998244352 / 4);
/// let mut f: Vec<F> = vec![
///     fp!(1111),
///     fp!(909),
///     fp!(990) + i * fp!(99),
///     fp!(990) - i * fp!(99),
/// ];
/// ifft(&mut f);
/// assert_eq!(f, vec![fp!(1000), fp!(100), fp!(10), fp!(1)]);
/// ```
pub fn ifft<const P: u64>(f: &mut [Fp<P>])
where
    (): PrimitiveRoot<P>,
{
    let n = f.len();
    assert!(n.is_power_of_two());
    let root = <() as PrimitiveRoot<P>>::VALUE.pow((P - 1) / f.len() as u64);
    let mut roots = std::iter::successors(Some(root.inv()), |x| Some(x * x))
        .take(n.trailing_zeros() as usize + 1)
        .collect::<Vec<_>>();
    roots.reverse();
    let fourth = <() as PrimitiveRoot<P>>::VALUE.pow((P - 1) / 4).inv();
    let mut quarter = 1_usize;
    if n.trailing_zeros() % 2 == 1 {
        for f in f.chunks_mut(2) {
            let x = f[0];
            let y = f[1];
            f[0] = x + y;
            f[1] = x - y;
        }
        quarter = 2;
    }
    while quarter != n {
        let fft_len = quarter * 4;
        let root = roots[fft_len.trailing_zeros() as usize];
        for f in f.chunks_mut(fft_len) {
            let mut c = Fp::new(1);
            for (((i, j), k), l) in (0..)
                .zip(quarter..)
                .zip(quarter * 2..)
                .zip(quarter * 3..)
                .take(quarter)
            {
                let c2 = c * c;
                let x = f[i] + c2 * f[j];
                let y = f[i] - c2 * f[j];
                let z = c * (f[k] + c2 * f[l]);
                let w = fourth * c * (f[k] - c2 * f[l]);
                f[i] = x + z;
                f[j] = y + w;
                f[k] = x - z;
                f[l] = y - w;
                c *= root;
            }
        }
        quarter = fft_len;
    }
    let d = Fp::from(f.len()).inv();
    f.iter_mut().for_each(|x| *x *= d);
}

/// Restore the original value from the remainder of the division by `P1`, `P2`, and `P3`.
fn garner<const P: u64>(x1: Fp<P1>, x2: Fp<P2>, x3: Fp<P3>) -> Fp<P> {
    let (x1, x2, x3) = (x1.value(), x2.value(), x3.value());
    let x2 = ((x2 + (P2 - x1)) * mod_inv::<P2>(P1)) % P2;
    let x3 = (((x3 + (P3 - x1)) * mod_inv::<P3>(P1) % P3 + (P3 - x2)) * mod_inv::<P3>(P2)) % P3;
    Fp::new(x1 + P1 * (x2 + P2 * x3 % P))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn naive_mul<const P: u64>(a: &[Fp<P>], b: &[Fp<P>]) -> Vec<Fp<P>> {
        let mut c = vec![Fp::new(0); a.len() + b.len() - 1];
        for (i, a) in a.iter().enumerate() {
            for (j, b) in b.iter().enumerate() {
                c[i + j] += *a * *b;
            }
        }
        c
    }

    #[test]
    fn test_fps_mul_random() {
        type F = Fp<998244353>;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..80 {
            let n = rng.gen_range(1..=40);
            let m = rng.gen_range(1..=40);
            let a: Vec<F> = (0..n).map(|_| F::new(rng.gen())).collect();
            let b: Vec<F> = (0..m).map(|_| F::new(rng.gen())).collect();
            if a.last() == Some(&F::new(0)) || b.last() == Some(&F::new(0)) {
                continue;
            }
            let expected = naive_mul(&a, &b);
            let result = fps_mul(&a, &b);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_any_mod_fps_mul_random() {
        type F = Fp<1000000007>;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..80 {
            let n = rng.gen_range(1..=40);
            let m = rng.gen_range(1..=40);
            let a: Vec<F> = (0..n).map(|_| F::new(rng.gen())).collect();
            let b: Vec<F> = (0..m).map(|_| F::new(rng.gen())).collect();
            if a.last() == Some(&F::new(0)) || b.last() == Some(&F::new(0)) {
                continue;
            }
            let expected = naive_mul(&a, &b);
            let result = any_mod_fps_mul(&a, &b);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_garner_random() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let x = rng.gen_range(0..u64::MAX);
            let result = garner(F1::new(x), F2::new(x), F3::new(x));
            assert_eq!(result, Fp::<1000000007>::new(x));
        }
    }
}
