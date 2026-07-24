//! Fast Fourier Transform over finite fields $𝔽_P$.
//!
//! This crate implements the Cooley-Tukey FFT and its inverse (IFFT) algorithm for
//! polynomial multiplication and other convolution-based computations in modular arithmetic.
//! Both transforms operate in-place on arrays of field elements and require the array length
//! to be a power of two.
//!
//! # When to Use
//!
//! Use this crate when you need to efficiently multiply polynomials or compute convolutions
//! over a prime field. The FFT reduces polynomial multiplication from $O(n^2)$ time to
//! $O(n \log n)$, making it essential for large-degree polynomials in competitive programming
//! and cryptographic applications.
//!
//! # Examples
//!
//! ```
//! use fp_fft::{fft, ifft};
//! use fp::fp;
//!
//! const P: u64 = 998_244_353;
//!
//! // Multiply polynomials a(x) = 1 + 2x and b(x) = 3 + 4x using FFT
//! // (product: 3 + 10x + 8x²)
//! let mut a = vec![fp::<P>(1), fp::<P>(2), fp::<P>(0), fp::<P>(0)];
//! let mut b = vec![fp::<P>(3), fp::<P>(4), fp::<P>(0), fp::<P>(0)];
//!
//! fft(&mut a);
//! fft(&mut b);
//!
//! for (av, bv) in a.iter_mut().zip(&b) {
//!     *av *= *bv;
//! }
//!
//! ifft(&mut a);
//!
//! assert_eq!(a[0], fp::<P>(3));  // constant term: 1 * 3
//! assert_eq!(a[1], fp::<P>(10)); // x term: 1*4 + 2*3
//! assert_eq!(a[2], fp::<P>(8));  // x² term: 2 * 4
//! ```
//!
//! # Main Items
//!
//! - [`fft`]: Forward FFT (in-place)
//! - [`ifft`]: Inverse FFT (in-place)
//!
//! # Complexity
//!
//! - Forward and inverse FFT: $O(n \log n)$ where $n$ is the array length
//! - Input length must be a power of two
//! - Time domain operations on the transformed data remain $O(n)$

use fp::{Fp, fp};

const DIADIC_ROOTS_BUFFER_LEN: usize = 64;

const fn find_primitive_root<const P: u64>() -> Fp<P> {
    let mut x = fp(2);
    while x.value() != P {
        if x.pow((P - 1) / 2).value() != 1 {
            return x;
        }
        x.add_assign(fp(1));
    }
    panic!("primitive root not found");
}

const fn build_diadic_roots<const P: u64>(root: Fp<P>) -> [Fp<P>; DIADIC_ROOTS_BUFFER_LEN] {
    let mut result = [fp(0); DIADIC_ROOTS_BUFFER_LEN];
    let k = (P - 1).trailing_zeros();
    let mut i = k as usize;
    result[i] = root.pow((P - 1) >> k);
    while i != 0 {
        result[i - 1] = result[i].mul(result[i]);
        i -= 1;
    }
    result
}

/// Computes the Fast Fourier Transform of a field element array (in-place).
///
/// Applies the Cooley-Tukey FFT algorithm to compute the Discrete Fourier Transform.
///
/// For an input array $(x_0, x_1, \ldots, x_{n-1})$, computes:
/// $$X_{\mathrm{rev}(i)} = \sum_{j=0}^{n-1} x_j \cdot w_n^{i \cdot j}$$
/// where $w_n$ is a primitive $n$-th root of unity over $\mathbb{F}_P$.
///
/// The implementation uses the in-place Cooley-Tukey algorithm with bit-reversal permutation.
/// The transform is performed in-place, modifying the input array directly. This is typically
/// followed by pointwise operations and an inverse FFT to compute the result in the
/// coefficient domain.
///
/// # Preconditions
///
/// - Array length must be a power of two
/// - Array length must not exceed $2^k$ where $k$ is the largest power of 2 dividing $P - 1$
///
/// # Time Complexity
///
/// $O(n \log n)$ where $n = $ `items.len()`
///
/// # Examples
///
/// ```
/// use fp_fft::fft;
/// use fp::fp;
///
/// const P: u64 = 998_244_353;
/// let mut data = [fp::<P>(3), fp::<P>(5)];
/// fft(&mut data);
/// // FFT of [x, y] is [x + y, x - y]
/// assert_eq!(data[0], fp::<P>(8));         // 3 + 5
/// assert_eq!(data[1], fp::<P>(998244351)); // 3 - 5 ≡ -2 (mod P)
/// ```
pub fn fft<const P: u64>(items: &mut [Fp<P>]) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let w = const { build_diadic_roots(find_primitive_root()) };
    let forth = w[2];
    let mut n = items.len();
    while n >= 4 {
        let w = w[n.trailing_zeros() as usize];
        for chunk in items.chunks_mut(n) {
            let mut wk = fp(1);
            for i in 0..n / 4 {
                let [a, b, c, d] = unsafe {
                    chunk.get_disjoint_unchecked_mut([i, i + n / 4, i + n / 2, i + 3 * n / 4])
                };
                [*a, *c] = [*a + *c, *a - *c];
                [*b, *d] = [*b + *d, *b - *d];
                *d *= forth;
                [*a, *b] = [*a + *b, *a - *b];
                [*c, *d] = [*c + *d, *c - *d];
                let wk2 = wk * wk;
                *b *= wk2;
                *c *= wk;
                *d *= wk * wk2;
                wk *= w;
            }
        }
        n /= 4;
    }
    if n == 2 {
        for chunk in items.chunks_mut(2) {
            let [a, b] = chunk else { unreachable!() };
            (*a, *b) = (*a + *b, *a - *b);
        }
    }
}

/// Computes the Inverse Fast Fourier Transform of a field element array (in-place).
///
/// Transforms an array from the frequency domain back to the coefficient domain,
/// inverting the effect of `fft`.
///
/// For a transformed array $(X_0, X_1, \ldots, X_{n-1})$, computes:
/// $$x_i = \frac{1}{n} \sum_{j=0}^{n-1} X_{\mathrm{rev}(j)} \cdot w^{-i \cdot j}$$
/// where $w_n$ is a primitive $n$-th root of unity over $\mathbb{F}_P$.
///
/// The implementation uses the in-place Cooley-Tukey algorithm with bit-reversal permutation.
/// The result is scaled by $1/n$ following the standard IFFT convention to ensure FFT and
/// IFFT are exact inverses.
///
/// # Preconditions
///
/// - Array length must be a power of two
/// - Array length must not exceed $2^k$ where $k$ is the largest power of 2 dividing $P - 1$
///
/// # Time Complexity
///
/// $O(n \log n)$ where $n = $ `items.len()`
///
/// # Examples
///
/// ```
/// use fp_fft::{fft, ifft};
/// use fp::fp;
///
/// const P: u64 = 998_244_353;
/// let original = [fp::<P>(1), fp::<P>(2), fp::<P>(3), fp::<P>(4)];
/// let mut data = original.clone();
///
/// fft(&mut data);
/// ifft(&mut data);
/// // IFFT inverts FFT: after round-trip, data equals the original
/// assert_eq!(data, original);
/// ```
pub fn ifft<const P: u64>(items: &mut [Fp<P>]) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let w = const { build_diadic_roots(find_primitive_root().inv()) };
    let mut n = 4;
    if items.len().trailing_zeros() % 2 == 1 {
        for chunk in items.chunks_mut(2) {
            let [a, b] = chunk else { unreachable!() };
            (*a, *b) = (*a + *b, *a - *b);
        }
        n *= 2;
    }
    let forth = w[2];
    while n <= items.len() {
        let w = w[n.trailing_zeros() as usize];
        for chunk in items.chunks_mut(n) {
            let mut wk = fp(1);
            for i in 0..n / 4 {
                let [a, b, c, d] = unsafe {
                    chunk.get_disjoint_unchecked_mut([i, i + n / 4, i + n / 2, i + 3 * n / 4])
                };
                let wk2 = wk * wk;
                *b *= wk2;
                *c *= wk;
                *d *= wk * wk2;
                [*a, *b] = [*a + *b, *a - *b];
                [*c, *d] = [*c + *d, *c - *d];
                *d *= forth;
                [*a, *c] = [*a + *c, *a - *c];
                [*b, *d] = [*b + *d, *b - *d];
                wk *= w;
            }
        }
        n *= 4;
    }
    let len_inv = fp(items.len() as u64).inv();
    for item in items {
        *item *= len_inv;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_primitive_root() {
        assert_eq!(find_primitive_root::<998_244_353>(), fp(3));
    }

    #[test]
    fn test_build_twiddle_factors() {
        let twiddle_factors = build_diadic_roots::<998_244_353>(fp(3));
        assert_eq!(twiddle_factors[0], fp(1));
        assert_eq!(twiddle_factors[1], -fp(1));
    }
}
