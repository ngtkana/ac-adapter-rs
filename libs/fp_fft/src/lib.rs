//! 有限体 $𝔽_P$ 上の高速フーリエ変換（FFT）。
//!
//! Cooley-Tukey アルゴリズムで、多項式乗算を $O(n^2)$ から $O(n \log n)$ に削減。
//!
//! # 仕様
//!
//! 配列 $(x_0, \ldots, x_{n-1})$ に対して：
//! - `fft`: $X_i = \sum_{j=0}^{n-1} x_j \cdot w^{ij}$（$w$ は $n$ 次原始単位根）
//! - `ifft`: `fft` の逆変換（$1/n$ でスケール）
//!
//! # 例
//!
//! ```
//! use fp::fp;
//! use fp_fft::fft;
//!
//! const P: u64 = 998_244_353;
//! let mut data = [fp::<P>(1), fp::<P>(2)];
//! fft(&mut data);
//! assert_eq!(data[0], fp::<P>(3)); // 1 + 2
//! assert_eq!(data[1], fp::<P>(998244352)); // 1 - 2 ≡ -1 (mod P)
//! ```
//!
//! # 公開 API
//!
//! - [`fft`]: 前方フーリエ変換、$O(n \log n)$
//! - [`ifft`]: 逆フーリエ変換、$O(n \log n)$

use fp::Fp;
use fp::fp;

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

trait DirootTrait<const P: u64> {
    const FORWARD: [Fp<P>; DIADIC_ROOTS_BUFFER_LEN];
    const BACKWARD: [Fp<P>; DIADIC_ROOTS_BUFFER_LEN];
}
enum Diroot<const P: u64> {}
impl<const P: u64> DirootTrait<P> for Diroot<P> {
    const BACKWARD: [Fp<P>; DIADIC_ROOTS_BUFFER_LEN] =
        build_diadic_roots(find_primitive_root().inv());
    const FORWARD: [Fp<P>; DIADIC_ROOTS_BUFFER_LEN] = build_diadic_roots(find_primitive_root());
}

/// FFT をします。周波数間引き(Sande–Tukey)で、出力はbit-reversedです。
///
/// 内部で [`build_twiddle_factors_forward`] と [`fft_with_twiddle_factors`] が呼ばれます。
///
/// # Examples
///
/// ```
/// use fp::fp;
/// use fp_fft::fft;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp::<P>(3), fp::<P>(5)];
/// fft(&mut a);
/// assert_eq!(a[0], fp::<P>(8)); // 3 + 5
/// assert_eq!(a[1], fp::<P>(998244351)); // 3 - 5 ≡ -1
/// ```
pub fn fft<const P: u64>(items: &mut [Fp<P>]) {
    let twiddle_factors = build_twiddle_factors_forward(items.len());
    fft_with_twiddle_factors(items, &twiddle_factors);
}

/// Twiddle factor 前計算済みの場合の、[`fft`]。
///
/// # Examples
///
/// ```
/// use fp::fp;
/// use fp_fft::build_twiddle_factors_forward;
/// use fp_fft::fft_with_twiddle_factors;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp::<P>(3), fp::<P>(5)];
/// let twiddle_factors = build_twiddle_factors_forward(2);
/// fft_with_twiddle_factors(&mut a, &twiddle_factors);
///
/// assert_eq!(a[0], fp::<P>(8)); // 3 + 5
/// assert_eq!(a[1], fp::<P>(998244351)); // 3 - 5 ≡ -1
/// ```
pub fn fft_with_twiddle_factors<const P: u64>(
    items: &mut [Fp<P>],
    twiddle_factor_forward: &[Fp<P>],
) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let mut n = items.len();
    while n >= 2 {
        for chunk in items.chunks_mut(n) {
            for i in 0..n / 2 {
                let [a, b] = unsafe { chunk.get_disjoint_unchecked_mut([i, i + n / 2]) };
                [*a, *b] = [*a + *b, *a - *b];
                *b *= twiddle_factor_forward[n / 2 + i];
            }
        }
        n /= 2;
    }
}

/// IFFT をします。時間間引き(Cooley–Tukey)で、入力はbit-reversed想定です。
///
/// 内部で [`build_twiddle_factors_backward`] と [`fft_with_twiddle_factors`] が呼ばれます。
///
/// # Examples
///
/// ```
/// use fp::fp;
/// use fp_fft::ifft;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp::<P>(12), fp::<P>(4)];
/// ifft(&mut a);
///
/// assert_eq!(a[0], fp::<P>(8));
/// assert_eq!(a[1], fp::<P>(4));
/// ```
pub fn ifft<const P: u64>(items: &mut [Fp<P>]) {
    let twiddle_factors = build_twiddle_factors_backward(items.len());
    ifft_with_twiddle_factors(items, &twiddle_factors);
}

/// Twiddle factor 前計算済みの場合の、[`ifft`]。
///
/// # Examples
///
/// ```
/// use fp::fp;
/// use fp_fft::build_twiddle_factors_backward;
/// use fp_fft::ifft_with_twiddle_factors;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp::<P>(12), fp::<P>(4)];
/// let twiddle_factors = build_twiddle_factors_backward(2);
/// ifft_with_twiddle_factors(&mut a, &twiddle_factors);
///
/// assert_eq!(a[0], fp::<P>(8));
/// assert_eq!(a[1], fp::<P>(4));
/// ```
pub fn ifft_with_twiddle_factors<const P: u64>(
    items: &mut [Fp<P>],
    twiddle_factor_backward: &[Fp<P>],
) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let mut n = 2;
    while n <= items.len() {
        for chunk in items.chunks_mut(n) {
            for i in 0..n / 2 {
                let [a, b] = unsafe { chunk.get_disjoint_unchecked_mut([i, i + n / 2]) };
                *b *= twiddle_factor_backward[n / 2 + i];
                [*a, *b] = [*a + *b, *a - *b];
            }
        }
        n *= 2;
    }
    let len_inv = fp(items.len() as u64).inv();
    for item in items {
        *item *= len_inv;
    }
}

/// Twiddle factors を計算する(FFT用)
///
/// $$
/// (1, e(0), e(0), e(1/4), e(0), e(1/8), e(2/8), e(3/8), e(0), e(1/16), \dots)
/// $$
///
/// ただし $e(p / q)$ は $1$ の原始 $q$ 乗根の $p$ 乗です。
///
/// # Examples
///
/// ```
/// use fp::fp;
/// use fp_fft::build_twiddle_factors_forward;
/// use fp_fft::fft_with_twiddle_factors;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp::<P>(3), fp::<P>(5)];
/// let twiddle_factors = build_twiddle_factors_forward(2);
/// fft_with_twiddle_factors(&mut a, &twiddle_factors);
///
/// assert_eq!(a[0], fp::<P>(8)); // 3 + 5
/// assert_eq!(a[1], fp::<P>(998244351)); // 3 - 5 ≡ -1
/// ```
pub fn build_twiddle_factors_forward<const P: u64>(n: usize) -> Vec<Fp<P>> {
    build_twiddle_factors(n, &Diroot::FORWARD)
}

/// Twiddle factors を計算する(IFFT用)
pub fn build_twiddle_factors_backward<const P: u64>(n: usize) -> Vec<Fp<P>> {
    build_twiddle_factors(n, &Diroot::BACKWARD)
}

fn build_twiddle_factors<const P: u64>(
    n: usize,
    diroots: &[Fp<P>; DIADIC_ROOTS_BUFFER_LEN],
) -> Vec<Fp<P>> {
    let mut twiddle_factors = vec![fp::<P>(1); n];
    let mut len = 4;
    while len <= n {
        let w = diroots[len.trailing_zeros() as usize];
        for i in 0..len / 4 {
            twiddle_factors[len / 2 + i * 2] = twiddle_factors[len / 4 + i];
        }
        for i in 0..len / 4 {
            twiddle_factors[len / 2 + i * 2 + 1] = twiddle_factors[len / 2 + i * 2] * w;
        }
        len *= 2;
    }
    twiddle_factors
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
