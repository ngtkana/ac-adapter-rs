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
//! use fp::fp_new;
//! use fp_fft::fft;
//!
//! const P: u64 = 998_244_353;
//! let mut data = [fp_new::<P>(1), fp_new::<P>(2)];
//! fft(&mut data);
//! assert_eq!(data[0], fp_new::<P>(3)); // 1 + 2
//! assert_eq!(data[1], fp_new::<P>(998244352)); // 1 - 2 ≡ -1 (mod P)
//! ```
//!
//! # 公開 API
//!
//! - [`fft`]: 前方フーリエ変換、$O(n \log n)$
//! - [`ifft`]: 逆フーリエ変換、$O(n \log n)$

use std::iter::successors;

use fp::Fp;
use fp::fp_new;

const DIADIC_ROOTS_BUFFER_LEN: usize = 64;

const fn find_primitive_root<const P: u64>() -> Fp<P> {
    let mut x = fp_new(2);
    while x.value() != P {
        if x.pow((P - 1) / 2).value() != 1 {
            return x;
        }
        x.add_assign(fp_new(1));
    }
    panic!("primitive root not found");
}

const fn build_diadic_roots<const P: u64>(root: Fp<P>) -> [Fp<P>; DIADIC_ROOTS_BUFFER_LEN] {
    let mut result = [fp_new(0); DIADIC_ROOTS_BUFFER_LEN];
    let k = (P - 1).trailing_zeros();
    let mut i = k as usize;
    result[i] = root.pow((P - 1) >> k);
    while i != 0 {
        result[i - 1] = result[i].mul(result[i]);
        i -= 1;
    }
    result
}

trait DiadicRootsTrait<const P: u64> {
    const VALUE: [Fp<P>; DIADIC_ROOTS_BUFFER_LEN];
}
enum DiadicRoots<const P: u64> {}
impl<const P: u64> DiadicRootsTrait<P> for DiadicRoots<P> {
    const VALUE: [Fp<P>; DIADIC_ROOTS_BUFFER_LEN] = build_diadic_roots(find_primitive_root());
}

/// FFT をします。周波数間引き(Sande–Tukey)で、出力はbit-reversedです。
///
/// 内部で [`build_twiddle_factors`] と [`fft_with_twiddle_factors`] が呼ばれます。
///
/// # Examples
///
/// ```
/// use fp::fp_new;
/// use fp_fft::fft;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp_new::<P>(3), fp_new::<P>(5)];
/// fft(&mut a);
/// assert_eq!(a[0], fp_new::<P>(8)); // 3 + 5
/// assert_eq!(a[1], fp_new::<P>(998244351)); // 3 - 5 ≡ -1
/// ```
pub fn fft<const P: u64>(items: &mut [Fp<P>]) {
    let twiddle_factors = build_twiddle_factors(items.len());
    fft_with_twiddle_factors(items, &twiddle_factors);
}

/// Twiddle factor 前計算済みの場合の、[`fft`]。
///
/// # Examples
///
/// ```
/// use fp::fp_new;
/// use fp_fft::build_twiddle_factors;
/// use fp_fft::fft_with_twiddle_factors;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp_new::<P>(3), fp_new::<P>(5)];
/// let twiddle_factors = build_twiddle_factors(2);
/// fft_with_twiddle_factors(&mut a, &twiddle_factors);
///
/// assert_eq!(a[0], fp_new::<P>(8)); // 3 + 5
/// assert_eq!(a[1], fp_new::<P>(998244351)); // 3 - 5 ≡ -1
/// ```
pub fn fft_with_twiddle_factors<const P: u64>(items: &mut [Fp<P>], twiddle_factors: &[Fp<P>]) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    for n in successors(Some(items.len()), |&n| Some(n / 2)).take_while(|&n| n >= 2) {
        for chunk in items.chunks_mut(n) {
            for i in 0..n / 2 {
                let [a, b] = unsafe { chunk.get_disjoint_unchecked_mut([i, i + n / 2]) };
                [*a, *b] = [*a + *b, *a - *b];
                *b *= twiddle_factors[n + i];
            }
        }
    }
}

/// IFFT をします。時間間引き(Cooley–Tukey)で、入力はbit-reversed想定です。
///
/// 内部で [`build_twiddle_factors`] と [`fft_with_twiddle_factors`] が呼ばれます。
///
/// # Examples
///
/// ```
/// use fp::fp_new;
/// use fp_fft::ifft;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp_new::<P>(12), fp_new::<P>(4)];
/// ifft(&mut a);
///
/// assert_eq!(a[0], fp_new::<P>(8));
/// assert_eq!(a[1], fp_new::<P>(4));
/// ```
pub fn ifft<const P: u64>(items: &mut [Fp<P>]) {
    let twiddle_factors = build_twiddle_factors(items.len());
    ifft_with_twiddle_factors(items, &twiddle_factors);
}

/// Twiddle factor 前計算済みの場合の、[`ifft`]。
///
/// # Examples
///
/// ```
/// use fp::fp_new;
/// use fp_fft::build_twiddle_factors;
/// use fp_fft::ifft_with_twiddle_factors;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp_new::<P>(12), fp_new::<P>(4)];
/// let twiddle_factors = build_twiddle_factors(2);
/// ifft_with_twiddle_factors(&mut a, &twiddle_factors);
///
/// assert_eq!(a[0], fp_new::<P>(8));
/// assert_eq!(a[1], fp_new::<P>(4));
/// ```
pub fn ifft_with_twiddle_factors<const P: u64>(items: &mut [Fp<P>], twiddle_factors: &[Fp<P>]) {
    let items_len = items.len();
    assert!(items_len.is_power_of_two());
    assert!(items_len.trailing_zeros() <= (P - 1).trailing_zeros());
    for n in successors(Some(2), |&n| Some(2 * n)).take_while(|&n| n <= items_len) {
        for chunk in items.chunks_mut(n) {
            for i in 0..n / 2 {
                let [a, b] = unsafe { chunk.get_disjoint_unchecked_mut([i, i + n / 2]) };
                *b *= twiddle_factors[2 * n - i];
                [*a, *b] = [*a + *b, *a - *b];
            }
        }
    }
    let len_inv = fp_new(items.len() as u64).inv();
    for item in items {
        *item *= len_inv;
    }
}

/// Twiddle factors を計算する(FFT用)
///
/// 長さ $2n + 1$ の配列ができます。最初の $1$ つは使わない場所。最後の $1$ つは番兵です。
///
/// $$
/// t _ { 2 ^ p + i } = e( i / 2 ^ p)
/// $$
///
/// ただし $e(a / b)$ は $1$ の原始 $b$ 乗根の $a$ 乗です。
///
/// # Examples
///
/// ```
/// use fp::fp_new;
/// use fp_fft::build_twiddle_factors;
/// use fp_fft::fft_with_twiddle_factors;
///
/// const P: u64 = 998_244_353;
///
/// let mut a = [fp_new::<P>(3), fp_new::<P>(5)];
/// let twiddle_factors = build_twiddle_factors(2);
/// fft_with_twiddle_factors(&mut a, &twiddle_factors);
///
/// assert_eq!(a[0], fp_new::<P>(8)); // 3 + 5
/// assert_eq!(a[1], fp_new::<P>(998244351)); // 3 - 5 ≡ -1
/// ```
pub fn build_twiddle_factors<const P: u64>(n: usize) -> Vec<Fp<P>> {
    let mut twiddle_factors = vec![fp_new::<P>(1); 2 * n + 1];
    for n in successors(Some(2), |&x| Some(2 * x)).take_while(|&x| x <= n) {
        let w = DiadicRoots::VALUE[n.trailing_zeros() as usize];
        for i in 0..n / 2 {
            twiddle_factors[n + i * 2] = twiddle_factors[n / 2 + i];
            twiddle_factors[n + i * 2 + 1] = twiddle_factors[n + i * 2] * w;
        }
    }
    twiddle_factors
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_primitive_root() {
        assert_eq!(find_primitive_root::<998_244_353>(), fp_new(3));
    }

    #[test]
    fn test_build_diadic_roots_small() {
        let diadic_roots = build_diadic_roots::<998_244_353>(fp_new(3));
        assert_eq!(diadic_roots[0], fp_new(1));
        assert_eq!(diadic_roots[1], fp_new(998_244_352));
        assert_eq!(diadic_roots[2], fp_new(911_660_635));
        assert_eq!(diadic_roots[3], fp_new(372_528_824));
    }

    #[test]
    fn test_build_twiddle_factors_small() {
        let diadic_roots = build_twiddle_factors::<998_244_353>(1024);
        assert_eq!(diadic_roots[0], fp_new(1));
        assert_eq!(diadic_roots[1], fp_new(1));
        assert_eq!(diadic_roots[2], fp_new(1));
        assert_eq!(diadic_roots[3], fp_new(998_244_352));
        assert_eq!(diadic_roots[4], fp_new(1));
        assert_eq!(diadic_roots[5], fp_new(911_660_635));
        assert_eq!(diadic_roots[6], fp_new(998_244_352));
        assert_eq!(diadic_roots[7], fp_new(86_583_718));
    }
}
