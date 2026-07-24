//! 有限体 $𝔽_P$ 上の高速フーリエ変換（FFT）。
//!
//! Cooley-Tukey アルゴリズムで、多項式乗算を $O(n^2)$ から $O(n \log n)$ に削減。
//!
//! # 仕様
//!
//! 配列 $(x_0, \ldots, x_{n-1})$ に対して：
//! - `fft`: $X_i = \sum_{j=0}^{n-1} x_j \cdot w^{ij}$（$w$ は $n$ 次原始単位根）
//! - `ifft`: `fft` の逆変換（$1/n$ でスケール）
//! - `split_fft`: IFFT後、各半分に FFT を適用
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
//! - [`split_fft`]: IFFT → 各半分に FFT

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

/// 前方フーリエ変換。入力 $(x_0, \ldots, x_{n-1})$ に対して $X_i = \sum_j x_j w^{ij}$。
///
/// インプレース変換。$n$ は 2 の累乗。
///
/// # 例
///
/// ```
/// use fp::fp;
/// use fp_fft::fft;
/// const P: u64 = 998_244_353;
/// let mut a = [fp::<P>(3), fp::<P>(5)];
/// fft(&mut a);
/// assert_eq!(a[0], fp::<P>(8)); // 3 + 5
/// assert_eq!(a[1], fp::<P>(998244351)); // 3 - 5 ≡ -1
/// ```
pub fn fft<const P: u64>(items: &mut [Fp<P>]) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let forth = Diroot::FORWARD[2];
    let mut n = items.len();
    while n >= 4 {
        let w = Diroot::FORWARD[n.trailing_zeros() as usize];
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

/// 逆フーリエ変換。`fft` の逆。出力は $1/n$ でスケール。
///
/// インプレース変換。$n$ は 2 の累乗。
///
/// # 例
///
/// ```
/// use fp::fp;
/// use fp_fft::fft;
/// use fp_fft::ifft;
/// const P: u64 = 998_244_353;
/// let orig = [fp::<P>(1), fp::<P>(2)];
/// let mut a = orig;
/// fft(&mut a);
/// ifft(&mut a);
/// assert_eq!(a, orig);
/// ```
pub fn ifft<const P: u64>(items: &mut [Fp<P>]) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let mut n = 4;
    if items.len().trailing_zeros() % 2 == 1 {
        for chunk in items.chunks_mut(2) {
            let [a, b] = chunk else { unreachable!() };
            (*a, *b) = (*a + *b, *a - *b);
        }
        n *= 2;
    }
    let forth = Diroot::BACKWARD[2];
    while n <= items.len() {
        let w = Diroot::BACKWARD[n.trailing_zeros() as usize];
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

/// IFFT後、各半分に FFT を適用。入力 $X$ に対して $y = \text{IFFT}(X)$ とし、$\text{FFT}(y[0..n/2])$ と $\text{FFT}(y[n/2..n])$ を出力。
///
/// 計算量は $n \log n$。
///
/// # 例
///
/// ```
/// use fp::fp;
/// use fp_fft::split_fft;
/// const P: u64 = 998_244_353;
/// let mut a = [fp::<P>(1), fp::<P>(2)];
/// split_fft(&mut a);
/// assert_eq!(a[0], fp::<P>(3) * fp::<P>(2).inv()); // IFFT: (1 + 2) / 2 = 3/2
/// assert_eq!(a[1], fp::<P>(998244352) * fp::<P>(2).inv()); // IFFT: (1 - 2) / 2 = -1/2
/// ```
pub fn split_fft<const P: u64>(items: &mut [Fp<P>]) {
    let len = items.len();
    let (a, b) = items.split_at_mut(len / 2);
    ifft(b);
    let w = Diroot::BACKWARD[len.trailing_zeros() as usize];
    let mut coeff = fp(1);
    for b in &mut *b {
        *b *= coeff;
        coeff *= w;
    }
    fft(b);
    let inv2 = fp(2).inv();
    for (a, b) in a.iter_mut().zip(b) {
        [*a, *b] = [(*a + *b) * inv2, (*a - *b) * inv2];
    }
}

pub fn mask_lower_part<const P: u64>(items: &mut [Fp<P>]) {
    let len = items.len();
    let (a, b) = items.split_at_mut(len / 2);
    ifft(b);
    let w = Diroot::BACKWARD[len.trailing_zeros() as usize];
    let mut coeff = fp(1);
    for b in &mut *b {
        *b *= coeff;
        coeff *= w;
    }
    fft(b);
    let inv2 = fp(2).inv();
    for (a, b) in a.iter_mut().zip(b) {
        [*a, *b] = [(*a + *b) * inv2, (*a - *b) * inv2];
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
