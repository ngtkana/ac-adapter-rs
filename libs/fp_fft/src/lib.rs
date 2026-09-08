//! 有限体 $𝔽_P$ 上の高速フーリエ変換（数論変換, NTT）。
//!
//! Cooley–Tukey 型のバタフライ演算を $\log n$ 段繰り返し、多項式の点値変換を
//! $O(n^2)$ から $O(n \log n)$ に削減する。$P$ が NTT-friendly
//! （$P - 1$ が十分大きな $2$ の冪で割り切れる）であることを利用し、$1$ の冪根を
//! [`fp`] クレート上で計算する。
//!
//! # 仕様
//!
//! 長さ $n = 2^k$ の配列 $(x_0, \ldots, x_{n-1})$、$w$ を $1$ の原始 $n$ 乗根として：
//!
//! - [`fft`][]: $X_i = \sum_{j=0}^{n-1} x_j w^{ij}$ を計算する。出力はビット反転順
//! - [`ifft`][]: [`fft`] の逆変換（結果を $1/n$ 倍）。入力はビット反転順を想定
//! - [`build_twiddle_factors`][]: [`fft`]、[`ifft`] で使う回転因子（twiddle factor）を前計算
//! - [`fft_with_twiddle_factors`]、[`ifft_with_twiddle_factors`][]: 回転因子を使い回す版
//!
//! いずれも `items.len()` は $2$ の冪であること、$n \mid P - 1$ であることが前提。
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
//! # 計算量
//!
//! - [`fft`]、[`ifft`][]: $O(n \log n)$（回転因子の前計算込み）
//! - [`fft_with_twiddle_factors`]、[`ifft_with_twiddle_factors`][]: $O(n \log n)$
//! - [`build_twiddle_factors`][]: $O(n)$

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

/// FFT（数論変換）をする。周波数間引き（Sande–Tukey）型で、出力はビット反転順になる。
///
/// 内部で [`build_twiddle_factors`] を呼んでから [`fft_with_twiddle_factors`] を適用する。
/// 回転因子を使い回したい場合は [`fft_with_twiddle_factors`] を直接使う。
///
/// # 仕様
///
/// `items` の長さ $n$ は $2$ の冪、かつ $n \mid P - 1$ であること。
/// $X_i = \sum_{j=0}^{n-1} x_j w^{ij}$（$w$ は $1$ の原始 $n$ 乗根）をビット反転順に並べて返す。
///
/// # 例
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
///
/// # 計算量
///
/// $O(n \log n)$
#[doc(alias = "ntt")]
pub fn fft<const P: u64>(items: &mut [Fp<P>]) {
    let twiddle_factors = build_twiddle_factors(items.len());
    fft_with_twiddle_factors(items, &twiddle_factors);
}

/// 回転因子を前計算済みの場合の [`fft`]。
///
/// `twiddle_factors` には [`build_twiddle_factors`] に `items.len()` を渡した結果を使う。
///
/// # 例
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
///
/// # 計算量
///
/// $O(n \log n)$
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

/// 逆FFT（数論変換の逆変換）をする。時間間引き（Cooley–Tukey）型で、入力はビット反転順を想定する。
///
/// [`fft`] の逆変換：$x_j = \frac{1}{n}\sum_{i=0}^{n-1} X_i w^{-ij}$ を計算する。
/// 内部で [`build_twiddle_factors`] を呼んでから [`ifft_with_twiddle_factors`] を適用する。
///
/// # 仕様
///
/// 前提は [`fft`] と同じ（長さ $n$ は $2$ の冪、$n \mid P - 1$）。
///
/// # 例
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
///
/// # 計算量
///
/// $O(n \log n)$
#[doc(alias = "ntt")]
#[doc(alias = "intt")]
pub fn ifft<const P: u64>(items: &mut [Fp<P>]) {
    let twiddle_factors = build_twiddle_factors(items.len());
    ifft_with_twiddle_factors(items, &twiddle_factors);
}

/// 回転因子を前計算済みの場合の [`ifft`]。
///
/// `twiddle_factors` には [`build_twiddle_factors`] に `items.len()` を渡した結果を使う。
///
/// # 例
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
///
/// # 計算量
///
/// $O(n \log n)$
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

/// [`fft`]、[`ifft`] で使う回転因子（twiddle factor）を前計算する。
///
/// 長さ $2n+1$ の配列を返す。添字 $0$ は未使用、添字 $2n$ は番兵（値 $1$）。
/// $2$ の冪 $m$（$2 \le m \le n$）ごとに
///
/// $$
/// t_{m+i} = w_m^i \quad (0 \le i < m)
/// $$
///
/// を満たす（$w_m$ は $1$ の原始 $m$ 乗根）。
///
/// # 例
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
///
/// # 計算量
///
/// $O(n)$
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
