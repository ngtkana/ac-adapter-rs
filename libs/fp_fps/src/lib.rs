//! 形式的冪級数（FPS）の演算。多項式の乗算・逆元・除算・多点評価を FFT で高速化する。
//!
//! 多項式の積は係数列の畳み込みに一致するため、[`fp_fft`] の FFT を用いて $O(n \log n)$ で計算できる。
//! 逆元はニュートン法により精度を倍々に伸ばしながら FFT で更新することで $O(n \log n)$ を達成する。
//! 除算・多点評価はこれらを組み合わせて構築する。
//!
//! # 仕様
//!
//! - [`poly_mul`][]: 多項式の積 $ab$
//! - [`fps_inv`][]: 形式的冪級数の逆元 $f^{-1} \bmod x^m$（$f(0) \neq 0$ が前提）
//! - [`poly_div_rem`][]: 多項式の除算 $a = bq + r$（$\deg r < \deg b$）
//! - [`multipoint_evaluation`][]: 多項式の複数点評価 $f(x_1), \ldots, f(x_n)$
//!
//! # 例
//!
//! ```
//! use fp::fp_new;
//! use fp_fps::poly_mul;
//! const P: u64 = 998_244_353;
//! let a = [fp_new::<P>(1), fp_new::<P>(2)]; // 1 + 2x
//! let b = [fp_new::<P>(3), fp_new::<P>(4)]; // 3 + 4x
//! let c = poly_mul::<P>(a.to_vec(), b.to_vec());
//! assert_eq!(c.as_slice(), [fp_new(3), fp_new(10), fp_new(8)]); // (1+2x)(3+4x) = 3+10x+8x^2
//! ```
//!
//! # 計算量
//!
//! - [`poly_mul`][]: $O(n \log n)$
//! - [`fps_inv`][]: $O(n \log n)$
//! - [`poly_div_rem`][]: $O(n \log n)$
//! - [`multipoint_evaluation`][]: $O(n \log^2 n)$

use fp::Fp;
use fp::fp_new;
use fp_fft::fft;
use fp_fft::ifft;

/// 形式的冪級数 $f$ の逆元を $\bmod x^m$ で計算する。
///
/// ニュートン法で精度を倍々に伸ばす。精度 $k$ の逆元 $g_k$ から
/// $g_{2k} = g_k (2 - f g_k) \bmod x^{2k}$ により精度 $2k$ の逆元を求める。
///
/// # 仕様
///
/// $f(0) \neq 0$ のとき、$fg \equiv 1 \pmod{x^m}$（$m = $ `precision`）を満たす
/// 長さ $m$ の係数列 $g$ を返す。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// use fp_fps::fps_inv;
/// const P: u64 = 998_244_353;
/// let f = [fp_new::<P>(1), fp_new::<P>(2)];
/// let g = fps_inv(&f, 2);
/// assert_eq!(g[0], fp_new::<P>(1)); // (1+2x)^{-1} の 0 次項 = 1
/// assert_eq!(g[1], fp_new::<P>(998244351)); // (1+2x)^{-1} の 1 次項 = -2
/// ```
///
/// # 計算量
///
/// $O(n \log n)$（$n = m$）
pub fn fps_inv<const P: u64>(f: &[Fp<P>], precision: usize) -> Vec<Fp<P>> {
    let fft_len_max = precision.next_power_of_two();
    let mut g = vec![fp_new(0); precision];
    g[0] = f[0].inv();
    let mut h = vec![fp_new(0); fft_len_max];
    let mut g_fft = vec![fp_new(0); fft_len_max];
    let mut fft_len = 2;
    while fft_len <= fft_len_max {
        if fft_len < f.len() {
            h[..fft_len].copy_from_slice(&f[..fft_len]);
        } else {
            h[..f.len()].copy_from_slice(&f[..f.len()]);
            h[f.len()..fft_len].fill(fp_new(0));
        }
        g_fft[..fft_len / 2].copy_from_slice(&g[..fft_len / 2]);
        fft(&mut h[..fft_len]);
        fft(&mut g_fft[..fft_len]);
        for i in 0..fft_len {
            h[i] = fp_new(1) - h[i] * g_fft[i];
        }
        ifft(&mut h[..fft_len]);
        h[..fft_len / 2].fill(fp_new(0));
        fft(&mut h[..fft_len]);
        for i in 0..fft_len {
            h[i] *= g_fft[i];
        }
        ifft(&mut h[..fft_len]);
        g[fft_len / 2..fft_len.min(precision)]
            .copy_from_slice(&h[fft_len / 2..fft_len.min(precision)]);
        fft_len *= 2;
    }
    g
}

/// 多項式 $a$ と $b$ の積 $ab$ を計算する。
///
/// 係数列を FFT で周波数領域に写し、要素ごとの積を取ってから逆変換することで、
/// 畳み込み（多項式の積）を $O(n \log n)$ で求める。
///
/// # 仕様
///
/// 出力の末尾の $0$ 係数はすべて取り除く。特に、$a$ または $b$ が $0$ 多項式なら空配列を返す。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// use fp_fps::poly_mul;
/// const P: u64 = 998_244_353;
/// let a = [fp_new(1), fp_new(2)]; // 1 + 2x
/// let b = [fp_new(3), fp_new(4)]; // 3 + 4x
/// let c = poly_mul::<P>(a.to_vec(), b.to_vec());
/// assert_eq!(c.as_slice(), [fp_new(3), fp_new(10), fp_new(8)]); // (1+2x)(3+4x) = 3+10x+8x^2
/// ```
///
/// # 計算量
///
/// $O(n \log n)$（$n = |a| + |b|$）
pub fn poly_mul<const P: u64>(mut a: Vec<Fp<P>>, mut b: Vec<Fp<P>>) -> Vec<Fp<P>> {
    if a.is_empty() {
        return b;
    }
    if b.is_empty() {
        return a;
    }
    let len = a.len() + b.len() - 1;
    let fft_len = len.next_power_of_two();
    a.resize(fft_len, fp_new(0));
    b.resize(fft_len, fp_new(0));
    fft(&mut a);
    fft(&mut b);
    for i in 0..fft_len {
        a[i] *= b[i];
    }
    ifft(&mut a);
    a.truncate(len);
    a
}

/// 多項式除算。$a = bq + r$（$\deg(r) < \deg(b)$）を満たす $(q, r)$ を返す。
///
/// $a, b$ の係数列を反転すると、$q$ の反転は $b$ の反転の逆元と $a$ の反転の積の
/// 先頭 $\deg(a) - \deg(b) + 1$ 項に一致する。これを [`fps_inv`], [`poly_mul`] で求め、
/// 反転を戻してから $r = a - bq$ で余りを計算する。
///
/// # 仕様
///
/// $b$ の最高次係数は $0$ でないことが前提。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// use fp_fps::poly_div_rem;
/// const P: u64 = 998_244_353;
/// let a = [fp_new(1), fp_new(0), fp_new(1)]; // 1 + x^2
/// let b = [fp_new(1), fp_new(1)]; // 1 + x
/// let (q, r) = poly_div_rem::<P>(a.to_vec(), b.to_vec());
/// assert_eq!(q.as_slice(), &[-fp_new(1), fp_new(1)]); // -1 + x
/// assert_eq!(r.as_slice(), &[fp_new(2)]); // 2
/// ```
///
/// # 計算量
///
/// $O(n \log n)$
pub fn poly_div_rem<const P: u64>(
    mut a: Vec<Fp<P>>,
    mut b: Vec<Fp<P>>,
) -> (Vec<Fp<P>>, Vec<Fp<P>>) {
    assert_ne!(*b.last().unwrap(), fp_new(0));
    if a.len() < b.len() {
        return (vec![], a);
    }
    let d = b.iter().position(|&b| b != fp_new(0)).unwrap();
    a[d..].reverse();
    b[d..].reverse();
    let precision = a.len() - b.len() + 1;
    let mut q = poly_mul(
        a[d..a.len().min(d + precision)].to_vec(),
        fps_inv(&b[d..], precision),
    );
    q.truncate(precision);
    q.reverse();
    a[d..].reverse();
    b[d..].reverse();
    let bq = poly_mul(b, q.clone());
    for i in 0..bq.len() {
        a[i] -= bq[i];
    }
    while a.pop_if(|&mut a| a == fp_new(0)).is_some() {}
    (q, a)
}

/// 多項式 $f$ を複数の点 $x_1, \ldots, x_n$ で評価する。
///
/// 分割統治で $\prod_i (x - x_i)$ を部分木ごとに構築し（葉から根へ）、
/// 根から葉に向かって $f$ をその部分木の積多項式で割った余りを伝播させる
/// （[`poly_div_rem`]）ことで、各葉で $f(x_i)$ を得る。
///
/// # 仕様
///
/// $[f(x_1), \ldots, f(x_n)]$ を返す。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// use fp_fps::multipoint_evaluation;
/// const P: u64 = 998_244_353;
/// let f = [fp_new::<P>(1), fp_new::<P>(2)]; // 1 + 2x
/// let points = [fp_new::<P>(0), fp_new::<P>(1)];
/// let result = multipoint_evaluation(f.to_vec(), &points);
/// assert_eq!(result[0], fp_new::<P>(1)); // f(0) = 1
/// assert_eq!(result[1], fp_new::<P>(3)); // f(1) = 3
/// ```
///
/// # 計算量
///
/// $O(n \log^2 n)$
pub fn multipoint_evaluation<const P: u64>(f: Vec<Fp<P>>, points: &[Fp<P>]) -> Vec<Fp<P>> {
    let n = points.len();
    let mut prod = vec![vec![]; n * 2];
    for (prod, &point) in prod[n..].iter_mut().zip(points) {
        *prod = vec![-point, fp_new(1)];
    }
    for i in (1..n).rev() {
        prod[i] = poly_mul(prod[2 * i].clone(), prod[2 * i + 1].clone());
    }
    let mut rem = vec![vec![]; n * 2];
    rem[1] = poly_div_rem(f, prod[1].clone()).1;
    for i in 1..n {
        rem[2 * i] = poly_div_rem(rem[i].clone(), prod[2 * i].clone()).1;
        rem[2 * i + 1] = poly_div_rem(rem[i].clone(), prod[2 * i + 1].clone()).1;
    }
    rem[n..]
        .iter()
        .map(|ans| ans.first().copied().unwrap_or(fp_new(0)))
        .collect()
}
