//! 形式べき級数（FPS）演算。多項式乗算・逆元・除算・評価を FFT で高速化。

use fp::Fp;
use fp::fp_new;
use fp_fft::fft;
use fp_fft::ifft;

/// $f^{-1} \bmod x^m$ を計算する。
///
/// # 計算量
///
/// $m$ が $2$ べきのとき、 $10 \mathcal{F}_m$
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

/// 多項式 $a$ と $b$ を乗算。
///
/// * 出力の trailing $0$ は全て削除されれる
/// * 特に、$0$ 多項式は空が返される
///
/// 計算量 $O(n \log n)$。
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
/// assert_eq!(c.as_slice(), [fp_new(3), fp_new(10), fp_new(8)]);
/// ```
pub fn poly_mul<const P: u64>(mut a: Vec<Fp<P>>, mut b: Vec<Fp<P>>) -> Vec<Fp<P>> {
    if a.is_empty() {
        return b;
    }
    if b.is_empty() {
        return a;
    }
    let len = a.len() + b.len() - 1;
    let fft_len = len.next_power_of_two() * 2;
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

/// 多項式除算。$a = bq + r$ を満たす $(q, r)$ を返す（$\deg(r) < \deg(b)$）。
///
/// 計算量 $O(n \log n)$。
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

/// 多項式 $f$ を複数点 $x_1, \ldots, x_n$ で評価。$[f(x_1), \ldots, f(x_n)]$ を返す。
///
/// 分割統治 + FFT、計算量 $O(n \log^2 n)$。
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
