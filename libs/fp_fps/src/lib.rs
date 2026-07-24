use fp::{Fp, fp};
use fp_fft::{fft, ifft};

pub fn fps_inv<const P: u64>(f: &[Fp<P>], precision: usize) -> Vec<Fp<P>> {
    let fft_len_max = precision.next_power_of_two();
    let mut g = vec![fp(0); precision];
    g[0] = f[0].inv();
    let mut h = vec![fp(0); fft_len_max];
    let mut g_fft = vec![fp(0); fft_len_max];
    let mut fft_len = 2;
    while fft_len <= fft_len_max {
        if fft_len < f.len() {
            h[..fft_len].copy_from_slice(&f[..fft_len]);
        } else {
            h[..f.len()].copy_from_slice(&f[..f.len()]);
            h[f.len()..fft_len].fill(fp(0));
        }
        g_fft[..fft_len / 2].copy_from_slice(&g[..fft_len / 2]);
        fft(&mut h[..fft_len]);
        fft(&mut g_fft[..fft_len]);
        for i in 0..fft_len {
            h[i] = fp(1) - h[i] * g_fft[i];
        }
        ifft(&mut h[..fft_len]);
        h[..fft_len / 2].fill(fp(0));
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

pub fn poly_mul<const P: u64>(mut a: Vec<Fp<P>>, mut b: Vec<Fp<P>>) -> Vec<Fp<P>> {
    let result_len = a.len() + b.len() - 1;
    let fft_len = result_len.next_power_of_two() * 2;
    a.resize(fft_len, fp(0));
    b.resize(fft_len, fp(0));
    fft(&mut a);
    fft(&mut b);
    for i in 0..fft_len {
        a[i] *= b[i];
    }
    ifft(&mut a);
    a.truncate(result_len);
    a
}

pub fn poly_div_rem<const P: u64>(
    mut a: Vec<Fp<P>>,
    mut b: Vec<Fp<P>>,
) -> (Vec<Fp<P>>, Vec<Fp<P>>) {
    assert_ne!(*b.last().unwrap(), fp(0));
    if a.len() < b.len() {
        return (vec![], a);
    }
    let d = b.iter().position(|&b| b != fp(0)).unwrap();
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
    while a.pop_if(|&mut a| a == fp(0)).is_some() {}
    (q, a)
}

pub fn multipoint_evaluation<const P: u64>(f: Vec<Fp<P>>, points: &[Fp<P>]) -> Vec<Fp<P>> {
    let n = points.len();
    let mut prod = vec![vec![]; n * 2];
    for (prod, &point) in prod[n..].iter_mut().zip(points) {
        *prod = vec![-point, fp(1)];
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
        .map(|ans| ans.first().copied().unwrap_or(fp(0)))
        .collect()
}
