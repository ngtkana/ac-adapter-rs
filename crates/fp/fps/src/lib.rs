use fp::{Fp, Mod};

pub trait Fourier: Sized {
    fn fourier(a: &mut [Self]);
    fn fourier_inverse(a: &mut [Self]);
    fn convolution_inplace_power_of_two(a: &mut [Self], b: &mut [Self]);
    fn convolution_power_of_two(mut a: Vec<Self>, mut b: Vec<Self>) -> Vec<Self> {
        Fourier::convolution_inplace_power_of_two(&mut a, &mut b);
        a
    }
}

#[macro_export]
macro_rules! define_fourier {
    ($(($mod: ident, $Fp: ty, $prim_root: expr, $e: expr),)*) => {$(
        mod $mod {
            use super::Fourier;
            type Fp = $Fp;

            static mut ROOT: Vec<Fp> = Vec::new();
            static mut ROOT_RECIP: Vec<Fp> = Vec::new();

            fn init() {
                unsafe {
                    if ROOT.is_empty() {
                        for i in 0..=$e-2 {
                            let x = -Fp::new(3).pow((Fp::P - 1) >> (i + 2));
                            ROOT.push(x);
                            ROOT_RECIP.push(x.recip());
                        }
                    }
                }
            }

            impl Fourier for Fp {
                fn fourier(a: &mut [Fp]) {
                    init();
                    unsafe {
                        super::fourier(a, &ROOT);
                    }
                }
                fn fourier_inverse(a: &mut [Fp]) {
                    init();
                    unsafe {
                        super::fourier_inverse(a, &ROOT_RECIP);
                    }
                }
                fn convolution_inplace_power_of_two(a: &mut [Fp], b: &mut [Fp]) {
                    init();
                    unsafe {
                        super::convolution_inplace_power_of_two(a, b, &ROOT, &ROOT_RECIP);
                    }
                }
            }
        }
    )*};
}

define_fourier! {
    (fourier_998244353, fp::F998244353, 3, 23),
    (fourier_1012924417, fp::F1012924417, 5, 21),
    (fourier_924844033, fp::F924844033, 5, 21),
}

fn fourier<M: Mod>(a: &mut [Fp<M>], root: &[Fp<M>]) {
    let n = a.len();
    let mut d = a.len() / 2;
    while d != 0 {
        let mut coeff = Fp::new(1);
        for (i, t) in (0..n).step_by(2 * d).zip(1u32..) {
            for (i, j) in (i..i + d).zip(i + d..) {
                let x = a[i];
                let y = a[j] * coeff;
                a[i] = x + y;
                a[j] = x - y;
            }
            coeff *= root[t.trailing_zeros() as usize];
        }
        d /= 2;
    }
}

fn fourier_inverse<M: Mod>(a: &mut [Fp<M>], root_recip: &[Fp<M>]) {
    let n = a.len();
    let mut d = 1;
    while d != n {
        let mut coeff = Fp::new(1);
        for (i, t) in (0..n).step_by(2 * d).zip(1u32..) {
            for (i, j) in (i..i + d).zip(i + d..) {
                let x = a[i];
                let y = a[j];
                a[i] = x + y;
                a[j] = (x - y) * coeff;
            }
            coeff *= root_recip[t.trailing_zeros() as usize];
        }
        d *= 2;
    }
    let d = Fp::from(a.len()).recip();
    a.iter_mut().for_each(|x| *x *= d);
}

fn convolution_inplace_power_of_two<M: Mod>(
    a: &mut [Fp<M>],
    b: &mut [Fp<M>],
    root: &[Fp<M>],
    root_recip: &[Fp<M>],
) {
    assert!(a.len().is_power_of_two());
    assert!(b.len().is_power_of_two());
    fourier(a, root);
    fourier(b, root);
    a.iter_mut().zip(b.iter()).for_each(|(x, y)| *x *= *y);
    fourier_inverse(a, root_recip);
}

#[cfg(test)]
mod test {
    use std::iter::repeat;

    use {
        super::Fourier,
        fp::F998244353 as Fp,
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::iter::repeat_with,
    };

    #[test]
    fn test_convolution_power_of_two() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let k = rng.gen_range(0..8);
            let n = 1 << k;
            let a = repeat_with(|| Fp::new(rng.gen_range(0..Fp::P)))
                .take(n)
                .chain(repeat(Fp::new(0)).take(n))
                .collect_vec();
            let b = repeat_with(|| Fp::new(rng.gen_range(0..Fp::P)))
                .take(n)
                .chain(repeat(Fp::new(0)).take(n))
                .collect_vec();
            let result = Fp::convolution_power_of_two(a.clone(), b.clone());
            let mut expected = vec![Fp::new(0); 2 * n];
            for i in 0..n {
                for j in 0..n {
                    expected[i + j] += a[i] * b[j];
                }
            }
            assert_eq!(result, expected);
        }
    }
}
