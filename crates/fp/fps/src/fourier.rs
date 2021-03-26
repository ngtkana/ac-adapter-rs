use super::{Fp, Mod};

pub fn fourier_impl<M: Mod>(a: &mut [Fp<M>], root: &[Fp<M>]) {
    let mut d = a.len() / 2;
    while d != 0 {
        let mut coeff = Fp::new(1);
        for (i, t) in (0..a.len()).step_by(2 * d).zip(1_u32..) {
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
pub fn fourier_inverse_impl<M: Mod>(a: &mut [Fp<M>], root_recip: &[Fp<M>]) {
    let mut d = 1;
    while d != a.len() {
        let mut coeff = Fp::new(1);
        for (i, t) in (0..a.len()).step_by(2 * d).zip(1_u32..) {
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
pub fn convolution_impl<M: Mod>(
    mut a: Vec<Fp<M>>,
    mut b: Vec<Fp<M>>,
    root: &[Fp<M>],
    root_recip: &[Fp<M>],
) -> Vec<Fp<M>> {
    assert!(a.len().is_power_of_two());
    assert!(b.len().is_power_of_two());
    assert_eq!(a.len(), b.len());
    fourier_impl(&mut a, root);
    fourier_impl(&mut b, root);
    a.iter_mut().zip(b.iter()).for_each(|(x, y)| *x *= *y);
    fourier_inverse_impl(&mut a, root_recip);
    a
}
