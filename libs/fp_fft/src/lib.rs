use fp::{Fp, fp};

const TWIDDLES_LEN: usize = 64;

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

const fn build_twiddle_factors<const P: u64>(root: Fp<P>) -> [Fp<P>; TWIDDLES_LEN] {
    let mut result = [fp(0); TWIDDLES_LEN];
    let k = (P - 1).trailing_zeros();
    let mut i = k as usize;
    result[i] = root.pow((P - 1) >> k);
    while i != 0 {
        result[i - 1] = result[i].mul(result[i]);
        i -= 1;
    }
    result
}

pub fn fft<const P: u64>(items: &mut [Fp<P>]) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let w = const { build_twiddle_factors(find_primitive_root()) };
    let mut n = items.len();
    while n != 1 {
        let w = w[n.trailing_zeros() as usize];
        for chunk in items.chunks_mut(n) {
            let (a, b) = chunk.split_at_mut(n / 2);
            let mut coeff = fp(1);
            for (a, b) in a.iter_mut().zip(b) {
                (*a, *b) = (*a + *b, (*a - *b) * coeff);
                coeff *= w;
            }
        }
        n /= 2;
    }
}

pub fn ifft<const P: u64>(items: &mut [Fp<P>]) {
    assert!(items.len().is_power_of_two());
    assert!(items.len().trailing_zeros() <= (P - 1).trailing_zeros());
    let w = const { build_twiddle_factors(find_primitive_root().inv()) };
    let mut n = 2;
    while n <= items.len() {
        let w = w[n.trailing_zeros() as usize];
        for chunk in items.chunks_mut(n) {
            let (a, b) = chunk.split_at_mut(n / 2);
            let mut coeff = fp(1);
            for (a, b) in a.iter_mut().zip(b) {
                (*a, *b) = (*a + *b * coeff, *a - *b * coeff);
                coeff *= w;
            }
        }
        n *= 2;
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
        let twiddle_factors = build_twiddle_factors::<998_244_353>(fp(3));
        assert_eq!(twiddle_factors[0], fp(1));
        assert_eq!(twiddle_factors[1], -fp(1));
    }
}
