use {
    super::Convolution,
    fp::{Fp, Mod},
};

/// 多項式の、積に関する逆元を mod x ^ `precision` で返します。
///
/// # 制約
///
/// * `a[0]` が 0 でない。
///
///
/// # 出力の要件
///
/// * a と出力の多項式としての積が、mod x ^ `precision` で 1
///
pub fn polynomial_inverse<M: Mod>(mut a: Vec<Fp<M>>, precision: usize) -> Vec<Fp<M>>
where
    Fp<M>: Convolution,
{
    let scalar = a[0];
    let scalar_recip = scalar.recip();
    assert_ne!(scalar, Fp::new(0), "定数項が 0 はだめです。");
    a.iter_mut().for_each(|x| *x *= scalar_recip);
    let mut b = vec![Fp::<M>::new(1)];
    while b.len() < 2 * precision {
        let next_precision = 2 * b.len();
        let a = a[..a.len().min(next_precision)].to_vec();
        let mut tmp = Fp::convolution(a, b.clone());
        tmp.iter_mut().for_each(|x| *x = -*x);
        tmp[0] += Fp::new(2);
        b = Fp::convolution(b, tmp);
        b.truncate(next_precision);
        b.resize(next_precision, Fp::new(0));
    }
    b.truncate(precision);
    b.iter_mut().for_each(|x| *x *= scalar_recip);
    b
}

#[cfg(test)]
mod tests {
    use {
        super::{super::Convolution, polynomial_inverse},
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::iter::{once, repeat, repeat_with},
    };

    #[test]
    fn test_polynomial_inverse() {
        use fp::F998244353 as Fp;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let k = rng.gen_range(0..6);
            let l = rng.gen_range(0..6);
            let n = 1 << k;
            let precision = 1 << l;
            let a = once(Fp::new(rng.gen_range(1..Fp::P)))
                .chain(repeat_with(|| Fp::new(rng.gen_range(0..3))))
                .take(n)
                .collect_vec();
            let result = polynomial_inverse(a.clone(), precision);
            let mut expected_to_be_one = Fp::convolution(a, result.clone());
            expected_to_be_one.truncate(precision);
            assert_eq!(
                expected_to_be_one,
                once(Fp::new(1))
                    .chain(repeat(Fp::new(0)))
                    .take(precision)
                    .collect_vec()
            );
        }
    }
}
