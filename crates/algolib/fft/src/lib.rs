use polynomial::Poly;
use std::{iter, marker};
use type_traits::Ring;

pub trait Fftable: Ring + Copy {
    fn root() -> Self;
    fn root_inv() -> Self;
    fn lg_ord() -> usize;
    fn div_assign_by_usize(&mut self, den: usize);

    fn root_seq<Tag: DirectionTag>() -> Vec<Self> {
        let mut root = Tag::root::<Self>();
        let mut res = Vec::with_capacity(Self::lg_ord());
        for _ in 0..Self::lg_ord() {
            res.push(root);
            root *= root;
        }
        res.push(root);
        res.reverse();
        res
    }
}

#[must_use]
pub fn multiply<T>(a: Poly<T>, b: Poly<T>) -> Poly<T>
where
    T: Fftable + std::fmt::Debug,
{
    let mut a = a.into_inner();
    let mut b = b.into_inner();
    let n = (a.len() + b.len()).next_power_of_two();
    a.resize(n, T::zero());
    b.resize(n, T::zero());
    a = fft(&a, marker::PhantomData::<Forward>);
    b = fft(&b, marker::PhantomData::<Forward>);
    let mut c = a
        .iter()
        .copied()
        .zip(b.iter().copied())
        .map(|(x, y)| x * y)
        .collect::<Vec<_>>();
    c = fft(&c, marker::PhantomData::<Backward>);
    c.iter_mut().for_each(|x| x.div_assign_by_usize(n));
    Poly::new(c)
}

#[allow(clippy::many_single_char_names)]
#[must_use]
pub fn fft<T, Tag>(a: &[T], _tag: marker::PhantomData<Tag>) -> Vec<T>
where
    T: Fftable + std::fmt::Debug,
    Tag: DirectionTag,
{
    let n = a.len();
    if 1 < n {
        assert!(n.is_power_of_two());
        let mut a = bit_reverse(a);
        for (d, &root) in iter::successors(Some(1), |x| Some(x * 2))
            .take_while(|&d| d != n)
            .zip(T::root_seq::<Tag>()[1..].iter())
        {
            for (i, coeff) in iter::successors(Some((0, T::one())), |&(mut i, mut coeff)| {
                i += 1;
                coeff *= root;
                if i % d == 0 {
                    i += d;
                    coeff = T::one();
                }
                Some((i, coeff))
            })
            .take_while(|&(i, _)| i != n)
            {
                let x = a[i];
                let y = a[i + d];
                a[i] = x + y * coeff;
                a[i + d] = x - y * coeff;
            }
        }
        a
    } else {
        a.to_vec()
    }
}

pub trait DirectionTag {
    fn root<T: Fftable>() -> T;
}
pub struct Forward {}
impl DirectionTag for Forward {
    fn root<T: Fftable>() -> T {
        T::root()
    }
}
pub struct Backward {}
impl DirectionTag for Backward {
    fn root<T: Fftable>() -> T {
        T::root_inv()
    }
}

#[must_use]
fn bit_reverse<T: Copy>(a: &[T]) -> Vec<T> {
    assert!(a.len().is_power_of_two());
    let shift = std::mem::size_of::<usize>() as u32 * 8 - a.len().trailing_zeros();
    (0..a.len())
        .map(|i| a[if i == 0 { 0 } else { i.reverse_bits() >> shift }])
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use fp::{fp_vec, Mod998244353, F998244353};
    use rand::prelude::*;
    use test_case::test_case;
    use type_traits::Constant;

    type Fp = F998244353;
    impl Fftable for Fp {
        fn root() -> Fp {
            Fp::new(3).pow(7 * 17)
        }
        fn root_inv() -> Fp {
            Fp::root().inv()
        }
        fn lg_ord() -> usize {
            23
        }
        fn div_assign_by_usize(&mut self, den: usize) {
            *self /= Fp::new(den as i64)
        }
    }

    #[test_case(&[0] => vec![0])]
    #[test_case(&[0, 1] => vec![0, 1])]
    #[test_case(&[0, 1, 2, 3] => vec![0, 2, 1, 3])]
    #[test_case(&[0, 1, 2, 3, 4, 5, 6, 7] => vec![0, 4, 2, 6, 1, 5, 3, 7])]
    fn test_bit_reverse_(a: &[u32]) -> Vec<u32> {
        bit_reverse(a)
    }

    #[test_case(fp_vec![0, 1, 2, 3] => fp_vec![0, 4, 8, 12])]
    #[test_case(fp_vec![1, 1, 0, 0] => fp_vec![4, 4, 0, 0])]
    #[test_case(fp_vec![0, 0, 1, 1, 1, 0, 0, 0] => fp_vec![0, 0, 8, 8, 8, 0, 0, 0])]
    fn test_transform(a: Vec<Fp>) -> Vec<Fp> {
        let b = fft(&a, marker::PhantomData::<Forward>);
        fft(&b, marker::PhantomData::<Backward>)
    }

    #[test_case(fp_vec![], fp_vec![] => fp_vec![])]
    #[test_case(fp_vec![], fp_vec![99, 999] => fp_vec![])]
    #[test_case(fp_vec![10], fp_vec![100] => fp_vec![1000])]
    #[test_case(fp_vec![1, 1], fp_vec![1, 1, 1] => fp_vec![1, 2, 2, 1])]
    #[test_case(fp_vec![1, 2], fp_vec![1, 4, 5] => fp_vec![1, 6, 13, 10])]
    #[test_case(fp_vec![1, 4, 20], fp_vec![5, 3, 2, 1] => fp_vec![5, 23, 114, 69, 44, 20])]
    fn test_multiply_hand(a: Vec<Fp>, b: Vec<Fp>) -> Vec<Fp> {
        multiply(Poly::new(a), Poly::new(b)).into_inner()
    }

    #[test]
    fn test_multiply_random() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let l = rng.gen_range(0, 42);
            let m = rng.gen_range(0, 42);
            let a = Poly::new(
                iter::repeat_with(|| rng.gen_range(0, <Mod998244353 as Constant>::VALUE))
                    .take(l)
                    .map(Fp::new)
                    .collect::<Vec<Fp>>(),
            );
            let b = Poly::new(
                iter::repeat_with(|| rng.gen_range(0, <Mod998244353 as Constant>::VALUE))
                    .take(m)
                    .map(Fp::new)
                    .collect::<Vec<Fp>>(),
            );
            let result = multiply(a.clone(), b.clone());
            let expected = a.clone() * b.clone();
            println!("a = {:?}", &a);
            println!("b = {:?}", &b);
            println!("result = {:?}", &result);
            println!("expected = {:?}", &expected);
            println!();
            assert_eq!(result, expected);
        }
    }
}
