use std::{fmt, iter, ops, slice};

#[derive(Debug, Clone)]
pub struct Factorial<T> {
    table: Vec<T>,
    inverse: Vec<T>,
}

impl<T> Factorial<T>
where
    T: Clone + fmt::Debug + ops::Mul<Output = T> + ops::Div<Output = T>,
{
    pub fn new(len: usize, from_usize: impl Fn(usize) -> T) -> Self {
        if len == 0 {
            Self {
                table: Vec::new(),
                inverse: Vec::new(),
            }
        } else {
            let mut table = vec![from_usize(1); len];
            for i in 1..len {
                table[i] = table[i - 1].clone() * from_usize(i);
            }
            let mut inverse = vec![from_usize(1); len];
            inverse[len - 1] = from_usize(1) / table[len - 1].clone();
            for i in (1..len).rev() {
                inverse[i - 1] = inverse[i].clone() * from_usize(i);
            }
            Self { table, inverse }
        }
    }

    pub fn inv(&self, i: usize) -> T {
        self.inverse[i].clone()
    }

    pub fn falling(&self, n: usize, k: usize) -> T {
        assert!(k <= n, "未対応です。0 がほしいでしょうか。");
        assert!(n < self.table.len(), "ちわーす。範囲外でーすｗｗｗ");
        self[n].clone() * self.inv(k)
    }

    pub fn binom(&self, n: usize, k: usize) -> T {
        assert!(k <= n, "未対応です。0 がほしいでしょうか。");
        assert!(n < self.table.len(), "ちわーす。範囲外でーすｗｗｗ");
        self[n].clone() * self.inv(k) * self.inv(n - k)
    }

    pub fn multichoose(&self, n: usize, k: usize) -> T {
        self.binom(n + k - 1, k - 1)
    }

    pub fn multinom(&self, a: &[usize]) -> T
    where
        T: iter::Product<T>,
    {
        let n = a.iter().sum::<usize>();
        assert!(n < self.table.len(), "ちわーす。範囲外でーすｗｗｗ");
        self[n].clone() * a.iter().map(|&x| self.inv(x)).product::<T>()
    }
}

impl<T, I> ops::Index<I> for Factorial<T>
where
    I: slice::SliceIndex<[T]>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        &self.table[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    constant::define_constant! { type Mod97: i16 = 97; }
    type F97 = fp::Fp<Mod97>;

    #[test]
    fn test_f64_hand() {
        let fact = Factorial::new(10, |x| x as f64);
        assert_eq!(fact[0], 1.0);
        assert_eq!(fact[1], 1.0);
        assert_eq!(fact[2], 2.0);
        assert_eq!(fact[3], 6.0);

        assert_eq!(fact.inv(0), 1.0);
        assert_eq!(fact.inv(1), 1.0);
        assert_eq!(fact.inv(2), 0.5);
    }

    #[test]
    fn test_998244353_hand() {
        type Fp = fp::aliases::F998244353;
        let fact = Factorial::new(100, |x| Fp::new(x as i64));

        assert_eq!(fact[0], Fp::one());
        assert_eq!(fact[1], Fp::one());
        assert_eq!(fact[2], Fp::new(2));
        assert_eq!(fact[3], Fp::new(6));

        assert_eq!(fact.inv(0), Fp::one());
        assert_eq!(fact.inv(1), Fp::one());
        assert_eq!(fact.inv(2), Fp::new(499122177));
    }

    #[test]
    fn test_97_binom() {
        type Fp = F97;
        let fact = Factorial::new(90, |x| Fp::new(x as i16));

        let expected = [
            vec![1],
            vec![1, 1],
            vec![1, 2, 1],
            vec![1, 3, 3, 1],
            vec![1, 4, 6, 4, 1],
            vec![1, 5, 10, 10, 5, 1],
        ];
        for (i, v) in expected.iter().enumerate() {
            for (j, &expected) in v.iter().enumerate() {
                println!("(i, j) = {:?}", (i, j));
                assert_eq!(fact.binom(i, j), Fp::new(expected));
            }
        }
    }

    #[test]
    fn test_97_multichoose() {
        type Fp = F97;
        let fact = Factorial::new(90, |x| Fp::new(x as i16));

        assert_eq!(fact.multichoose(80, 1), Fp::one());
        assert_eq!(fact.multichoose(80, 2), Fp::new(81));
        assert_eq!(fact.multichoose(2, 3), Fp::new(6));
    }

    #[test]
    fn test_97_multinom() {
        type Fp = F97;
        let fact = Factorial::new(90, |x| Fp::new(x as i16));

        assert_eq!(fact.multinom(&[]), Fp::one());
        assert_eq!(fact.multinom(&[88]), Fp::one());
        assert_eq!(fact.multinom(&[1, 88]), Fp::new(89));
        assert_eq!(fact.multinom(&[1, 1, 1, 1, 1]), Fp::new(120));
        assert_eq!(fact.multinom(&[1, 2, 3]), Fp::new(60));
        assert_eq!(fact.multinom(&[2, 2, 3]), Fp::new(210));
    }
}
