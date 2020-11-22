use {
    fp::{Fp, Mod},
    std::ops::{Bound, RangeBounds},
};

// TODO: mod <= n バージョンもつくります。
pub struct Fact<T>(pub Vec<Fp<T>>, pub Vec<Fp<T>>);
impl<T: Mod> Fact<T> {
    pub fn new(n: usize) -> Self {
        if n == 0 {
            Self(Vec::new(), Vec::new())
        } else {
            let a = std::iter::once(1)
                .chain(1..n as i64)
                .map(Fp::new)
                .scan(Fp::new(1), |state, x| {
                    *state *= x;
                    Some(*state)
                })
                .collect::<Vec<_>>();
            let mut b = vec![Fp::new(0); n];
            b[n - 1] = a[n - 1].inv();
            (1..n)
                .rev()
                .for_each(|i| b[i - 1] = b[i] * Fp::new(i as i64));
            assert_eq!(b[0], Fp::new(1));
            Self(a, b)
        }
    }
    pub fn binom(&self, n: usize, k: usize) -> Fp<T> {
        if n < k {
            Fp::new(0)
        } else {
            assert!(n < self.0.len());
            self.0[n] * self.1[k] * self.1[n - k]
        }
    }
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Fp<T> {
        use Bound::{Excluded, Included, Unbounded};
        let s = match range.start_bound() {
            Unbounded => 0,
            Included(&x) => x,
            Excluded(&x) => x + 1,
        };
        let t = match range.end_bound() {
            Excluded(&x) => x - 1,
            Included(&x) => x,
            Unbounded => panic!("Semantically no upper bound in Fact"),
        };
        if s == 0 {
            self.0[t + 1]
        } else {
            self.0[t + 1] * self.1[s]
        }
    }
}
pub fn binom_table<T: Mod>(n: usize) -> Vec<Vec<Fp<T>>> {
    let mut ans = Vec::new();
    if n == 0 {
        ans
    } else {
        ans.push(vec![Fp::new(1)]);
        for _ in 0..n - 1 {
            let mut v = ans.last().unwrap().clone();
            v.push(Fp::new(0));
            for i in (0..v.len() - 1).rev() {
                let x = v[i];
                v[i + 1] += x;
            }
            ans.push(v);
        }
        ans
    }
}

#[cfg(test)]
mod tests {
    use fp::{Fp, Mod};
    fp::define_fp!(F1009, Mod1009, 1009);

    #[test]
    fn test_fact() {
        type Mod = Mod1009;
        type Fp = F1009;
        let fact = super::Fact::<Mod>::new(Fp::r#mod() as usize);
        let binom = super::binom_table::<Mod>(Fp::r#mod() as usize);
        binom
            .iter()
            .enumerate()
            .map(|(i, v)| v.iter().enumerate().map(move |(j, &x)| (i, j, x)))
            .flatten()
            .for_each(|(i, j, x)| assert_eq!(fact.binom(i, j), x, "Binom({}, {})", i, j,));
    }
}
