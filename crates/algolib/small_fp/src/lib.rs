use fp::{Fp, Mod};

pub struct SmallInversions<T>(Vec<Fp<T>>);
impl<T: Mod> SmallInversions<T> {
    pub fn new(n: u32) -> Self {
        let mut vec = vec![Fp::new(1); n as usize];
        for x in (2..n).map(|x| x as i64) {
            let q = Fp::<T>::r#mod() / x;
            let r = Fp::<T>::r#mod() % x;
            vec[x as usize] = -Fp::new(q) * vec[r as usize];
        }
        Self(vec)
    }
    pub fn inv_small(&self, n: u32) -> Fp<T> {
        self.0[n as usize]
    }
    pub fn inv_large(&self, n: i64) -> Fp<T> {
        if 0 <= n && n < self.0.len() as i64 {
            self.inv_small(n as u32)
        } else {
            let n = Fp::<T>::new(n).into_inner();
            let m = Fp::<T>::r#mod();
            let q = m / n;
            let r = m % n;
            -Fp::new(q) * self.inv_large(r)
        }
    }
}

pub struct SmallestPrimeFactors(Vec<u32>);
impl SmallestPrimeFactors {
    pub fn new(n: u32) -> Self {
        let mut vec = (0..n).collect::<Vec<_>>();
        for p in (2..).take_while(|&p| p * p < n) {
            let mut i = 2 * p;
            while i < n {
                if vec[i as usize] == i {
                    vec[i as usize] = p
                }
                i += p;
            }
        }
        Self(vec)
    }
    pub fn get(&self, n: u32) -> u32 {
        assert!(n != 0 && n < self.0.len() as u32);
        self.0[n as usize]
    }
    pub fn factorize(&self, mut n: u32) -> Vec<(u32, u32)> {
        let mut ans = Vec::new();
        while n != 1 {
            let p = self.0[n as usize];
            if ans.last().map_or(true, |&(p1, _)| p1 != p) {
                ans.push((p, 0));
            }
            ans.last_mut().unwrap().1 += 1;
            n /= p;
        }
        ans
    }
}

#[cfg(test)]
mod tests {
    use super::{SmallInversions, SmallestPrimeFactors};

    type Fp = fp::F998244353;

    #[test]
    fn test_inv_small() {
        let si = SmallInversions::new(1000);
        (1..1000).for_each(|x| assert_eq!(Fp::new(x as i64).inv(), si.inv_small(x)));
    }

    #[test]
    fn test_inv_large_less_than_mod() {
        let si = SmallInversions::new(1000);
        (1..1000)
            .map(|x| x + 100_000_000)
            .for_each(|x| assert_eq!(Fp::new(x).inv(), si.inv_large(x)));
    }

    #[test]
    fn test_inv_large_greater_than_mod() {
        let si = SmallInversions::new(1000);
        (1..1000i64)
            .map(|x| x + 100_000_000_000)
            .for_each(|x| assert_eq!(Fp::new(x).inv(), si.inv_large(x)));
    }

    #[test]
    fn test_smallest_prime_factor() {
        let sp = SmallestPrimeFactors::new(20);
        assert_eq!(sp.get(1), 1);
        assert_eq!(sp.get(2), 2);
        assert_eq!(sp.get(3), 3);
        assert_eq!(sp.get(4), 2);
        assert_eq!(sp.get(5), 5);
        assert_eq!(sp.get(6), 2);
        assert_eq!(sp.get(7), 7);
        assert_eq!(sp.get(8), 2);
        assert_eq!(sp.get(9), 3);
        assert_eq!(sp.get(10), 2);
        assert_eq!(sp.get(11), 11);
        assert_eq!(sp.get(12), 2);
        assert_eq!(sp.get(13), 13);
        assert_eq!(sp.get(14), 2);
        assert_eq!(sp.get(15), 3);
        assert_eq!(sp.get(16), 2);
        assert_eq!(sp.get(17), 17);
        assert_eq!(sp.get(18), 2);
        assert_eq!(sp.get(19), 19);
    }

    #[test]
    fn test_factorize() {
        let sp = SmallestPrimeFactors::new(20);
        assert_eq!(sp.factorize(1), Vec::new());
        assert_eq!(sp.factorize(2), vec![(2, 1)]);
        assert_eq!(sp.factorize(3), vec![(3, 1)]);
        assert_eq!(sp.factorize(4), vec![(2, 2)]);
        assert_eq!(sp.factorize(5), vec![(5, 1)]);
        assert_eq!(sp.factorize(6), vec![(2, 1), (3, 1)]);
        assert_eq!(sp.factorize(7), vec![(7, 1)]);
        assert_eq!(sp.factorize(8), vec![(2, 3)]);
        assert_eq!(sp.factorize(9), vec![(3, 2)]);
        assert_eq!(sp.factorize(10), vec![(2, 1), (5, 1)]);
        assert_eq!(sp.factorize(11), vec![(11, 1)]);
        assert_eq!(sp.factorize(12), vec![(2, 2), (3, 1)]);
        assert_eq!(sp.factorize(13), vec![(13, 1)]);
        assert_eq!(sp.factorize(14), vec![(2, 1), (7, 1)]);
        assert_eq!(sp.factorize(15), vec![(3, 1), (5, 1)]);
        assert_eq!(sp.factorize(16), vec![(2, 4)]);
        assert_eq!(sp.factorize(17), vec![(17, 1)]);
        assert_eq!(sp.factorize(18), vec![(2, 1), (3, 2)]);
        assert_eq!(sp.factorize(19), vec![(19, 1)]);
    }
}
