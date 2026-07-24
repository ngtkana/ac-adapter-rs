use fp::{Fp, fpu};

pub trait Switch {
    type Option<T>;
}
pub enum On {}
pub enum Off {}
impl Switch for On {
    type Option<T> = T;
}
impl Switch for Off {
    type Option<T> = ();
}

pub struct Precalc<const P: u64, Fact: Switch = Off, Finv: Switch = Off, Inv: Switch = Off> {
    len: usize,
    fact: Fact::Option<Vec<Fp<P>>>,
    finv: Finv::Option<Vec<Fp<P>>>,
    inv: Inv::Option<Vec<Fp<P>>>,
}
impl<const P: u64> Precalc<P, Off, Off, Off> {
    pub fn new(len: usize) -> Self {
        Precalc {
            len,
            fact: (),
            finv: (),
            inv: (),
        }
    }
}

// ==========================================
// Build
// ==========================================
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, Off, Finv, Inv> {
    pub fn build_fact(self) -> Precalc<P, On, Finv, Inv> {
        let len = self.len;
        let mut fact = vec![fpu(1); len];
        if 2 < len {
            for i in 2..len {
                fact[i] = fact[i - 1] * fpu(i);
            }
        }
        Precalc {
            len,
            fact,
            finv: self.finv,
            inv: self.inv,
        }
    }
}
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, Off> {
    pub fn build_inv(self) -> Precalc<P, Fact, Finv, On> {
        let len = self.len;
        let mut inv = vec![fpu(1); len];
        if 2 < len {
            for i in 2..len {
                let q = P as usize / i;
                let r = P as usize - i * q;
                inv[i] = inv[r] * -fpu(q);
            }
        }
        Precalc {
            len,
            fact: self.fact,
            finv: self.finv,
            inv,
        }
    }
}
impl<const P: u64, Fact: Switch> Precalc<P, Fact, Off, On> {
    pub fn build_finv_using_inv(self) -> Precalc<P, Fact, On, On> {
        let len = self.len;
        let mut finv = vec![fpu(1); len];
        if 2 <= len {
            for i in 2..len {
                finv[i] = finv[i - 1] * self.inv[i];
            }
        }
        Precalc {
            len,
            fact: self.fact,
            finv,
            inv: self.inv,
        }
    }
}
impl<const P: u64, Inv: Switch> Precalc<P, On, Off, Inv> {
    pub fn build_finv_using_fact(self) -> Precalc<P, On, On, Inv> {
        let len = self.len;
        let mut finv = vec![fpu(1); len];
        if len > 0 {
            finv[len - 1] = self.fact[len - 1].inv();
            if 3 < len {
                for i in (2..len - 1).rev() {
                    finv[i] = finv[i + 1] * fpu(i + 1);
                }
            }
        }
        Precalc {
            len,
            fact: self.fact,
            finv,
            inv: self.inv,
        }
    }
}

// ==========================================
// Query
// ==========================================
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, On, Finv, Inv> {
    pub fn fact(&self, n: usize) -> Fp<P> {
        self.fact[n]
    }
}
impl<const P: u64, Fact: Switch, Inv: Switch> Precalc<P, Fact, On, Inv> {
    pub fn finv(&self, n: usize) -> Fp<P> {
        self.finv[n]
    }
}
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, On> {
    pub fn inv(&self, n: usize) -> Fp<P> {
        self.inv[n]
    }
}
impl<const P: u64, Inv: Switch> Precalc<P, On, On, Inv> {
    pub fn binom(&self, n: usize, k: usize) -> Fp<P> {
        assert!(n < self.len, "n={} out of bounds for len={}", n, self.len);
        assert!(k < self.len, "k={} out of bounds for len={}", k, self.len);
        assert!(k <= n, "k={} must be <= n={}", k, n);
        self.fact[n] * self.finv[k] * self.finv[n - k]
    }
}
