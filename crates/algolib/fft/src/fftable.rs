use super::Fftable;
use fp::F998244353;

impl Fftable for F998244353 {
    fn root() -> F998244353 {
        F998244353::new(3).pow(7 * 17)
    }
    fn root_inv() -> F998244353 {
        F998244353::root().inv()
    }
    fn lg_ord() -> usize {
        23
    }
    fn div_assign_by_usize(&mut self, den: usize) {
        *self /= F998244353::new(den as i64)
    }
}
