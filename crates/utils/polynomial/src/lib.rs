#![warn(missing_docs)]
//! [`Add`] と [`Mul`] がなす環上の多項式です。中身は [`Vec`] です。
//!
//! # 構築
//!
//! [`new`] で構築して、[`into_inner`] で中身を取ります。
//! [`new`] は trailing zeros を消去することに注意です。
//!
//! ```
//! use polynomial::*;
//! let mut f = Poly::new(vec![1, 0, 2]);
//! let mut a = f.into_inner();
//! a.sort_by_key(|&x| std::cmp::Reverse(x));
//! let f = Poly::new(a);
//! assert_eq!(f, Poly::new(vec![2, 1]));
//! ```
//!
//! # トレイト実装
//!
//! - [`ops`] 系: [`Add`], [`AddAssign`], [`Sub`], [`SubAssign`], [`Mul`], [`MulAssign`]
//! - [`fmt`] 系: [`Debug`]
//! - [`type_traits`] 系: [`Zero`], [`One`]
//!
//!
//! # ライブラリ連携
//!
//! [`fp`] に対応しています。
//!
//! ```
//! use polynomial::*;
//! type Fp = fp::F998244353;
//! assert_eq!(
//!     Poly::new(vec![Fp::new(1), Fp::new(1)]).pow(2),
//!     Poly::new(vec![Fp::new(1), Fp::new(2), Fp::new(1)])
//! );
//! ```
//!
//! [`new`]: struct.Poly.html#method.new
//! [`into_inner`]: struct.Poly.html#method.into_inner
//!
//! [`type_traits`]: ../type_traits/index.html
//! [`Zero`]: ../type_traits/trait.Zero.html
//! [`One`]: ../type_traits/trait.One.html
//! [`fp`]: ../fp/indx.html
//!
//! [`slice`]: https://doc.rust-lang.org/std/primitive/slice.html
//! [`ops`]: https://doc.rust-lang.org/std/ops/index.html
//! [`fmt`]: https://doc.rust-lang.org/std/fmt/index.html
//! [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
//! [`Add`]: https://doc.rust-lang.org/std/ops/trait.Add.html
//! [`Sub`]: https://doc.rust-lang.org/std/ops/trait.Sub.html
//! [`Mul`]: https://doc.rust-lang.org/std/ops/trait.Mul.html
//! [`AddAssign`]: https://doc.rust-lang.org/std/ops/trait.AddAssign.html
//! [`SubAssign`]: https://doc.rust-lang.org/std/ops/trait.SubAssign.html
//! [`MulAssign`]: https://doc.rust-lang.org/std/ops/trait.MulAssign.html
//! [`Debug`]: https://doc.rust-lang.org/std/ops/trait.Debug.html

use type_traits::{One, Ring, Zero};

mod arith;

/// 多項式です。値型は [`Copy`](https://doc.rust-lang.org/std/ops/trait.Debug.html)
/// と [`Ring`](../type_traits/traits.Ring.html) を満たすことが要求されます。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Poly<T>(Vec<T>);

impl<T: Ring + Copy> Poly<T> {
    /// [`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html) から trailing zeros を消して
    /// キャストします。
    pub fn new(mut src: Vec<T>) -> Self {
        Poly::remove_trailig_zeros(&mut src);
        Poly(src)
    }

    /// [`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html) にキャストします。
    pub fn into_inner(self) -> Vec<T> {
        self.0
    }

    /// 塁乗をします。
    pub fn pow(mut self, mut b: u64) -> Poly<T> {
        let mut res = Poly::one();
        while b != 0 {
            if b % 2 == 1 {
                res *= self.clone();
            }
            self *= self.clone();
            b /= 2
        }
        res
    }

    fn remove_trailig_zeros(a: &mut Vec<T>) {
        while a.last().map(T::is_zero).unwrap_or(false) {
            a.pop();
        }
    }
}

impl<T: Ring + Copy> Default for Poly<T> {
    fn default() -> Poly<T> {
        Poly(Vec::new())
    }
}

impl<T: Ring + Copy> Zero for Poly<T> {
    fn zero() -> Poly<T> {
        Poly(Vec::new())
    }
    fn times(mut self, n: u64) -> Poly<T> {
        self.times_assign(n);
        self
    }
    fn times_assign(&mut self, n: u64) {
        self.0.iter_mut().for_each(|x| *x = x.times(n));
    }
    fn from_u64(n: u64) -> Poly<T> {
        if n == 0 {
            Poly::new(Vec::new())
        } else {
            Poly(vec![T::from_u64(n)])
        }
    }
}

impl<T: Ring + Copy> One for Poly<T> {
    fn one() -> Poly<T> {
        Poly(vec![T::one()])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Fp = fp::F998244353;

    #[test]
    fn test_call_method_of_vec() {
        let mut f = Poly::new(vec![1, 0, 2]);
        f.0.sort();
        assert_eq!(f, Poly::new(vec![0, 1, 2]));
    }

    #[test]
    fn test_add_hand() {
        // len(a) < len(b)
        assert_eq!(
            Poly::new(vec![0, 1]) + Poly::new(vec![2, 3, 4]),
            Poly::new(vec![2, 4, 4])
        );

        // len(a) > len(b)
        assert_eq!(
            Poly::new(vec![0, 1, 2]) + Poly::new(vec![3, 4]),
            Poly::new(vec![3, 5, 2])
        );

        // Trailing zeros
        assert_eq!(
            Poly::new(vec![0, 1, 2]) + Poly::new(vec![0, 1, -2]),
            Poly::new(vec![0, 2])
        );
        assert_eq!(
            Poly::new(vec![0, 1, 2]) + Poly::new(vec![0, -1, -2]),
            Poly::new(Vec::new())
        );
    }

    #[test]
    fn test_sub_hand() {
        // len(a) < len(b)
        assert_eq!(
            Poly::new(vec![0, 1]) - Poly::new(vec![2, 3, 4]),
            Poly::new(vec![-2, -2, -4])
        );

        // len(a) > len(b)
        assert_eq!(
            Poly::new(vec![0, 1, 2]) - Poly::new(vec![3, 4]),
            Poly::new(vec![-3, -3, 2])
        );

        // Trailing zeros
        assert_eq!(
            Poly::new(vec![0, 1, 2]) - Poly::new(vec![0, -1, 2]),
            Poly::new(vec![0, 2])
        );
        assert_eq!(
            Poly::new(vec![0, 1, 2]) - Poly::new(vec![0, 1, 2]),
            Poly::new(Vec::new())
        );
    }

    #[test]
    fn test_mul_hand() {
        assert_eq!(
            Poly::new(vec![0, 1]) * Poly::new(vec![2, 3, 4]),
            Poly::new(vec![0, 2, 3, 4])
        );

        assert_eq!(
            Poly::new(vec![0, 1, 2]) * Poly::new(vec![3, 4]),
            Poly::new(vec![0, 3, 10, 8])
        );

        assert_eq!(
            Poly::new(vec![0, 1, 2]) * Poly::new(vec![0, -1, 2]),
            Poly::new(vec![0, 0, -1, 0, 4])
        );
        assert_eq!(
            Poly::new(vec![0, 1, 2]) * Poly::new(vec![0, 1, 2]),
            Poly::new(vec![0, 0, 1, 4, 4])
        );
    }

    #[test]
    fn test_pow_hand() {
        assert_eq!(Poly::new(vec![1, 2]).pow(0), Poly::one());
        assert_eq!(Poly::new(vec![1, 2]).pow(1), Poly::new(vec![1, 2]));
        assert_eq!(Poly::new(vec![1, 2]).pow(2), Poly::new(vec![1, 4, 4]));
        assert_eq!(Poly::new(vec![1, 2]).pow(3), Poly::new(vec![1, 6, 12, 8]));
    }

    #[test]
    fn test_fp() {
        assert_eq!(Poly::new(vec![Fp::new(1), Fp::new(2)]).pow(0), Poly::one());
        assert_eq!(
            Poly::new(vec![Fp::new(1), Fp::new(2)]).pow(1),
            Poly::new(vec![Fp::new(1), Fp::new(2)])
        );
        assert_eq!(
            Poly::new(vec![Fp::new(1), Fp::new(2)]).pow(2),
            Poly::new(vec![Fp::new(1), Fp::new(4), Fp::new(4)])
        );
        assert_eq!(
            Poly::new(vec![Fp::new(1), Fp::new(2)]).pow(3),
            Poly::new(vec![Fp::new(1), Fp::new(6), Fp::new(12), Fp::new(8)])
        );
    }
}
