//! 巡回群上の離散対数問題を $O(\sqrt N)$ で解く（Baby-step Giant-step 法）。
//!
//! 生成元 $g$ の冪 $g^0, g^1, \ldots, g^{m-1}$（$m = \lceil \sqrt N \rceil$、baby step）を
//! あらかじめ表に持っておく。問い合わせ $x$ に対し $x, xg^{-m}, xg^{-2m}, \ldots$（giant step）を
//! 順に計算し、表に一致する $g^i$ が見つかった時点で $x = g^{km+i}$ が求まる。
//! 位数の上界 $N$ を1つずつ探索する代わりに、baby/giant の2段の $O(\sqrt N)$ 個の候補に絞り込む。
//!
//! # 仕様
//!
//! [`Bsgs::new`] は生成元 `generator`、位数の上界 `ord_upper_bound`、群演算 `mul`・`inv`・`id`
//! （`(generator, mul, inv, id)` が巡回群の演算とその生成元であることが前提）からソルバーを構築する。
//! [`Bsgs::log`] は $x = g^k$ を満たす最小の $k \in [0, N)$ を返す（存在しなければ `None`）。
//! 群演算は型ではなくクロージャで渡すため、法（モジュラス）が実行時に決まる場合にも使える。
//!
//! # 例
//!
//! ```
//! use bsgs::Bsgs;
//!
//! // Z/10Z の乗法群の巡回部分群 {1, 3, 9, 7}（生成元 3, 位数 4）
//! let bsgs = Bsgs::new(3, 4, |x, y| x * y % 10, |x| x * x * x % 10, || 1);
//! assert_eq!(bsgs.log(1), Some(0));
//! assert_eq!(bsgs.log(3), Some(1));
//! assert_eq!(bsgs.log(9), Some(2));
//! assert_eq!(bsgs.log(7), Some(3));
//! assert_eq!(bsgs.log(2), None); // 巡回部分群に属さない値
//!
//! // 生成元でなくても、位数さえ正しければ動く（9 の位数は 2）
//! let bsgs = Bsgs::new(9, 2, |x, y| x * y % 10, |x| x * x * x % 10, || 1);
//! assert_eq!(bsgs.log(9), Some(1));
//! ```
//!
//! # 計算量
//!
//! - 構築（[`Bsgs::new`]）: $O(\sqrt N)$ 回の `mul` 呼び出しと2回の `id` 呼び出し
//! - 問い合わせ（[`Bsgs::log`]）: $O(\sqrt N)$ 回の `mul` 呼び出し
use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::Result;
use std::hash::Hash;
use std::iter::successors;

/// Baby-step Giant-step ソルバー。巡回群 $\langle g \rangle$ 上の離散対数を計算する状態を保持する。
#[derive(Clone)]
pub struct Bsgs<T, Mul> {
    generator: T,
    ord_upper_bound: u64,
    sqrt: u64,
    giant_step_inverse: T,
    map: HashMap<T, u64>,
    mul: Mul,
}
impl<T, Mul> Bsgs<T, Mul>
where
    T: Copy + Hash + Eq,
    Mul: Fn(T, T) -> T,
{
    /// 生成元 `generator`・位数上界 `ord_upper_bound`・群演算 `mul`/`inv`/`id` からソルバーを構築する。
    ///
    /// `(generator, mul, inv, id)` が巡回群の演算とその生成元であることを要求する。
    /// baby step表 $g^0, \ldots, g^{\lceil\sqrt{N}\rceil - 1}$ と giant step用の $g^{-\lceil\sqrt{N}\rceil}$ を構築する。
    ///
    /// # 計算量
    ///
    /// $O(\sqrt N)$ 回の `mul` 呼び出しと2回の `id` 呼び出し（$N$ = `ord_upper_bound`）
    pub fn new<Inv, Id>(generator: T, ord_upper_bound: u64, mul: Mul, inv: Inv, id: Id) -> Self
    where
        Id: Fn() -> T,
        Inv: Fn(T) -> T,
    {
        let sqrt = sqrt(ord_upper_bound);
        let map = successors(Some(id()), |&acc| Some(mul(acc, generator)))
            .take(sqrt as usize)
            .enumerate()
            .map(|(i, x)| (x, i as u64))
            .collect::<HashMap<_, _>>();
        let giant_step_inverse = inv(binary(generator, sqrt, id(), &mul));
        Self {
            generator,
            ord_upper_bound,
            sqrt,
            giant_step_inverse,
            map,
            mul,
        }
    }

    /// $x = g^k$ を満たす最小の $k \in [0, N)$ を返す。存在しなければ `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use bsgs::Bsgs;
    /// let bsgs = Bsgs::new(3, 4, |x, y| x * y % 10, |x| x * x * x % 10, || 1);
    /// assert_eq!(bsgs.log(9), Some(2));
    /// assert_eq!(bsgs.log(2), None);
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(\sqrt N)$ 回の `mul` 呼び出し（$N$ = `ord_upper_bound`）
    pub fn log(&self, mut x: T) -> Option<u64> {
        let mut ans = 0;
        while ans < self.ord_upper_bound {
            match self.map.get(&x) {
                None => {
                    ans += self.sqrt;
                    x = (self.mul)(x, self.giant_step_inverse);
                }
                Some(&i) => return Some(ans + i),
            }
        }
        None
    }
}

#[allow(clippy::missing_fields_in_debug)]
impl<T: Debug, Mul> Debug for Bsgs<T, Mul> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Bsgs")
            .field("generator", &self.generator)
            .field("ord_upper_bound", &self.ord_upper_bound)
            .field("sqrt", &self.sqrt)
            .field("giant_step_inverse", &self.giant_step_inverse)
            .finish()
    }
}

fn binary<T: Copy>(mut a: T, mut b: u64, init: T, f: impl Fn(T, T) -> T) -> T {
    let mut ans = init;
    if b != 0 {
        while b != 1 {
            if (b & 1) == 1 {
                ans = f(ans, a);
            }
            a = f(a, a);
            b /= 2;
        }
        ans = f(ans, a);
    }
    ans
}

fn sqrt(a: u64) -> u64 {
    let f = |x: u64| (a / x + x) >> 1;
    let mut x = (a as f64).sqrt() as u64;
    let mut xn = f(x);
    while x < xn {
        x = xn;
        xn = f(x);
    }
    while xn < x {
        x = xn;
        xn = f(x);
    }
    x
}

#[cfg(test)]
mod tests {
    use super::binary;
    use super::Bsgs;

    #[test]
    fn test_additive() {
        for n in 2..40 {
            let add = |x, y| (x + y) % n;
            let minus = |x| (n - x) % n;
            for g in 0..n {
                let ord = n / gcd(g, n);
                let bsgs = Bsgs::new(g, ord, add, minus, || 0);
                let mut j = 0;
                for i in 0..ord {
                    let k = bsgs.log(j).unwrap();
                    assert_eq!(i, k);
                    j = add(j, g);
                }
            }
        }
    }

    #[test]
    fn test_multiplicative() {
        for n in 2..40 {
            let mul = |x, y| (x * y) % n;
            let pow = |x, y| binary(x, y, 1, mul);
            let ord = totient(n);
            let inv = |x| pow(x, ord - 1);
            for g in (2..n)
                .filter(|&g| gcd(n, g) == 1 && (1..ord).all(|p| pow(g, p) != 1) && pow(g, ord) == 1)
            {
                let bsgs = Bsgs::new(g, ord, mul, inv, || 1);
                let mut j = 1;
                for i in 0..ord {
                    let k = bsgs.log(j).unwrap();
                    assert_eq!(i, k);
                    j = mul(j, g);
                }
            }
        }
    }

    fn gcd(x: u64, y: u64) -> u64 {
        if x == 0 {
            y
        } else {
            gcd(y % x, x)
        }
    }

    fn totient(mut n: u64) -> u64 {
        let mut ans = n;
        for p in 2.. {
            if n < p * p {
                break;
            }
            if n % p == 0 {
                ans -= ans / p;
                while n % p == 0 {
                    n /= p;
                }
            }
        }
        if n != 1 {
            ans -= ans / n;
        }
        ans
    }
}
