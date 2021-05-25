//! Baby-step giant-step により、巡回群上の離散対数をします。
//!
//! # 使い方
//!
//! [`Bsgs::new`] を使いましょう。
//!
//! ```
//! use bsgs::Bsgs;
//!
//! // ℤ / 10 ℤ の乗法群は、巡回群 { 1, 3, 9, 7 }
//! let bsgs = Bsgs::new(3, 4, |x, y| x * y % 10, |x| x * x * x % 10, || 1);
//!
//! assert_eq!(bsgs.log(1), Some(0));
//! assert_eq!(bsgs.log(3), Some(1));
//! assert_eq!(bsgs.log(9), Some(2));
//! assert_eq!(bsgs.log(7), Some(3));
//!
//! // 存在しないものを指定すると、None です。
//! assert_eq!(bsgs.log(0), None);
//! assert_eq!(bsgs.log(2), None);
//!
//!
//! // 原子根でない場合も、位数さえちゃんとしていればうごきます。
//! let bsgs = Bsgs::new(9, 2, |x, y| x * y % 10, |x| x * x * x %10, || 1);
//! assert_eq!(bsgs.log(1), Some(0));
//! assert_eq!(bsgs.log(9), Some(1));
//!
//! assert_eq!(bsgs.log(0), None);
//! assert_eq!(bsgs.log(2), None);
//! assert_eq!(bsgs.log(3), None);
//! assert_eq!(bsgs.log(7), None);
//! ```
//!
//!
//! # 仕様検討
//!
//! * ちなみに位数の上界は、探索の打ち切りに用いています。
//! * 群の演算は、モジュラス等が動的に与えられる可能性を考えて、型ではなくオブジェクトにしました。
//! * たいてい ℤ / n ℤ
//! の乗法群にしか使わない気がするのですが、それようのユーティルがうまく作れず……
//!
use std::{
    collections::HashMap,
    fmt::{Debug, Formatter, Result},
    hash::Hash,
    iter::successors,
};

/// Baby-stpp giant-step のソルバーです。
///
#[derive(Clone)]
pub struct Bsgs<T, Mul, Inv, Id> {
    generator: T,
    ord_upper_bound: u64,
    sqrt: u64,
    giant_step_inverse: T,
    map: HashMap<T, u64>,
    mul: Mul,
    inv: Inv,
    id: Id,
}
impl<T, Mul, Inv, Id> Bsgs<T, Mul, Inv, Id>
where
    T: Copy + Hash + Eq,
    Mul: Fn(T, T) -> T,
    Inv: Fn(T) -> T,
    Id: Fn() -> T,
{
    /// 新しい BSGS ソルバーを構築します。
    ///
    /// # Parameters
    ///
    /// * `generator`: 生成子
    /// * `ord_upper_bound`: 生成子の位数の上界
    /// * `mul`, `inv`, `id`: 群の演算
    ///
    /// # 要件
    ///
    /// `(generator, mul, inv, id)` が巡回群の演算とその生成子
    ///
    ///
    /// # 計算量
    ///
    /// Θ ( √ ( `ord_upper_bound` ) ) 回の `mul` の呼び出しと、2 回の `id` の呼び出し
    ///
    ///
    /// # 計算しているもの
    ///
    /// * `sqrt`: `ord_upper_bound` の平方根
    /// * `map`: `generator` の `0..sqrt` 乗
    /// * `giant_step_inverse`: `generator` の `-sqrt` 乗
    ///
    pub fn new(generator: T, ord_upper_bound: u64, mul: Mul, inv: Inv, id: Id) -> Self {
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
            inv,
            id,
        }
    }
    /// `x` の離散対数が存在すれば返し、存在しなければ `None` を返します。
    ///
    /// # 計算量
    ///
    /// Θ ( √ ( `ord_upper_bound` ) ) 回の `mul` の呼び出し
    ///
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

impl<T: Debug, Mul, Inv, Id> Debug for Bsgs<T, Mul, Inv, Id> {
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
    use super::{binary, Bsgs};

    #[test]
    fn test_additive() {
        for n in 2..40 {
            let add = |x, y| (x + y) % n;
            let minus = |x| (n - x) % n;
            for g in 0..n {
                let ord = n / gcd(g, n);
                let bsgs = Bsgs::new(g, ord, add.clone(), minus, || 0);
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
            let pow = |x, y| binary(x, y, 1, mul.clone());
            let ord = totient(n);
            let inv = |x| pow(x, ord - 1);
            for g in (2..n)
                .filter(|&g| gcd(n, g) == 1 && (1..ord).all(|p| pow(g, p) != 1) && pow(g, ord) == 1)
            {
                let bsgs = Bsgs::new(g, ord, mul.clone(), inv, || 1);
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
