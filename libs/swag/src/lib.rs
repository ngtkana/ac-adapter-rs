//! モノイドを載せた両端キュー（SWAG: Sliding Window Aggregation）。
//!
//! 前後 2 本のスタックと、それぞれの累積積を保持する。front 側の操作は前方累積積を、
//! back 側の操作は後方累積積を演算 1 回の呼び出しで更新するだけで済む。片側が空になったら
//! 残った要素を半分ずつ振り分けて両側の均衡を取り直すため、この再配分の償却込みで
//! push・pop が均し $O(1)$、全体の畳み込みは両側の累積積を 1 回演算するだけの $O(1)$ で行える。
//!
//! # 仕様
//!
//! [`Op`] トレイトで結合律を満たす演算 $x \cdot y$ を定義する。本体は [`DequeueSwag`]。
//!
//! - [`DequeueSwag::push_front`][] / [`DequeueSwag::push_back`][]: 要素を追加
//! - [`DequeueSwag::pop_front`][] / [`DequeueSwag::pop_back`][]: 要素を削除して返す（空なら `None`）
//! - [`DequeueSwag::fold`][]: 全要素の積を返す（空なら `None`）
//! - [`DequeueSwag::get`][] / `Index`: 前から $i$ 番目の要素を参照
//!
//! # 例
//!
//! ```
//! use swag::DequeueSwag;
//! use swag::Op;
//!
//! enum Add {}
//! impl Op for Add {
//!     type Value = i32;
//!     fn op(a: &i32, b: &i32) -> i32 {
//!         a + b
//!     }
//! }
//!
//! let mut swag = DequeueSwag::<Add>::copy_from_slice(&[2, 3, 4]);
//! swag.push_front(1);
//! assert_eq!(swag.collect_vec(), vec![1, 2, 3, 4]);
//! assert_eq!(swag.fold(), Some(10)); // 1 + 2 + 3 + 4
//! ```
//!
//! # 計算量
//!
//! - [`DequeueSwag::push_front`][] / [`DequeueSwag::push_back`][]: $O(1)$
//! - [`DequeueSwag::pop_front`][] / [`DequeueSwag::pop_back`][]: 均し $O(1)$
//! - [`DequeueSwag::fold`][]: $O(1)$

use std::iter::FromIterator;
use std::ops::Index;

/// 結合律を満たす二項演算 $x \cdot y$ を定義するトレイト。
pub trait Op {
    /// 演算対象の値の型。
    type Value;

    /// 演算 $a \cdot b$（結合律 $\mathrm{op}(\mathrm{op}(a, b), c) = \mathrm{op}(a, \mathrm{op}(b, c))$ を満たすこと）。
    fn op(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

/// モノイドを載せた両端キュー。前後 2 本のスタックと累積積を保持する。
pub struct DequeueSwag<O: Op> {
    front: Vec<O::Value>,
    back: Vec<O::Value>,
    front_sum: Vec<O::Value>,
    back_sum: Vec<O::Value>,
}
impl<O: Op> DequeueSwag<O> {
    /// 空の `DequeueSwag` を構築する。
    pub fn new() -> Self {
        Self {
            front: Vec::new(),
            back: Vec::new(),
            front_sum: Vec::new(),
            back_sum: Vec::new(),
        }
    }

    /// 前から $i$ 番目（0-indexed）の要素を返す。範囲外なら `None`。
    pub fn get(&self, i: usize) -> Option<&O::Value> {
        if i < self.front.len() {
            Some(&self.front[self.front.len() - i - 1])
        } else if i < self.front.len() + self.back.len() {
            Some(&self.back[i - self.front.len()])
        } else {
            None
        }
    }

    /// 要素数を返す。
    pub fn len(&self) -> usize {
        self.front.len() + self.back.len()
    }

    /// 要素数が $0$ かどうかを返す。
    pub fn is_empty(&self) -> bool {
        self.front.is_empty() && self.back.is_empty()
    }

    /// 先頭に要素を追加する。$O(1)$。
    ///
    /// # 例
    ///
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[2, 3, 4]);
    /// swag.push_front(1);
    /// assert_eq!(swag.collect_vec(), vec![1, 2, 3, 4]);
    /// ```
    pub fn push_front(&mut self, x: O::Value)
    where
        O::Value: Clone,
    {
        self.front_sum.push(if self.front_sum.is_empty() {
            x.clone()
        } else {
            O::op(&x, self.front_sum.last().unwrap())
        });
        self.front.push(x);
    }

    /// 末尾に要素を追加する。$O(1)$。
    ///
    /// # 例
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// swag.push_back(4);
    /// assert_eq!(swag.collect_vec(), vec![1, 2, 3, 4]);
    /// ```
    pub fn push_back(&mut self, x: O::Value)
    where
        O::Value: Clone,
    {
        self.back_sum.push(if self.back_sum.is_empty() {
            x.clone()
        } else {
            O::op(self.back_sum.last().unwrap(), &x)
        });
        self.back.push(x);
    }

    /// 先頭の要素を削除して返す。空なら `None`。均し $O(1)$。
    /// # 例
    /// ```
    /// use swag::DequeueSwag;
    /// # enum O {}
    /// # impl swag::Op for O {
    /// #    type Value = i32;
    /// #    fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    /// #        a + b
    /// #    }
    /// # }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// assert_eq!(swag.pop_front(), Some(1));
    /// assert_eq!(swag.collect_vec(), vec![2, 3]);
    /// ```
    pub fn pop_front(&mut self) -> Option<O::Value>
    where
        O::Value: Clone,
    {
        if self.front.is_empty() {
            let n = self.back.len();
            let mut swp = Self::new();
            for x in self.back.drain(..n.div_ceil(2)).rev() {
                swp.push_front(x);
            }
            for x in self.back.drain(..) {
                swp.push_back(x);
            }
            *self = swp;
        }
        let _ = self.front_sum.pop();
        self.front.pop()
    }

    /// 末尾の要素を削除して返す。空なら `None`。均し $O(1)$。
    /// # 例
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// assert_eq!(swag.pop_back(), Some(3));
    /// assert_eq!(swag.collect_vec(), vec![1, 2]);
    /// ```
    pub fn pop_back(&mut self) -> Option<O::Value>
    where
        O::Value: Clone,
    {
        if self.back.is_empty() {
            let n = self.front.len();
            let mut swp = Self::new();
            for x in self.front.drain(n.div_ceil(2)..) {
                swp.push_front(x);
            }
            for x in self.front.drain(..).rev() {
                swp.push_back(x);
            }
            *self = swp;
        }
        let _ = self.back_sum.pop();
        self.back.pop()
    }

    /// 全要素の積 $x_0 \cdot x_1 \cdots x_{n-1}$ を返す。空なら `None`。$O(1)$。
    /// # 例
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// assert_eq!(swag.fold(), Some(6));
    /// ```
    pub fn fold(&self) -> Option<O::Value>
    where
        O::Value: Clone,
    {
        match (self.front_sum.last(), self.back_sum.last()) {
            (None, None) => None,
            (Some(x), None) | (None, Some(x)) => Some(x.clone()),
            (Some(x), Some(y)) => Some(O::op(x, y)),
        }
    }

    /// 前から順に要素を走査するイテレータを返す。
    pub fn iter(&self) -> impl Iterator<Item = &O::Value> {
        self.front.iter().rev().chain(self.back.iter())
    }

    /// 前から順に要素を集めた `Vec` を返す。
    pub fn collect_vec(&self) -> Vec<O::Value>
    where
        O::Value: Clone,
    {
        self.iter().cloned().collect()
    }

    /// 前後 2 本のスタックをスライスのまま返す。
    ///
    /// 前側は逆順（先頭要素が末尾に来る）で格納されている。全要素を先頭から順に並べるには
    /// `front.iter().rev().chain(back)` とする必要がある。
    pub fn as_two_slices(&self) -> (&[O::Value], &[O::Value]) {
        (&self.front, &self.back)
    }

    /// スライスの要素を複製して `DequeueSwag` を構築する。
    pub fn clone_from_slice(slice: &[O::Value]) -> Self
    where
        O::Value: Clone,
    {
        let mut reslt = Self::new();
        for x in slice {
            reslt.push_back(x.clone());
        }
        reslt
    }

    /// スライスの要素をコピーして `DequeueSwag` を構築する。
    pub fn copy_from_slice(slice: &[O::Value]) -> Self
    where
        O::Value: Copy,
    {
        let mut reslt = Self::new();
        for x in slice {
            reslt.push_back(*x);
        }
        reslt
    }
}

impl<O: Op> Default for DequeueSwag<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Op> Index<usize> for DequeueSwag<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.front.len() {
            &self.front[self.front.len() - index - 1]
        } else {
            &self.back[index - self.front.len()]
        }
    }
}

impl<O: Op> std::fmt::Debug for DequeueSwag<O>
where
    O::Value: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DequeueSwag")
            .field("front", &self.front)
            .field("back", &self.back)
            .field("front_sum", &self.front_sum)
            .field("back_sum", &self.back_sum)
            .finish()
    }
}

impl<O: Op> From<Vec<O::Value>> for DequeueSwag<O>
where
    O::Value: Clone,
{
    fn from(mut values: Vec<O::Value>) -> Self {
        let mut reslt = Self::new();
        let n = values.len();
        for x in values.drain(n / 2..) {
            reslt.push_back(x);
        }
        for x in values.into_iter().rev() {
            reslt.push_front(x);
        }
        reslt
    }
}

impl<O: Op> IntoIterator for DequeueSwag<O> {
    type IntoIter = std::iter::Chain<
        std::iter::Rev<std::vec::IntoIter<O::Value>>,
        std::vec::IntoIter<O::Value>,
    >;
    type Item = O::Value;

    fn into_iter(self) -> Self::IntoIter {
        self.front.into_iter().rev().chain(self.back)
    }
}

impl<'a, O: Op> IntoIterator for &'a DequeueSwag<O> {
    type IntoIter = std::iter::Chain<
        std::iter::Rev<std::slice::Iter<'a, O::Value>>,
        std::slice::Iter<'a, O::Value>,
    >;
    type Item = &'a O::Value;

    fn into_iter(self) -> Self::IntoIter {
        self.front.iter().rev().chain(self.back.iter())
    }
}

impl<O: Op> FromIterator<O::Value> for DequeueSwag<O>
where
    O::Value: Clone,
{
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        iter.into_iter().collect::<Vec<_>>().into()
    }
}

impl<O: Op> Extend<O::Value> for DequeueSwag<O>
where
    O::Value: Clone,
{
    fn extend<T: IntoIterator<Item = O::Value>>(&mut self, iter: T) {
        for x in iter {
            self.push_back(x);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::VecDeque;
    use std::fmt::Debug;
    use std::ops::Add;
    use std::ops::Mul;

    const P: u64 = 998_244_353;

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    struct Fp(u64);
    impl Debug for Fp {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }
    impl Add for Fp {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output {
            Fp((self.0 + rhs.0) % P)
        }
    }

    impl Mul for Fp {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            Fp(self.0 * rhs.0 % P)
        }
    }

    enum Affine {}
    impl Op for Affine {
        type Value = (Fp, Fp);

        fn op(&(a, b): &Self::Value, &(c, d): &Self::Value) -> Self::Value {
            (a * c, d + c * b)
        }
    }

    #[test]
    fn test_swag() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let q = 10;
            let mut swag = DequeueSwag::<Affine>::new();
            let mut deque = VecDeque::new();
            for _ in 0..q {
                match rng.gen_range(0..4) {
                    0 => {
                        let a = Fp(rng.gen_range(0..4));
                        let b = Fp(rng.gen_range(0..4));
                        eprintln!("push_front {:?}", (a, b));
                        swag.push_front((a, b));
                        deque.push_front((a, b));
                    }
                    1 => {
                        let a = Fp(rng.gen_range(0..4));
                        let b = Fp(rng.gen_range(0..4));
                        eprintln!("push_back {:?}", (a, b));
                        swag.push_back((a, b));
                        deque.push_back((a, b));
                    }
                    2 => {
                        eprintln!("pop_front");
                        assert_eq!(swag.pop_front(), deque.pop_front());
                    }
                    3 => {
                        eprintln!("pop_back");
                        assert_eq!(swag.pop_back(), deque.pop_back());
                    }
                    _ => unreachable!(),
                }
                eprintln!("{deque:?}");
                eprintln!("{swag:?}");
                let result = swag.fold().unwrap_or((Fp(1), Fp(0)));
                let expected = deque
                    .iter()
                    .fold((Fp(1), Fp(0)), |acc, x| Affine::op(&acc, x));
                assert_eq!(result, expected);
                let result = swag.collect_vec();
                let expected = deque.iter().copied().collect::<Vec<_>>();
                assert_eq!(result, expected);
                eprintln!("---");
            }
        }
    }
}
