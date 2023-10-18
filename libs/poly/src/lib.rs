//! [`std::ops`] を利用した多項式のナイーブな計算
//!
//! # あるもの
//!
//!
//! | お名前    | 計算量                | やること  |
//! | -         | -                     | -         |
//! | [`poly_add`]   | Θ ( max ( l, m ) )   | 足し算    |
//! | [`poly_sub`]   | Θ ( max ( l, m ) )   | 引き算    |
//! | [`poly_mul`]   | Θ ( l + m )          | 掛け算    |

use std::fmt::Debug;
use std::iter::repeat_with;
use std::iter::Fuse;
use std::marker::PhantomData;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Sub;

/// 自由関数 [`poly_add`], [`poly_sub`] を呼び出します。
///
/// # Examples
///
/// ```
/// use poly::Poly;
///
/// // 成分ごとの和を計算します。
/// let a = vec![1, 2];
/// let b = vec![10];
/// let c = a.into_iter().poly_add(b).collect::<Vec<_>>();
/// assert_eq!(c, vec![11, 2]);
///
/// let a = vec![1, 2];
/// let b = vec![10];
/// let c = a.into_iter().poly_sub(b).collect::<Vec<_>>();
/// assert_eq!(c, vec![-9, 2]);
/// ```
pub trait Poly: Iterator + Sized {
    fn poly_add<B: Iterator>(
        self,
        b: impl IntoIterator<Item = Self::Item, IntoIter = B>,
    ) -> PolyAdd<Self::Item, Self, B>
    where
        Self::Item: Add<Output = Self::Item>,
        B: Iterator<Item = Self::Item>,
    {
        poly_add(self, b)
    }
    fn poly_sub<B: Iterator>(
        self,
        b: impl IntoIterator<Item = Self::Item, IntoIter = B>,
    ) -> PolySub<Self::Item, Self, B>
    where
        Self::Item: Sub<Output = Self::Item> + Neg<Output = Self::Item>,
        B: Iterator<Item = Self::Item>,
    {
        poly_sub(self, b)
    }
}
impl<T: Iterator + Sized> Poly for T {}

/// 足し算
///
/// 成分ごとの和（[`Add::add`]
/// の結果を）を計算します。長さが異なる場合は、片方が都議らたあとはもう一方の要素要素をそのまま返します。
///
/// # Examples
///
/// ```
/// # use poly::poly_add;
/// // 成分ごとの和を計算します。
/// let a = vec![1, 2];
/// let b = vec![10];
/// let c = poly_add(a, b).collect::<Vec<_>>();
/// assert_eq!(c, vec![11, 2]);
/// ```
pub fn poly_add<T, A, B>(
    a: impl IntoIterator<Item = T, IntoIter = A>,
    b: impl IntoIterator<Item = T, IntoIter = B>,
) -> PolyAdd<T, A, B>
where
    T: Add<Output = T>,
    A: Iterator<Item = T>,
    B: Iterator<Item = T>,
{
    PolyAdd {
        a: a.into_iter().fuse(),
        b: b.into_iter().fuse(),
        __marker: PhantomData,
    }
}
/// [`poly_add` の戻り値型ですので、そちらのドキュメントをご覧ください。](poly_add)
pub struct PolyAdd<T, A, B> {
    a: Fuse<A>,
    b: Fuse<B>,
    __marker: PhantomData<T>,
}
impl<T, A, B> Iterator for PolyAdd<T, A, B>
where
    T: Add<Output = T>,
    A: Iterator<Item = T>,
    B: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.next(), self.b.next()) {
            (None, None) => None,
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (Some(a), Some(b)) => Some(a + b),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (a_lower, a_upper) = self.a.size_hint();
        let (b_lower, b_upper) = self.b.size_hint();
        let lower = std::cmp::max(a_lower, b_lower);
        let upper = match (a_upper, b_upper) {
            (Some(x), Some(y)) => Some(std::cmp::max(x, y)),
            _ => None,
        };
        (lower, upper)
    }
}

/// 引き算
///
/// 成分ごとの差（[`Sub::sub`]
/// の結果を）を計算します。長さが異なる場合の仕様は [`poly_sub`] に似ていますが、`a`
/// が余ればそのまま、`b` が余ればその negation（[`Neg::neg`] の結果）を返します。
///
/// # Examples
///
/// ```
/// # use poly::poly_sub;
/// // 成分ごとの差を計算します。
/// let a = vec![1, 2];
/// let b = vec![10];
/// let c = poly_sub(a, b).collect::<Vec<_>>();
/// assert_eq!(c, vec![-9, 2]);
/// ```
pub fn poly_sub<T, A, B>(
    a: impl IntoIterator<Item = T, IntoIter = A>,
    b: impl IntoIterator<Item = T, IntoIter = B>,
) -> PolySub<T, A, B>
where
    T: Sub,
    A: Iterator<Item = T>,
    B: Iterator<Item = T>,
{
    PolySub {
        a: a.into_iter().fuse(),
        b: b.into_iter().fuse(),
        __marker: PhantomData,
    }
}
/// [`poly_sub` の戻り値型ですので、そちらのドキュメントをご覧ください。](poly_sub)
pub struct PolySub<T, A, B> {
    a: Fuse<A>,
    b: Fuse<B>,
    __marker: PhantomData<T>,
}
impl<T, A, B> Iterator for PolySub<T, A, B>
where
    T: Sub<Output = T> + Neg<Output = T>,
    A: Iterator<Item = T>,
    B: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.next(), self.b.next()) {
            (None, None) => None,
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(-b),
            (Some(a), Some(b)) => Some(a - b),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (a_lower, a_upper) = self.a.size_hint();
        let (b_lower, b_upper) = self.b.size_hint();
        let lower = std::cmp::max(a_lower, b_lower);
        let upper = match (a_upper, b_upper) {
            (Some(x), Some(y)) => Some(std::cmp::max(x, y)),
            _ => None,
        };
        (lower, upper)
    }
}

/// 掛け算
///
/// 多項式としての積を計算します。長さは、`a` と `b` のいずれかが殻ならば空、さもなくば `a.len() +
/// b.len() - 1` となります。
///
/// # Examples
///
/// ```
/// # use poly::poly_mul;
/// // 多項式の積を計算します。
/// let a = vec![1, 2];
/// let b = vec![10, 20];
/// let c = poly_mul(&a, &b, || 0);
/// assert_eq!(c, vec![10, 40, 40]);
/// ```
pub fn poly_mul<T: AddAssign + Mul<Output = T> + Debug + Copy>(
    a: &[T],
    b: &[T],
    zero: impl Fn() -> T,
) -> Vec<T> {
    if a.is_empty() || b.is_empty() {
        Vec::new()
    } else {
        let mut c = repeat_with(zero)
            .take(a.len() + b.len() - 1)
            .collect::<Vec<_>>();
        a.iter()
            .enumerate()
            .for_each(|(i, &x)| c[i..].iter_mut().zip(b).for_each(|(z, &y)| *z += x * y));
        c
    }
}

#[cfg(test)]
mod tests {
    use super::poly_add;
    use super::poly_mul;
    use super::poly_sub;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter::repeat_with;

    #[test]
    fn test_add() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let l = rng.gen_range(1..10);
            let m = rng.gen_range(1..10);
            let a = repeat_with(|| rng.gen_range(-10..=10))
                .take(l)
                .collect::<Vec<_>>();
            let b = repeat_with(|| rng.gen_range(-10..=10))
                .take(m)
                .collect::<Vec<_>>();
            let mut c = vec![0; a.len().max(b.len())];
            c.iter_mut().zip(&a).for_each(|(z, &x)| *z += x);
            c.iter_mut().zip(&b).for_each(|(z, &y)| *z += y);
            let expected = c;
            let result = poly_add(a, b).collect::<Vec<_>>();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_sub() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let l = rng.gen_range(1..10);
            let m = rng.gen_range(1..10);
            let a = repeat_with(|| rng.gen_range(-10..=10))
                .take(l)
                .collect::<Vec<_>>();
            let b = repeat_with(|| rng.gen_range(-10..=10))
                .take(m)
                .collect::<Vec<_>>();
            let mut c = vec![0; a.len().max(b.len())];
            c.iter_mut().zip(&a).for_each(|(z, &x)| *z += x);
            c.iter_mut().zip(&b).for_each(|(z, &y)| *z -= y);
            let expected = c;
            let result = poly_sub(a, b).collect::<Vec<_>>();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_mul() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let l = rng.gen_range(1..10);
            let m = rng.gen_range(1..10);
            let a = repeat_with(|| rng.gen_range(-10..=10))
                .take(l)
                .collect::<Vec<_>>();
            let b = repeat_with(|| rng.gen_range(-10..=10))
                .take(m)
                .collect::<Vec<_>>();
            let mut c = vec![0; a.len() + b.len() - 1];
            for i in 0..l {
                for j in 0..m {
                    c[i + j] += a[i] * b[j];
                }
            }
            let expected = c;
            let result = poly_mul(&a, &b, || 0);
            assert_eq!(result, expected);
        }
    }
}
