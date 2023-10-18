use std::cmp::Ord;
use std::ops::AddAssign;
use std::ops::BitAndAssign;
use std::ops::BitOrAssign;
use std::ops::BitXorAssign;
use std::ops::DivAssign;
use std::ops::MulAssign;
use std::ops::SubAssign;
pub fn add<T: Copy + AddAssign>(a: &mut [T]) { for_each_mut(a, |&mut x, y| *y += x); }
pub fn add_inv<T: Copy + SubAssign>(a: &mut [T]) { rfor_each_mut(a, |&mut x, y| *y -= x); }
pub fn mul<T: Copy + MulAssign>(a: &mut [T]) { for_each_mut(a, |&mut x, y| *y *= x); }
pub fn mul_inv<T: Copy + DivAssign>(a: &mut [T]) { rfor_each_mut(a, |&mut x, y| *y /= x); }
// -- ord
pub fn min<T: Copy + Ord>(a: &mut [T]) { for_each_mut(a, |&mut x, y| *y = x.min(*y)); }
pub fn max<T: Copy + Ord>(a: &mut [T]) { for_each_mut(a, |&mut x, y| *y = x.max(*y)); }
pub fn skipped_min<T: Copy + Ord>(a: &[T], max: T) -> Vec<T> {
    skipped(a, |x, y| (*x).min(*y), || max).collect()
}
pub fn skipped_max<T: Copy + Ord>(a: &[T], min: T) -> Vec<T> {
    skipped(a, |x, y| (*x).max(*y), || min).collect()
}
// --  bit
pub fn xor<T: Copy + BitXorAssign>(a: &mut [T]) { for_each_mut(a, |&mut x, y| *y ^= x); }
pub fn xor_inv<T: Copy + BitXorAssign>(a: &mut [T]) { rfor_each_mut(a, |&mut x, y| *y ^= x); }
pub fn or<T: Copy + BitOrAssign>(a: &mut [T]) { for_each_mut(a, |&mut x, y| *y |= x); }
pub fn and<T: Copy + BitAndAssign>(a: &mut [T]) { for_each_mut(a, |&mut x, y| *y &= x); }
// -- for_each
pub fn for_each<T>(a: &[T], mut f: impl FnMut(&T, &T)) {
    if !a.is_empty() {
        for i in 1..a.len() {
            let (left, right) = a.split_at(i);
            f(left.last().unwrap(), right.first().unwrap());
        }
    }
}
pub fn rfor_each<T>(a: &[T], mut f: impl FnMut(&T, &T)) {
    if !a.is_empty() {
        for i in (1..a.len()).rev() {
            let (left, right) = a.split_at(i);
            f(left.last().unwrap(), right.first().unwrap());
        }
    }
}
pub fn for_each_mut<T>(a: &mut [T], mut f: impl FnMut(&mut T, &mut T)) {
    if !a.is_empty() {
        for i in 1..a.len() {
            let (left, right) = a.split_at_mut(i);
            f(left.last_mut().unwrap(), right.first_mut().unwrap());
        }
    }
}
pub fn rfor_each_mut<T>(a: &mut [T], mut f: impl FnMut(&mut T, &mut T)) {
    if !a.is_empty() {
        for i in (1..a.len()).rev() {
            let (left, right) = a.split_at_mut(i);
            f(left.last_mut().unwrap(), right.first_mut().unwrap());
        }
    }
}

pub fn skipped<T, F, I>(a: &[T], f: F, identity: I) -> Skipped<T, F, I>
where
    F: FnMut(&T, &T) -> T,
    I: FnMut() -> T,
{
    Skipped::new(a, f, identity)
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct Skipped<'a, T, F, I> {
    a: &'a [T],
    left: T,
    right: Vec<T>,
    f: F,
    identity: I,
}
impl<'a, T, F, I> Skipped<'a, T, F, I>
where
    F: FnMut(&T, &T) -> T,
    I: FnMut() -> T,
{
    fn new(a: &'a [T], mut f: F, mut identity: I) -> Self {
        let right = if a.is_empty() {
            Vec::new()
        } else {
            let mut right = vec![identity()];
            for x in a[1..].iter().rev() {
                let x = f(x, right.last().unwrap());
                right.push(x);
            }
            right
        };
        Self {
            a,
            left: identity(),
            right,
            f,
            identity,
        }
    }
}
impl<'a, T, F, I> Iterator for Skipped<'a, T, F, I>
where
    F: FnMut(&T, &T) -> T,
    I: FnMut() -> T,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(right) = self.right.pop() {
            let res = (self.f)(&self.left, &right);
            self.left = (self.f)(&self.left, &self.a[0]);
            self.a = &self.a[1..];
            Some(res)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::skipped;
    use super::skipped_max;
    use super::skipped_min;

    #[test]
    fn test_for_each() {
        let a = vec![0, 1, 2, 3];
        let mut b = Vec::new();
        super::for_each(&a, |&x, &y| {
            b.push((x, y));
        });
        let b_expected = vec![(0, 1), (1, 2), (2, 3)];
        assert_eq!(&b, &b_expected);
    }
    #[test]
    fn test_for_each_mut() {
        let mut a = vec![0, 1, 2, 3];
        let mut b = Vec::new();
        super::for_each_mut(&mut a, |&mut x, y| {
            *y += x;
            b.push((x, *y));
        });
        let a_expected = vec![0, 1, 3, 6];
        let b_expected = vec![(0, 1), (1, 3), (3, 6)];
        assert_eq!(&a, &a_expected);
        assert_eq!(&b, &b_expected);
    }

    #[test]
    fn test_add() {
        let mut a = vec![4, 6, 7, 3, 7];
        let orig_a = a.clone();
        super::add(&mut a);
        assert_eq!(&a, &[4, 10, 17, 20, 27]);

        super::add_inv(&mut a);
        assert_eq!(&a, &orig_a);
    }
    #[test]
    fn test_mul() {
        let mut a = vec![4, 6, 7, 3, 7];
        let orig_a = a.clone();
        super::mul(&mut a);
        assert_eq!(&a, &[4, 24, 7 * 24, 21 * 24, 147 * 24]);

        super::mul_inv(&mut a);
        assert_eq!(&a, &orig_a);
    }
    #[test]
    fn test_xor() {
        let mut a = vec![4, 6, 7, 3, 7];
        let orig_a = a.clone();
        super::xor(&mut a);
        assert_eq!(&a, &[4, 2, 5, 6, 1]);

        super::xor_inv(&mut a);
        assert_eq!(&a, &orig_a);
    }
    #[test]
    fn test_min() {
        let mut a = vec![4, 6, 7, 3, 7];
        super::min(&mut a);
        assert_eq!(&a, &[4, 4, 4, 3, 3]);
    }
    #[test]
    fn test_max() {
        let mut a = vec![4, 6, 7, 3, 7];
        super::max(&mut a);
        assert_eq!(&a, &[4, 6, 7, 7, 7]);
    }
    #[test]
    fn test_skipped() {
        let a = (0..4)
            .map(|i| ((b'a' + i) as char).to_string())
            .collect::<Vec<_>>();
        let skipped = skipped(
            &a,
            |s, t| s.chars().chain(t.chars()).collect::<String>(),
            String::new,
        )
        .collect::<Vec<_>>();
        assert_eq!(skipped[0].as_str(), "bcd");
        assert_eq!(skipped[1].as_str(), "acd");
        assert_eq!(skipped[2].as_str(), "abd");
        assert_eq!(skipped[3].as_str(), "abc");
    }
    #[test]
    fn test_skipped_min() {
        let a = vec![4, 2, 6, 1];
        let skipped = skipped_min(&a, std::i32::MAX);
        assert_eq!(skipped, vec![1, 1, 1, 2]);
    }
    #[test]
    fn test_skipped_max() {
        let a = vec![4, 2, 6, 1];
        let skipped = skipped_max(&a, std::i32::MIN);
        assert_eq!(skipped, vec![6, 6, 4, 6]);
    }
}
