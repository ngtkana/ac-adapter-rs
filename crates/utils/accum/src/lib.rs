use std::{
    cmp::Ord,
    ops::{AddAssign, BitAndAssign, BitOrAssign, BitXorAssign, DivAssign, MulAssign, SubAssign},
};
pub fn add<T: Copy + AddAssign>(a: &mut [T]) {
    for_each(a, |&mut x, y| *y += x);
}
pub fn add_inv<T: Copy + SubAssign>(a: &mut [T]) {
    rfor_each(a, |&mut x, y| *y -= x);
}
pub fn mul<T: Copy + MulAssign>(a: &mut [T]) {
    for_each(a, |&mut x, y| *y *= x);
}
pub fn mul_inv<T: Copy + DivAssign>(a: &mut [T]) {
    rfor_each(a, |&mut x, y| *y /= x);
}
// -- ord
pub fn min<T: Copy + Ord>(a: &mut [T]) {
    for_each(a, |&mut x, y| *y = x.min(*y));
}
pub fn max<T: Copy + Ord>(a: &mut [T]) {
    for_each(a, |&mut x, y| *y = x.max(*y));
}
// --  bit
pub fn xor<T: Copy + BitXorAssign>(a: &mut [T]) {
    for_each(a, |&mut x, y| *y ^= x);
}
pub fn xor_inv<T: Copy + BitXorAssign>(a: &mut [T]) {
    rfor_each(a, |&mut x, y| *y ^= x);
}
pub fn or<T: Copy + BitOrAssign>(a: &mut [T]) {
    for_each(a, |&mut x, y| *y |= x);
}
pub fn and<T: Copy + BitAndAssign>(a: &mut [T]) {
    for_each(a, |&mut x, y| *y &= x);
}
pub fn for_each<T>(a: &mut [T], mut f: impl FnMut(&mut T, &mut T)) {
    if !a.is_empty() {
        for i in 1..a.len() {
            let (left, right) = a.split_at_mut(i);
            f(left.last_mut().unwrap(), right.first_mut().unwrap());
        }
    }
}
pub fn rfor_each<T>(a: &mut [T], mut f: impl FnMut(&mut T, &mut T)) {
    if !a.is_empty() {
        for i in (1..a.len()).rev() {
            let (left, right) = a.split_at_mut(i);
            f(left.last_mut().unwrap(), right.first_mut().unwrap());
        }
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn test() {
        let mut a = vec![0, 1, 2, 3];
        let mut b = Vec::new();
        super::for_each(&mut a, |&mut x, y| {
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
}
