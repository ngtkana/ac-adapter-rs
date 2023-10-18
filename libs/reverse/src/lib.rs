//! std::cmp::Reverse です。
//!
//! Rust 1.17.0 がお好きな AOJ さんのために用意した特別ディナーです。
use std::cmp::Ordering;

#[derive(PartialEq, Eq, Debug, Copy, Clone, Default, Hash)]
pub struct Reverse<T>(pub T);

impl<T: PartialOrd> PartialOrd for Reverse<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { other.0.partial_cmp(&self.0) }

    #[inline]
    fn lt(&self, other: &Self) -> bool { other.0 < self.0 }

    #[inline]
    fn le(&self, other: &Self) -> bool { other.0 <= self.0 }

    #[inline]
    fn gt(&self, other: &Self) -> bool { other.0 > self.0 }

    #[inline]
    fn ge(&self, other: &Self) -> bool { other.0 >= self.0 }
}

impl<T: Ord> Ord for Reverse<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering { other.0.cmp(&self.0) }
}
