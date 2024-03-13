//! `{lower,upper}_bound` and `partition_point`

use std::cmp::Ordering::Equal;
use std::cmp::Ordering::Greater;
use std::cmp::Ordering::Less;
use std::cmp::Ordering::{self};

/// Method versions of functions.
pub trait SliceMore<T> {
    fn partition_point<F: FnMut(&T) -> bool>(&self, pred: F) -> usize;
    fn lower_bound_by<F: FnMut(&T) -> Ordering>(&self, f: F) -> usize;
    fn upper_bound_by<F: FnMut(&T) -> Ordering>(&self, f: F) -> usize;
    fn lower_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, f: F) -> usize;
    fn upper_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, f: F) -> usize;
    fn lower_bound(&self, x: &T) -> usize
    where
        T: Ord;
    fn upper_bound(&self, x: &T) -> usize
    where
        T: Ord;
}
impl<T> SliceMore<T> for [T] {
    /// Method version of [`partition_point()`].
    fn partition_point<F: FnMut(&T) -> bool>(&self, pred: F) -> usize {
        partition_point(self, pred)
    }

    /// Method version of [`lower_bound_by()`].
    fn lower_bound_by<F: FnMut(&T) -> Ordering>(&self, f: F) -> usize {
        lower_bound_by(self, f)
    }

    /// Method version of [`upper_bound_by()`].
    fn upper_bound_by<F: FnMut(&T) -> Ordering>(&self, f: F) -> usize {
        upper_bound_by(self, f)
    }

    /// Method version of [`lower_bound_by_key()`].
    fn lower_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, f: F) -> usize {
        lower_bound_by_key(self, b, f)
    }

    /// Method version of [`upper_bound_by_key()`].
    fn upper_bound_by_key<B: Ord, F: FnMut(&T) -> B>(&self, b: &B, f: F) -> usize {
        upper_bound_by_key(self, b, f)
    }

    /// Method version of [`lower_bound()`].
    fn lower_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        lower_bound(self, x)
    }

    /// Method version of [`upper_bound()`].
    fn upper_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        upper_bound(self, x)
    }
}

/// Find $i$ s.t. $f ( a _ { i - 1 } ) \land \neg f ( a _ i )$.
///
/// Espacially, if $a$ is partitioned, it count the `true`'s from the head.
///
/// The same implementation as [in the standard library of Rust 1.52.0](https://doc.rust-lang.org/std/primitive.slice.html#method.partition_point).
///
/// # Examples
/// ```
/// # use slicemore::partition_point;
/// assert_eq!(partition_point(&[true, false], |&x| x), 1);
/// ```
pub fn partition_point<T, F: FnMut(&T) -> bool>(slice: &[T], mut pred: F) -> usize {
    slice
        .binary_search_by(|x| if pred(x) { Less } else { Greater })
        .unwrap_err()
}

/// Find $i$ s.t. $f ( a _ { i - 1 } ) \in \left \lbrace \mathtt{Less} \right \rbrace \land f ( a _ i ) \in \left \lbrace \mathtt { Equal }, \mathtt { Greater } \right \rbrace$.
///
/// # Examples
/// ```
/// # use slicemore::lower_bound_by;
/// # use std::cmp::Ordering::*;
/// assert_eq!(lower_bound_by(&[Less, Equal, Greater], |&x| x), 1);
/// ```
pub fn lower_bound_by<T, F: FnMut(&T) -> Ordering>(slice: &[T], mut f: F) -> usize {
    partition_point(slice, |x| matches!(f(x), Less))
}

/// Find $i$ s.t. $f ( a _ { i - 1 } ) \in \left \lbrace \mathtt{ Less }, \mathtt { Equal } \right \rbrace \land f ( a _ i ) \in \left \lbrace \mathtt { Greater } \right \rbrace$.
///
/// # Examples
/// ```
/// # use slicemore::upper_bound_by;
/// # use std::cmp::Ordering::*;
/// assert_eq!(upper_bound_by(&[Less, Equal, Greater], |&x| x), 2);
/// ```
pub fn upper_bound_by<T, F: FnMut(&T) -> Ordering>(slice: &[T], mut f: F) -> usize {
    partition_point(slice, |x| matches!(f(x), Less | Equal))
}

/// Find $i$ s.t. $f ( a _ { i - 1 } ) \lt b \le f ( a _ i )$.
///
/// # Examples
/// ```
/// # use slicemore::lower_bound_by_key;
/// # use std::cmp::Ordering::*;
/// assert_eq!(lower_bound_by_key(&[9, 10, 11, 12], &5, |&x| x / 2), 1);
/// ```
pub fn lower_bound_by_key<T, B: Ord, F: FnMut(&T) -> B>(slice: &[T], b: &B, mut f: F) -> usize {
    lower_bound_by(slice, |x| f(x).cmp(b))
}

/// Find $i$ s.t. $f ( a _ { i - 1 } ) \le b \lt f ( a _ i )$.
///
/// # Examples
/// ```
/// # use slicemore::upper_bound_by_key;
/// # use std::cmp::Ordering::*;
/// assert_eq!(upper_bound_by_key(&[9, 10, 11, 12], &5, |&x| x / 2), 3);
/// ```
pub fn upper_bound_by_key<T, B: Ord, F: FnMut(&T) -> B>(slice: &[T], b: &B, mut f: F) -> usize {
    upper_bound_by(slice, |x| f(x).cmp(b))
}

/// Find $i$ s.t. $a _ { i - 1 } \lt b \le a _ i$.
///
/// # Examples
/// ```
/// # use slicemore::lower_bound;
/// # use std::cmp::Ordering::*;
/// assert_eq!(lower_bound(&[10, 11, 12], &11), 1);
/// ```
pub fn lower_bound<T: Ord>(slice: &[T], x: &T) -> usize {
    lower_bound_by(slice, |p| p.cmp(x))
}

/// Find $i$ s.t. $a _ { i - 1 } \le b \lt a _ i$.
///
/// # Examples
/// ```
/// # use slicemore::upper_bound;
/// # use std::cmp::Ordering::*;
/// assert_eq!(upper_bound(&[10, 11, 12], &11), 2);
/// ```
pub fn upper_bound<T: Ord>(slice: &[T], x: &T) -> usize {
    upper_bound_by(slice, |p| p.cmp(x))
}
