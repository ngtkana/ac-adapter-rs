//! Utility `change_{min,max}`.

/// If `lhs` is larger than `rhs`, override `lhs` by `rhs`.
///
/// # Examples
///
/// ```
/// # use cmpmore::change_min;
/// let mut x: i32 = 3;
/// change_min(&mut x, 2);
/// assert_eq!(x, 2);
/// ```
pub fn change_min<T: PartialOrd>(lhs: &mut T, rhs: T) {
    if *lhs > rhs {
        *lhs = rhs;
    }
}

/// If `lhs` is smaller than `rhs`, override `lhs` by `rhs`.
///
/// # Examples
///
/// ```
/// # use cmpmore::change_max;
/// let mut x: i32 = 3;
/// change_max(&mut x, 4);
/// assert_eq!(x, 4);
/// ```
pub fn change_max<T: PartialOrd>(lhs: &mut T, rhs: T) {
    if *lhs < rhs {
        *lhs = rhs;
    }
}

/// Macro version of [`change_min()`]. This is useful to avoid borrow checkers.
///
/// # Examples
///
/// ```
/// # use cmpmore::change_min;
/// let mut a = [3, 2];
/// change_min!(&mut a[0], a[1]);
/// assert_eq!(a, [2, 2]);
/// ```
#[macro_export]
macro_rules! change_min {
    ($lhs:expr, $rhs:expr) => {
        let rhs = $rhs;
        let lhs = $lhs;
        $crate::change_min(lhs, rhs);
    };
}

/// Macro version of [`change_max()`]. This is useful to avoid borrow checkers.
///
/// # Examples
///
/// ```
/// # use cmpmore::change_max;
/// let mut a = [3, 4];
/// change_max!(&mut a[0], a[1]);
/// assert_eq!(a, [4, 4]);
/// ```
#[macro_export]
macro_rules! change_max {
    ($lhs:expr, $rhs:expr) => {
        let rhs = $rhs;
        let lhs = $lhs;
        $crate::change_max(lhs, rhs);
    };
}

/// Provide method versions of [`change_min()`], [`change_max()`]
pub trait CmpMore: PartialOrd + Sized {
    /// If `self` is larger than `rhs`, override `self` by `rhs`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cmpmore::CmpMore;
    /// let mut x: i32 = 3;
    /// x.change_min(2);
    /// assert_eq!(x, 2);
    /// ```
    fn change_min(&mut self, rhs: Self) {
        change_min(self, rhs)
    }

    /// If `self` is smaller than `rhs`, override `self` by `rhs`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cmpmore::CmpMore;
    /// let mut x: i32 = 3;
    /// x.change_max(4);
    /// assert_eq!(x, 4);
    /// ```
    fn change_max(&mut self, rhs: Self) {
        change_max(self, rhs)
    }
}

impl<T: PartialOrd + Sized> CmpMore for T {}
