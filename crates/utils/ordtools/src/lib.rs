//! [`change_min`], [`change_max`] を提供します。
//!
//! # Note
//!
//! 等しいときには代入が行われません。
//!
//! ```
//! use std::cmp::{PartialOrd, Ordering};
//! use ordtools::Ordtools;
//!
//! #[derive(Eq, Debug, Clone)]
//! struct Person {
//!     id: u32,
//!     name: String,
//!     height: u32,
//! }
//!
//! impl PartialOrd for Person {
//!     fn partial_cmp(&self, other: &Person) -> Option<Ordering> {
//!         Some(self.cmp(other))
//!     }
//! }
//!
//! impl Ord for Person {
//!     fn cmp(&self, other: &Person) -> Ordering {
//!         self.height.cmp(&other.height)
//!     }
//! }
//!
//! impl PartialEq for Person {
//!     fn eq(&self, other: &Person) -> bool {
//!         self.height == other.height
//!     }
//! }
//!
//! let kana = Person {
//!     id: 3,
//!     name: "kana".to_string(),
//!     height: 195,
//! };
//! let hiroshi = Person {
//!     id: 4,
//!     name: "hiroshi".to_string(),
//!     height: 115,
//! };
//!
//! let mut person = kana.clone();
//! assert_eq!(&person, &kana);
//! assert_ne!(&person, &hiroshi);
//! person.change_min(hiroshi.clone());
//! assert_ne!(&person, &kana);
//! assert_eq!(&person, &hiroshi);
//! ```
//!
//! [`change_min`]: trait.Ordtools.html#method.change_min
//! [`change_max`]: trait.Ordtools.html#method.change_max

/// [`change_min`], [`change_max`] を提供します。
///
/// [`change_min`]: trait.Ordtools.html#method.change_min
/// [`change_max`]: trait.Ordtools.html#method.change_max
pub trait Ordtools: PartialOrd + Sized {
    /// `rhs` が `self` よりも小さいときに、`self` を `rhs` で置き換えます。
    /// 等しい場合は代入は行いません。
    ///
    /// # Examples
    ///
    /// ```
    /// use ordtools::Ordtools;
    /// let mut x: i32 = 3;
    /// x.change_min(4);
    /// assert_eq!(x, 3);
    /// x.change_min(2);
    /// assert_eq!(x, 2);
    /// ```
    ///
    fn change_min(&mut self, mut rhs: Self) {
        if self > &mut rhs {
            *self = rhs;
        }
    }

    /// `rhs` が `self` よりも大きいときに、`self` を `rhs` で置き換えます。
    /// 等しい場合は代入は行いません。
    ///
    /// # Examples
    ///
    /// ```
    /// use ordtools::Ordtools;
    /// let mut x: i32 = 3;
    /// x.change_max(2);
    /// assert_eq!(x, 3);
    /// x.change_max(4);
    /// assert_eq!(x, 4);
    /// ```
    ///
    fn change_max(&mut self, mut rhs: Self) {
        if self < &mut rhs {
            *self = rhs;
        }
    }
}

impl<T: PartialOrd + Sized> Ordtools for T {}
