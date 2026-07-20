//! A Fenwick tree (Binary Indexed Tree) for efficient range queries.
//!
//! This crate provides a generic implementation of Fenwick trees,
//! which support point updates and prefix/range queries in O(log n) time.
//!
//! # When to use
//!
//! A Fenwick tree is useful when you need to:
//! - Quickly update individual elements
//! - Query aggregate values over ranges (sum, XOR, min, etc.)
//! - Process online queries where the dataset changes dynamically
//!
//! It's particularly common in competitive programming for range sum queries.
//!
//! # Examples
//!
//! ```
//! use fenwick::{Fenwick, Op, OpSub};
//!
//! struct Sum;
//! impl Op for Sum {
//!     type Value = i64;
//!     fn identity() -> i64 { 0 }
//!     fn add(a: &i64, b: &i64) -> i64 { a + b }
//! }
//! impl OpSub for Sum {
//!     fn sub(a: &i64, b: &i64) -> i64 { a - b }
//! }
//!
//! let mut tree = Fenwick::<Sum>::new(5);
//! tree.add(1, &10);
//! tree.add(3, &20);
//!
//! // Sum of elements in [1, 4)
//! assert_eq!(tree.fold(1..4), 30);
//! ```
//!
//! # How it works
//!
//! This crate uses a generic [`Op`] trait to define the aggregation operation.
//! Your type must implement:
//! - An identity element (via [`Op::identity`])
//! - An associative binary operation (via [`Op::add`])
//!
//! For range queries over arbitrary intervals, additionally implement [`OpSub`]
//! to support subtraction. This enables the formula:
//! `range_sum(start..end) = prefix_sum(end) - prefix_sum(start)`.
//!
//! # Core Items
//!
//! - [`Fenwick<O>`]: The main data structure for efficient range queries
//! - [`Op`]: Trait defining associative operations (identity + add)
//! - [`OpSub`]: Extension of [`Op`] that also supports subtraction
//!
//! # Complexity
//!
//! - `new(n)`: O(n)
//! - `add()`, `sub()`: O(log n)
//! - `fold_to()`, `fold()`: O(log n)

use std::{
    fmt::Debug,
    marker::PhantomData,
    ops::{Range, RangeTo},
};

/// A trait for defining associative operations on values.
///
/// This trait encapsulates the core operations needed for a Fenwick tree
/// to perform efficient range queries and updates. Implementations must
/// provide an identity element and an associative binary operation.
///
/// # Safety and Correctness
///
/// For the Fenwick tree to work correctly, `add` must be associative:
/// for all values `a`, `b`, `c`, the operation must satisfy associativity.
///
/// # Examples
///
/// ```
/// # use fenwick::Op;
/// struct AddOp;
/// impl Op for AddOp {
///     type Value = i64;
///     fn identity() -> Self::Value { 0 }
///     fn add(a: &Self::Value, b: &Self::Value) -> Self::Value {
///         a + b
///     }
/// }
/// ```
pub trait Op {
    /// The type of values this operation works with.
    type Value;

    /// Returns the identity element for this operation.
    ///
    /// This is the element that, when combined with any value `v` via
    /// `add`, leaves `v` unchanged.
    fn identity() -> Self::Value;

    /// Computes the result of the associative operation: `a ⊕ b`.
    fn add(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

/// An extension of [`Op`] that also supports subtraction.
///
/// This trait is needed to compute range queries over an arbitrary range
/// `[start, end)`. With only addition, you can only compute prefix sums.
/// With subtraction, you can compute range sums via the formula:
/// `range_sum(start..end) = prefix_sum(end) - prefix_sum(start)`.
///
/// # Examples
///
/// ```
/// # use fenwick::OpSub;
/// struct AddOp;
/// impl OpSub for AddOp {
///     fn sub(a: &i64, b: &i64) -> i64 {
///         a - b
///     }
/// }
/// # impl fenwick::Op for AddOp {
/// #     type Value = i64;
/// #     fn identity() -> i64 { 0 }
/// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
/// # }
/// ```
pub trait OpSub: Op {
    /// Computes the result of the inverse operation: `a ⊖ b`.
    fn sub(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

/// A Fenwick tree (also known as a Binary Indexed Tree).
///
/// A Fenwick tree is a data structure that efficiently supports:
/// - **Point updates**: Update a single element in O(log n) time
/// - **Prefix queries**: Compute the fold of elements in [0, i) in O(log n) time
/// - **Range queries**: (with [`OpSub`]) Compute the fold of elements in [i, j) in O(log n) time
///
/// The tree uses a generic operation [`Op`] to define the aggregation function.
///
/// # Memory
///
/// A `Fenwick<O>` uses O(n) space where n is the length of the tree.
///
/// # Examples
///
/// Creating and updating a tree with addition:
///
/// ```
/// # use fenwick::{Fenwick, Op};
/// struct AddOp;
/// impl Op for AddOp {
///     type Value = i64;
///     fn identity() -> i64 { 0 }
///     fn add(a: &i64, b: &i64) -> i64 { a + b }
/// }
///
/// let mut tree = Fenwick::<AddOp>::new(5);
/// tree.add(2, &10);  // Add 10 at index 2
/// tree.add(4, &5);   // Add 5 at index 4
/// let sum = tree.fold_to(..5);  // Sum of [0, 5)
/// assert_eq!(sum, 15);
/// ```
pub struct Fenwick<O: Op> {
    items: Vec<O::Value>,
    __maker: PhantomData<O>,
}
impl<T: Debug, O: Op<Value = T>> Debug for Fenwick<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(
                (1usize..self.items.len()).map(|i| (i - (i & i.wrapping_neg())..i, &self.items[i])),
            )
            .finish()
    }
}

impl<O: Op> Default for Fenwick<O> {
    /// Creates a new empty Fenwick tree.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fenwick::Fenwick;
    /// # struct AddOp;
    /// # impl fenwick::Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let tree: Fenwick<AddOp> = Default::default();
    /// ```
    fn default() -> Self {
        Self {
            items: vec![],
            __maker: PhantomData,
        }
    }
}
impl<T, O: Op<Value = T>> Fenwick<O> {
    /// Creates a new Fenwick tree with the given length.
    ///
    /// All elements are initialized to the identity element of the operation.
    ///
    /// # Arguments
    ///
    /// * `len` - The number of logical elements in the tree
    ///
    /// # Examples
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let tree = Fenwick::<AddOp>::new(10);
    /// ```
    pub fn new(len: usize) -> Self
    where
        T: Clone,
    {
        Self {
            items: vec![O::identity(); len + 1],
            __maker: PhantomData,
        }
    }

    /// Adds a value to the element at the given index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index to update (must be < length)
    /// * `value` - The value to add
    ///
    /// # Examples
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(2, &10);
    /// ```
    pub fn add(&mut self, mut index: usize, value: &T) {
        index += 1;
        while index < self.items.len() {
            self.items[index] = O::add(&self.items[index], value);
            index += index & index.wrapping_neg();
        }
    }

    /// Computes the fold of all elements in the range `[0, end)`.
    ///
    /// # Arguments
    ///
    /// * `range` - A range `..end` specifying the prefix
    ///
    /// # Examples
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(0, &1);
    /// tree.add(1, &2);
    /// tree.add(2, &3);
    /// assert_eq!(tree.fold_to(..3), 6);
    /// ```
    pub fn fold_to(&self, range: RangeTo<usize>) -> T {
        let mut end = range.end;
        let mut result = O::identity();
        while end != 0 {
            result = O::add(&result, &self.items[end]);
            end -= end & end.wrapping_neg();
        }
        result
    }
}

impl<T, O: OpSub<Value = T>> Fenwick<O> {
    /// Subtracts a value from the element at the given index.
    ///
    /// This requires the operation to support subtraction (i.e., implement [`OpSub`]).
    ///
    /// # Arguments
    ///
    /// * `index` - The index to update (must be < length)
    /// * `value` - The value to subtract
    ///
    /// # Examples
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op, OpSub};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// # impl OpSub for AddOp {
    /// #     fn sub(a: &i64, b: &i64) -> i64 { a - b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(2, &10);
    /// tree.sub(2, &3);
    /// ```
    pub fn sub(&mut self, mut index: usize, value: &T) {
        index += 1;
        while index < self.items.len() {
            self.items[index] = O::sub(&self.items[index], value);
            index += index & index.wrapping_neg();
        }
    }

    /// Computes the fold of all elements in the range `[start, end)`.
    ///
    /// This requires the operation to support subtraction (i.e., implement [`OpSub`]).
    ///
    /// # Arguments
    ///
    /// * `range` - A range `[start, end)` specifying the interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op, OpSub};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// # impl OpSub for AddOp {
    /// #     fn sub(a: &i64, b: &i64) -> i64 { a - b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(0, &1);
    /// tree.add(1, &2);
    /// tree.add(2, &3);
    /// tree.add(3, &4);
    /// assert_eq!(tree.fold(1..3), 5);  // 2 + 3
    /// ```
    pub fn fold(&self, range: Range<usize>) -> T {
        let mut result = self.fold_to(..range.end);
        result = O::sub(&result, &self.fold_to(..range.start));
        result
    }
}
