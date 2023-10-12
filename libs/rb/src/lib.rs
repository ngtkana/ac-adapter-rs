#![warn(missing_docs)]
//! A list based on red-black tree.

use std::marker::PhantomData;
use std::ops::RangeBounds;

/// A trait that represents an operation on a value.
pub trait Op {
    /// The type of the value.
    type Value;
    /// The type of the result of reduce.
    type Reduce;

    /// Reduct a single value.
    fn once(value: &Self::Value) -> Self::Reduce;

    /// The operation that is used to reduce the elements.
    fn op(lhs: &Self::Reduce, rhs: &Self::Reduce) -> Self::Reduce;
}

/// A type to represent no reduce operation.
pub struct Nop<T> {
    __marker: PhantomData<T>,
}
impl<T> Op for Nop<T> {
    type Value = T;
    type Reduce = ();
    fn once(_: &Self::Value) {}
    fn op(_: &Self::Reduce, _: &Self::Reduce) {}
}

/// A list based on red-black tree.
pub struct Rblist<O: Op> {
    __maker: std::marker::PhantomData<O>,
}
impl<O: Op> Rblist<O> {
    /// Makes a new, empty `Rblist`.
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    /// ```should_panic
    /// use rb::Rblist;
    /// use rb::Nop;
    ///
    /// let mut list = Rblist::<Nop<_>>::new();
    /// list.push_back('a');
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns true if the list contains no elements.
    ///
    /// # Examples
    /// ```should_panic
    /// use rb::Rblist;
    /// use rb::Nop;
    ///
    /// let mut list = Rblist::<Nop<_>>::new();
    /// assert!(list.is_empty());
    /// list.push_back('a');
    /// assert!(!list.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        todo!()
    }

    /// Returns the number of elements in the list.
    ///
    /// # Examples
    /// ```should_panic
    /// use rb::Rblist;
    /// use rb::Nop;
    ///
    /// let mut list = Rblist::<Nop<_>>::new();
    /// assert_eq!(list.len(), 0);
    /// list.push_back('a');
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        todo!()
    }

    /// Reduces the elements to a single one, by repeatedly applying [`Op::op`].
    ///
    /// # Examples
    /// ```should_panic
    /// use rb::Rblist;
    /// use rb::Op;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = char;
    ///     type Reduce = String;
    ///     fn once(value: &char) -> String {
    ///         value.to_string()
    ///     }
    ///     fn op(lhs: &String, rhs: &String) -> String {
    ///         format!("{lhs}{rhs}")
    ///     }
    /// }
    ///
    /// let mut list = Rblist::<O>::new();
    /// list.push_back('a');
    /// list.push_back('b');
    /// assert_eq!(&list.reduce(..), "ab");
    /// ```
    pub fn reduce(&self, range: impl RangeBounds<usize>) -> O::Reduce {
        drop(range);
        todo!()
    }

    /// Returns the index of the partition point according to the given predicate (the index of the first element of the second partition).
    ///
    /// # Examples
    /// ```should_panic
    /// use rb::Rblist;
    /// use rb::Op;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = char;
    ///     type Reduce = String;
    ///     fn once(value: &char) -> String {
    ///         value.to_string()
    ///     }
    ///     fn op(lhs: &String, rhs: &String) -> String {
    ///         format!("{lhs}{rhs}")
    ///     }
    /// }
    ///
    /// let mut list = Rblist::<O>::new();
    /// list.push_back('a');
    /// list.push_back('b');
    /// assert_eq!(list.reduce_partition_point(.., |reduce| reduce.len() <= 1), 1);
    /// ```
    pub fn reduce_partition_point(
        &self,
        range: impl RangeBounds<usize>,
        predicate: impl Fn(&O::Reduce) -> bool,
    ) -> usize {
        drop(range);
        drop(predicate);
        todo!()
    }

    /// Appends an element to the back of the list.
    ///
    /// # Examples
    /// ```should_panic
    /// use rb::Rblist;
    /// use rb::Nop;
    ///
    /// let mut list = Rblist::<Nop<_>>::new();
    /// list.push_back('a');
    /// list.push_back('b');
    /// assert_eq!(list.len(), 2);
    /// ```
    pub fn push_back(&mut self, value: O::Value) {
        drop(value);
        todo!()
    }
}

impl<O: Op> Default for Rblist<O> {
    fn default() -> Self {
        todo!()
    }
}

impl<O: Op> FromIterator<O::Value> for Rblist<O> {
    fn from_iter<I: IntoIterator<Item = O::Value>>(_iter: I) -> Self {
        todo!()
    }
}
