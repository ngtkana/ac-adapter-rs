//! An intrusive splay tree for flexible, generic binary search trees with dynamic aggregation.
//!
//! This crate provides a splay tree where you define the node structure and the aggregation logic
//! via the [`Op`] trait. This allows efficient tree operations while computing arbitrary
//! aggregate values (sum, min, max, etc.) on subtrees.
//!
//! # When to use
//!
//! Use this crate when you need:
//! - A self-balancing binary search tree with O(log n) amortized operations
//! - Flexible control over node values and tree aggregates
//! - Frequent insertions, deletions, and queries on the same dataset
//! - Ordered access to elements (e.g., sorted ranges or k-th element queries)
//!
//! # How it works
//!
//! Insert and remove operations guide traversal via a closure that compares at each node.
//! The tree rebalances via **splaying**: moving the accessed node to the root.
//! This is particularly efficient when accessing the same or nearby nodes repeatedly.
//!
//! You define aggregation (e.g., sum of values) by implementing the [`Op`] trait,
//! which is called whenever the tree structure changes.
//!
//! # Examples
//!
//! ```
//! use intrusive_splay_tree::{Tree, Op, Navi2};
//!
//! struct Value { val: i32, sum: i32 }
//!
//! enum U {}
//! impl Op for U {
//!     type Value = Value;
//!     fn update(node: &mut Value, left: Option<&Value>, right: Option<&Value>) {
//!         node.sum = node.val;
//!         if let Some(l) = left { node.sum += l.sum; }
//!         if let Some(r) = right { node.sum += r.sum; }
//!     }
//! }
//!
//! let mut tree = Tree::<U>::new();
//! tree.insert(Value { val: 10, sum: 10 }, |_, _, _| Navi2::GoDownRight);
//! tree.insert(Value { val: 5, sum: 5 }, |_, _, _| Navi2::GoDownLeft);
//!
//! // Query the entire tree's aggregate
//! assert_eq!(tree.fold_all().unwrap().sum, 15);
//! ```
//!
//! # Core Items
//!
//! - [`Tree<U>`]: The main splay tree structure
//! - [`Op`]: Trait for defining aggregation logic
//! - [`Navi2`]: Navigation enum for insert/split operations (never-terminating search)
//! - [`Navi3`]: Navigation enum for remove/get operations (can terminate early)
//! - [`Node<U>`]: A tree node (exposed for accessing subtree metadata during searches)
//!
//! # Complexity
//!
//! All operations (insert, remove, get, split, merge) are **O(log n) amortized**.
//! Splaying ensures that frequently accessed elements are brought near the root.

use std::{
    borrow::Borrow,
    cmp::Ordering,
    ops::{Bound, Deref, RangeBounds},
    ptr::NonNull,
};

type NN<U> = NonNull<Node<U>>;
type ONN<U> = Option<NonNull<Node<U>>>;

/// A navigation direction for binary searches that always progress (never terminate early).
///
/// This enum is used by [`insert`](Tree::insert), [`split_off`](Tree::split_off),
/// and related operations. Since the search continues until hitting a leaf,
/// you always end up inserting or splitting at a specific location.
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Op, Navi2};
///
/// enum U {}
/// impl Op for U {
///     type Value = i32;
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<U>::new();
/// tree.insert(5, |center, _, _| {
///     if 5 < *center { Navi2::GoDownLeft } else { Navi2::GoDownRight }
/// });
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Navi2 {
    GoDownLeft,
    GoDownRight,
}
impl Navi2 {
    fn lower_bound_by_index<T>(
        index: &mut usize,
        size: &mut impl FnMut(&T) -> usize,
        left: Option<&T>,
    ) -> Self {
        let lsize = left.map_or(0, size);
        match (*index).cmp(&lsize) {
            Ordering::Less | Ordering::Equal => Self::GoDownLeft,
            Ordering::Greater => {
                *index -= lsize + 1;
                Self::GoDownRight
            }
        }
    }
    fn upper_bound_by_index<T>(
        index: &mut usize,
        size: &mut impl FnMut(&T) -> usize,
        left: Option<&T>,
    ) -> Self {
        let lsize = left.map_or(0, size);
        match (*index).cmp(&lsize) {
            Ordering::Less => Self::GoDownLeft,
            Ordering::Equal | Ordering::Greater => {
                *index -= lsize + 1;
                Self::GoDownRight
            }
        }
    }
    fn lower_bound_by_key<T, K: Borrow<Q>, Q: ?Sized + Ord>(
        probe: &Q,
        center: &T,
        f: &mut impl FnMut(&T) -> K,
    ) -> Self {
        match probe.cmp(f(center).borrow()) {
            Ordering::Less | Ordering::Equal => Self::GoDownLeft,
            Ordering::Greater => Self::GoDownRight,
        }
    }
    fn upper_bound_by_key<T, K: Borrow<Q>, Q: ?Sized + Ord>(
        probe: &Q,
        center: &T,
        f: &mut impl FnMut(&T) -> K,
    ) -> Self {
        match probe.cmp(f(center).borrow()) {
            Ordering::Less => Self::GoDownLeft,
            Ordering::Equal | Ordering::Greater => Self::GoDownRight,
        }
    }
}

/// A navigation direction for binary searches that can terminate early upon finding a target.
///
/// This enum is used by [`remove`](Tree::remove), [`get`](Tree::get),
/// and related operations. It allows you to communicate whether the current node is the target
/// or whether to continue searching left or right.
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Op, Navi3};
///
/// enum U {}
/// impl Op for U {
///     type Value = i32;
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<U>::new();
/// tree.insert_lower_bound_by_key(5, |v| *v);
/// tree.insert_lower_bound_by_key(3, |v| *v);
///
/// let removed = tree.remove(|center, _, _| {
///     if 3 < *center { Navi3::GoDownLeft }
///     else if 3 > *center { Navi3::GoDownRight }
///     else { Navi3::Found }
/// });
/// assert_eq!(removed, Some(3));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Navi3 {
    GoDownLeft,
    Found,
    GoDownRight,
}
impl Navi3 {
    fn at<T>(index: &mut usize, size: &mut impl FnMut(&T) -> usize, left: Option<&T>) -> Self {
        let lsize = left.map_or(0, size);
        match (*index).cmp(&lsize) {
            Ordering::Less => Self::GoDownLeft,
            Ordering::Equal => Self::Found,
            Ordering::Greater => {
                *index -= lsize + 1;
                Self::GoDownRight
            }
        }
    }
    fn by_key<T, K: Borrow<Q>, Q: ?Sized + Ord>(
        probe: &Q,
        center: &T,
        f: &mut impl FnMut(&T) -> K,
    ) -> Self {
        match probe.cmp(f(center).borrow()) {
            Ordering::Less => Self::GoDownLeft,
            Ordering::Equal => Self::Found,
            Ordering::Greater => Self::GoDownRight,
        }
    }
}

/// A splay tree.
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Node, Op, Tree, Navi2, Navi3};
/// use std::cmp::Ordering;
///
/// // Boilerplates.
/// struct Value {
///     value: u32,
///     sum: u32,
/// }
///
/// enum U {}
/// impl Op for U {
///     type Value = Value;
///
///     fn update(root: &mut Self::Value, left: Option<&Self::Value>, right: Option<&Self::Value>) {
///         root.sum = root.value;
///         if let Some(left) = left {
///             root.sum = left.sum + root.sum;
///         }
///         if let Some(right) = right {
///             root.sum = root.sum + right.sum;
///         }
///     }
/// }
///
///
/// let mut tree = Tree::<U>::new();
///
/// // Insertions. When inserting, you must specify the full value of the node and the binary search method.
/// for value in 10..=13 {
///     tree.insert(Value { value, sum: value }, |center, _left, _right| {
///         match value.cmp(&center.value) {
///             Ordering::Less | Ordering::Equal => Navi2::GoDownLeft,
///             Ordering::Greater => Navi2::GoDownRight,
///         }
///     });
/// }
///
/// // Removals. You must also specify this when removing.
/// tree.remove(|center, _left, _right| {
///     match center.value.cmp(&12) {
///         Ordering::Less => Navi3::GoDownRight,
///         Ordering::Equal => Navi3::Found,
///         Ordering::Greater => Navi3::GoDownLeft,
///    }
/// });
///
/// // Debugging.
/// assert_eq!(
///     tree.collect().into_iter().map(|value| value.value).collect::<Vec<_>>().as_slice(),
///     &[
///         10,
///         11,
///         13,
///     ],
/// );
///
/// // Folding. Only overall aggregation (`fold_all()`) is available.
/// assert_eq!(tree.fold_all().unwrap().sum, 34);
/// ```
pub struct Tree<U: Op> {
    root: ONN<U>,
}

impl<U: Op> Default for Tree<U> {
    fn default() -> Self {
        Self { root: None }
    }
}

impl<U: Op> Drop for Tree<U> {
    fn drop(&mut self) {
        free_subtree(self.root);
    }
}
/// A guard that temporarily exposes an aggregated value over a tree range.
///
/// `FoldEntry` uses the RAII pattern: it holds a reference to the aggregated value
/// computed over a range of nodes. When dropped, it automatically restores the tree
/// to its original state by merging the split parts back together.
///
/// Access the aggregated value via `Deref` coercion (deref to `U::Value`).
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Op};
///
/// struct Value { val: i32, sum: i32 }
/// enum U {}
/// impl Op for U {
///     type Value = Value;
///     fn update(n: &mut Value, l: Option<&Value>, r: Option<&Value>) {
///         n.sum = n.val;
///         if let Some(l) = l { n.sum += l.sum; }
///         if let Some(r) = r { n.sum += r.sum; }
///     }
/// }
///
/// let mut tree = Tree::<U>::new();
/// tree.insert_lower_bound_by_key(Value { val: 5, sum: 5 }, |v| v.val);
///
/// // FoldEntry automatically restores the tree when dropped
/// if let Some(entry) = tree.fold_by_key(1..10, |v| v.val) {
///     println!("Sum: {}", entry.sum);
///     // Tree is restored here when `entry` is dropped
/// }
/// ```
pub struct FoldEntry<'a, U: Op> {
    tree: &'a mut Tree<U>,
    left: ONN<U>,
    center: NN<U>,
    right: ONN<U>,
}
impl<'a, U: Op> FoldEntry<'a, U> {
    fn maybe_new(
        tree: &'a mut Tree<U>,
        left: ONN<U>,
        center: ONN<U>,
        right: ONN<U>,
    ) -> Option<Self> {
        match center {
            None => {
                tree.root = merge2(left, right);
                None
            }
            Some(center) => Some(Self {
                tree,
                left,
                center,
                right,
            }),
        }
    }
}
impl<U: Op> Deref for FoldEntry<'_, U> {
    type Target = U::Value;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.center.as_ptr()).node_value }
    }
}
impl<U: Op> Drop for FoldEntry<'_, U> {
    fn drop(&mut self) {
        self.tree.root = merge2(merge2(self.left, Some(self.center)), self.right);
    }
}

impl<T, U: Op<Value = T>> Tree<U> {
    /// Creates a new empty tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let tree = Tree::<U>::new();
    /// assert!(tree.collect().is_empty());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Computes the aggregated value over a range using custom closures to define the boundaries.
    ///
    /// Returns a [`FoldEntry`] that provides a reference to the aggregated value.
    /// The tree is temporarily modified (split) during the operation but is automatically
    /// restored when the `FoldEntry` is dropped (RAII pattern).
    ///
    /// # Arguments
    ///
    /// * `start` - Closure guiding traversal to find the left boundary (inclusive)
    /// * `end` - Closure guiding traversal to find the right boundary (exclusive)
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op, Navi2};
    ///
    /// struct Value { val: i32, sum: i32 }
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(n: &mut Value, l: Option<&Value>, r: Option<&Value>) {
    ///         n.sum = n.val;
    ///         if let Some(l) = l { n.sum += l.sum; }
    ///         if let Some(r) = r { n.sum += r.sum; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert(Value { val: 5, sum: 5 }, |_, _, _| Navi2::GoDownLeft);
    /// tree.insert(Value { val: 10, sum: 10 }, |_, _, _| Navi2::GoDownRight);
    ///
    /// // Note: fold operates on ranges defined by custom navigation closures
    /// // It temporarily splits and returns the middle portion
    /// let result = tree.fold_all();
    /// assert_eq!(result.map(|e| e.sum), Some(15));
    /// ```
    pub fn fold(
        &mut self,
        start: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2,
        end: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2,
    ) -> Option<FoldEntry<'_, U>> {
        let (mut lc, right) = split2(self.root.take(), end);
        let (left, center) = split2(lc.take(), start);
        FoldEntry::maybe_new(self, left, center, right)
    }

    /// Computes the aggregated value over a key range.
    ///
    /// Returns a [`FoldEntry`] that provides a reference to the aggregated value
    /// for the specified key range. The tree is temporarily modified but is automatically
    /// restored when the `FoldEntry` is dropped.
    ///
    /// # Arguments
    ///
    /// * `range` - The range bounds (using standard Rust `RangeBounds`)
    /// * `f` - Function extracting the key from each node's value
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Value { key: i32, sum: i32 }
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(n: &mut Value, l: Option<&Value>, r: Option<&Value>) {
    ///         n.sum = n.key;
    ///         if let Some(l) = l { n.sum += l.sum; }
    ///         if let Some(r) = r { n.sum += r.sum; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// for key in 10..18 {
    ///   tree.insert_lower_bound_by_key(Value { key, sum: key }, |v| v.key);
    /// }
    ///
    /// let result = tree.fold_by_key(13..16, |v| v.key);
    /// assert_eq!(result.map(|e| e.sum), Some(13 + 14 + 15));
    /// ```
    pub fn fold_by_key<K, Q: ?Sized + Ord>(
        &mut self,
        range: impl RangeBounds<Q>,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<FoldEntry<'_, U>>
    where
        K: Borrow<Q>,
    {
        let (mut lc, right) = split2(self.root.take(), |center, _, _| match range.end_bound() {
            Bound::Unbounded => Navi2::GoDownRight,
            Bound::Included(key) => Navi2::upper_bound_by_key(key, center, &mut f),
            Bound::Excluded(key) => Navi2::lower_bound_by_key(key, center, &mut f),
        });
        let (left, center) = split2(lc.take(), |center, _, _| match range.start_bound() {
            Bound::Unbounded => Navi2::GoDownLeft,
            Bound::Included(key) => Navi2::lower_bound_by_key(key, center, &mut f),
            Bound::Excluded(key) => Navi2::upper_bound_by_key(key, center, &mut f),
        });
        FoldEntry::maybe_new(self, left, center, right)
    }

    /// Computes the aggregated value over an index range.
    ///
    /// Returns a [`FoldEntry`] that provides a reference to the aggregated value
    /// for elements at the specified index positions. The tree is temporarily modified
    /// but is automatically restored when the `FoldEntry` is dropped.
    ///
    /// # Arguments
    ///
    /// * `range` - The range bounds for indices (0-based)
    /// * `size` - Function computing the subtree size for each node
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op, Navi2};
    ///
    /// struct Value { value: i32, size: usize, sum: i32 }
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(n: &mut Value, l: Option<&Value>, r: Option<&Value>) {
    ///         n.size = 1;
    ///         n.sum = n.value;
    ///         if let Some(l) = l {
    ///             n.size += l.size;
    ///             n.sum += l.sum;
    ///         }
    ///         if let Some(r) = r {
    ///             n.size += r.size;
    ///             n.sum += r.sum;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// let values = [8, 1, 6, 3, 5, 3, 7];
    /// for &value in &values {
    ///     tree.insert(Value { value, size: 1, sum: value }, |_, _, _| Navi2::GoDownRight);
    /// }
    ///
    /// let result = tree.fold_by_index(3..6, |v| v.size);
    /// assert_eq!(result.map(|e| e.sum), Some(3 + 5 + 3));
    /// ```
    pub fn fold_by_index(
        &mut self,
        range: impl RangeBounds<usize>,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<FoldEntry<'_, U>> {
        let (mut lc, right) = split2(self.root.take(), |_, left, _| match range.end_bound() {
            Bound::Unbounded => Navi2::GoDownRight,
            Bound::Included(&(mut index)) => {
                Navi2::upper_bound_by_index(&mut index, &mut size, left)
            }
            Bound::Excluded(&(mut index)) => {
                Navi2::lower_bound_by_index(&mut index, &mut size, left)
            }
        });
        let (left, center) = split2(lc.take(), |_, left, _| match range.start_bound() {
            Bound::Unbounded => Navi2::GoDownLeft,
            Bound::Included(&(mut index)) => {
                Navi2::lower_bound_by_index(&mut index, &mut size, left)
            }
            Bound::Excluded(&(mut index)) => {
                Navi2::upper_bound_by_index(&mut index, &mut size, left)
            }
        });
        FoldEntry::maybe_new(self, left, center, right)
    }

    /// Returns a reference to the aggregated value of the entire tree, computed via [`Op::update`], if the tree is non-empty.
    //
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op, Navi2};
    ///
    /// struct Value {
    ///     val: i32,
    ///     sum: i32,
    /// }
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(root: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         root.sum = root.val;
    ///         if let Some(left) = left {
    ///             root.sum += left.sum;
    ///         }
    ///         if let Some(right) = right {
    ///             root.sum += right.sum;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert(Value { val: 10, sum: 10 }, |_, _, _| Navi2::GoDownRight);
    /// tree.insert(Value { val: 20, sum: 20 }, |_, _, _| Navi2::GoDownRight);
    /// assert_eq!(tree.fold_all().unwrap().sum, 30);
    /// ```
    pub fn fold_all(&self) -> Option<&T> {
        unsafe { self.root.map(|root| &(*root.as_ptr()).node_value) }
    }

    /// Splits the tree using a custom closure to guide the split operation.
    ///
    /// The closure is called at each node to determine whether to descend left or right.
    /// The tree is split so that this tree retains the left subtree and the returned tree
    /// gets the right subtree at the split point.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op, Navi2};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let mut right = tree.split_off(|center, _, _| {
    ///     if *center < 3 { Navi2::GoDownRight } else { Navi2::GoDownLeft }
    /// });
    /// assert_eq!(tree.collect().len(), 1);
    /// assert_eq!(right.collect().len(), 2);
    /// ```
    pub fn split_off(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2) -> Self {
        let (left, right) = split2(self.root.take(), f);
        self.root = left;
        Self { root: right }
    }

    /// Splits the tree at a given index, returning the elements at or after that index.
    ///
    /// Uses a size function to compute subtree sizes and guide the split operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Value { val: i32, size: usize }
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(Value { val: 1, size: 1 }, |v| v.val);
    /// tree.insert_lower_bound_by_key(Value { val: 2, size: 1 }, |v| v.val);
    /// tree.insert_lower_bound_by_key(Value { val: 3, size: 1 }, |v| v.val);
    ///
    /// let mut rest = tree.split_off_at(1, |v| v.size);
    /// assert_eq!(tree.collect().len(), 1);
    /// assert_eq!(rest.collect().len(), 2);
    /// ```
    pub fn split_off_at(&mut self, mut index: usize, mut size: impl FnMut(&T) -> usize) -> Self {
        self.split_off(|_center, left, _right| {
            Navi2::lower_bound_by_index(&mut index, &mut size, left)
        })
    }

    /// Splits the tree at the lower bound of a key, returning elements >= the key.
    ///
    /// The probe type `Q` may differ from the key type `K` via `Borrow`.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Value { key: u32 }
    /// #[derive(Debug, PartialEq)]
    /// enum U {}
    /// impl intrusive_splay_tree::Op for U {
    ///     type Value = Value;
    ///     fn update(_: &mut Value, _: Option<&Value>, _: Option<&Value>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(Value { key: 1 }, |v| v.key);
    /// tree.insert_lower_bound_by_key(Value { key: 2 }, |v| v.key);
    /// tree.insert_lower_bound_by_key(Value { key: 3 }, |v| v.key);
    ///
    /// let mut ge = tree.split_off_lower_bound_by_key(&2, |v| v.key);
    /// assert_eq!(tree.collect().len(), 1);
    /// assert_eq!(ge.collect().len(), 2);
    /// ```
    pub fn split_off_lower_bound_by_key<K, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Self
    where
        K: Borrow<Q>,
    {
        self.split_off(|center, _left, _right| Navi2::lower_bound_by_key(probe, center, &mut f))
    }

    /// Splits the tree at the upper bound of a key, returning elements > the key.
    ///
    /// The probe type `Q` may differ from the key type `K` via `Borrow`.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Value { key: u32 }
    /// enum U {}
    /// impl intrusive_splay_tree::Op for U {
    ///     type Value = Value;
    ///     fn update(_: &mut Value, _: Option<&Value>, _: Option<&Value>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(Value { key: 1 }, |v| v.key);
    /// tree.insert_lower_bound_by_key(Value { key: 2 }, |v| v.key);
    /// tree.insert_lower_bound_by_key(Value { key: 3 }, |v| v.key);
    ///
    /// let mut gt = tree.split_off_upper_bound_by_key(&2, |v| v.key);
    /// assert_eq!(tree.collect().len(), 2);
    /// assert_eq!(gt.collect().len(), 1);
    /// ```
    pub fn split_off_upper_bound_by_key<K, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Self
    where
        K: Borrow<Q>,
    {
        self.split_off(|center, _left, _right| Navi2::upper_bound_by_key(probe, center, &mut f))
    }

    /// Concatenates another tree to this one, consuming the other tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum U {}
    /// impl intrusive_splay_tree::Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree1 = Tree::<U>::new();
    /// tree1.insert_lower_bound_by_key(1, |v| *v);
    /// tree1.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let mut tree2 = Tree::<U>::new();
    /// tree2.insert_lower_bound_by_key(2, |v| *v);
    ///
    /// tree1.append(&mut tree2);
    /// assert_eq!(tree1.collect().len(), 3);
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        self.root = merge2(self.root.take(), other.root.take());
    }

    /// Inserts a new node by using a closure to guide traversal.
    ///
    /// The closure is called at each node to determine whether to descend left or right.
    /// A new node is inserted when encountering a boundary (no child in the chosen direction).
    /// The tree is rebalanced via splaying.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op, Navi2};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert(5, |center, _, _| {
    ///     if 5 < *center { Navi2::GoDownLeft } else { Navi2::GoDownRight }
    /// });
    /// tree.insert(3, |center, _, _| {
    ///     if 3 < *center { Navi2::GoDownLeft } else { Navi2::GoDownRight }
    /// });
    /// assert_eq!(tree.collect().len(), 2);
    /// ```
    pub fn insert(&mut self, node_value: T, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2) {
        let (left, right) = split2(self.root.take(), f);
        let center = unsafe {
            NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                node_value,
                left: None,
                right: None,
                parent: None,
            })))
        };
        self.root = Some(merge3(left, center, right));
    }

    /// Inserts a new node at a specific index position.
    ///
    /// Uses a size function to compute subtree sizes and guide the insertion.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Value { val: i32, size: usize }
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_at(Value { val: 1, size: 1 }, 0, |v| v.size);
    /// tree.insert_at(Value { val: 3, size: 1 }, 1, |v| v.size);
    /// assert_eq!(tree.collect().len(), 2);
    /// ```
    pub fn insert_at(
        &mut self,
        node_value: T,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) {
        self.insert(node_value, |_center, left, _right| {
            Navi2::lower_bound_by_index(&mut index, &mut size, left)
        })
    }

    /// Inserts a new node by extracting a key and using lower_bound semantics.
    ///
    /// Duplicates are inserted to the left (allowing multiple equal keys).
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    /// tree.insert_lower_bound_by_key(7, |v| *v);
    /// assert_eq!(tree.collect().len(), 3);
    /// ```
    pub fn insert_lower_bound_by_key<K: Ord>(&mut self, node_value: T, mut f: impl FnMut(&T) -> K) {
        let probe = f(&node_value);
        self.insert(node_value, |center, _left, _right| {
            Navi2::lower_bound_by_key(&probe, center, &mut f)
        });
    }

    /// Inserts a new node by extracting a key and using upper_bound semantics.
    ///
    /// Duplicates are inserted to the right (allowing multiple equal keys).
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_upper_bound_by_key(5, |v| *v);
    /// tree.insert_upper_bound_by_key(3, |v| *v);
    /// tree.insert_upper_bound_by_key(5, |v| *v);
    /// assert_eq!(tree.collect().len(), 3);
    /// ```
    pub fn insert_upper_bound_by_key<K: Ord>(&mut self, node_value: T, mut f: impl FnMut(&T) -> K) {
        let probe = f(&node_value);
        self.insert(node_value, |center, _left, _right| {
            Navi2::upper_bound_by_key(&probe, center, &mut f)
        });
    }

    /// Removes a node by using a closure to guide traversal and identify the target.
    ///
    /// The closure is called at each node to determine whether to descend left, right, or if the node is found.
    /// If found, the node is removed and its value is returned; otherwise `None` is returned.
    /// The tree is rebalanced via splaying.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op, Navi3};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let removed = tree.remove(|center, _, _| {
    ///     if 3 < *center { Navi3::GoDownLeft }
    ///     else if 3 > *center { Navi3::GoDownRight }
    ///     else { Navi3::Found }
    /// });
    /// assert_eq!(removed, Some(3));
    /// assert_eq!(tree.collect().len(), 1);
    /// ```
    pub fn remove(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3) -> Option<T> {
        unsafe {
            match split3(self.root.take(), f) {
                Split3Result::Success(left, center, right) => {
                    let node_value = Box::from_raw(center.as_ptr()).node_value;
                    self.root = merge2(left, right);
                    Some(node_value)
                }
                Split3Result::Failure(root) => {
                    self.root = root;
                    None
                }
            }
        }
    }

    /// Removes a node at a specific index, returning its value.
    ///
    /// Uses a size function to compute subtree sizes and guide the removal.
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Value { val: i32, size: usize }
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(Value { val: 1, size: 1 }, |v| v.val);
    /// tree.insert_lower_bound_by_key(Value { val: 2, size: 1 }, |v| v.val);
    ///
    /// let removed = tree.remove_at(0, |v| v.size);
    /// assert_eq!(removed.map(|v| v.val), Some(1));
    /// ```
    pub fn remove_at(&mut self, mut index: usize, mut size: impl FnMut(&T) -> usize) -> Option<T> {
        self.remove(|_center, left, _right| Navi3::at(&mut index, &mut size, left))
    }

    /// Removes a node by extracting a key from each node and comparing with a probe.
    ///
    /// This is a convenience wrapper around [`remove`](Self::remove) that extracts a key from each node's value
    /// and compares it with the probe using `Ord`. The probe type `Q` need not match the key type `K` exactly,
    /// as long as `K` implements `Borrow<Q>` (enabling `String` nodes to be searched by `&str`, for example).
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let removed = tree.remove_by_key(&3, |v| *v);
    /// assert_eq!(removed, Some(3));
    /// ```
    pub fn remove_by_key<K: Ord, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        self.remove(|center, _left, _right| Navi3::by_key(probe, center, &mut f))
    }

    /// Retrieves a reference to a node's value via a closure-guided traversal.
    ///
    /// The closure is called at each node to determine whether to descend left, right, or if found.
    /// The tree is rebalanced via splaying but the node is not removed.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op, Navi3};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let found = tree.get(|center, _, _| {
    ///     if 3 < *center { Navi3::GoDownLeft }
    ///     else if 3 > *center { Navi3::GoDownRight }
    ///     else { Navi3::Found }
    /// });
    /// assert_eq!(found, Some(&3));
    /// ```
    pub fn get(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3) -> Option<&T> {
        unsafe {
            match split3(self.root.take(), f) {
                Split3Result::Success(left, center, right) => {
                    self.root = Some(merge3(left, center, right));
                    Some(&(*center.as_ptr()).node_value)
                }
                Split3Result::Failure(root) => {
                    self.root = root;
                    None
                }
            }
        }
    }

    /// Retrieves a reference to a node's value at a specific index.
    ///
    /// Uses a size function to compute subtree sizes and guide the search.
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Value { val: i32, size: usize }
    /// enum U {}
    /// impl Op for U {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(Value { val: 1, size: 1 }, |v| v.val);
    /// tree.insert_lower_bound_by_key(Value { val: 2, size: 1 }, |v| v.val);
    ///
    /// let found = tree.get_at(1, |v| v.size);
    /// assert_eq!(found.map(|v| v.val), Some(2));
    /// ```
    pub fn get_at(&mut self, mut index: usize, mut size: impl FnMut(&T) -> usize) -> Option<&T> {
        self.get(|_center, left, _right| Navi3::at(&mut index, &mut size, left))
    }

    /// Retrieves a reference to a node's value by extracting a key and comparing.
    ///
    /// The probe type `Q` may differ from the key type `K` via `Borrow`.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Value { key: u32 }
    /// enum U {}
    /// impl intrusive_splay_tree::Op for U {
    ///     type Value = Value;
    ///     fn update(_: &mut Value, _: Option<&Value>, _: Option<&Value>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(Value { key: 5 }, |v| v.key);
    /// tree.insert_lower_bound_by_key(Value { key: 3 }, |v| v.key);
    ///
    /// let found = tree.get_by_key(&3, |v| v.key);
    /// assert_eq!(found.map(|v| v.key), Some(3));
    /// ```
    pub fn get_by_key<K: Ord, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<&T>
    where
        K: Borrow<Q>,
    {
        self.get(|center, _left, _right| Navi3::by_key(probe, center, &mut f))
    }

    /// Returns a vector of references to all node values in the tree, in sorted order (in-order traversal).
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum U {}
    /// impl Op for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    ///
    /// let values: Vec<_> = tree.collect().into_iter().copied().collect();
    /// assert_eq!(values, vec![1, 2, 3]);
    /// ```
    pub fn collect(&self) -> Vec<&T> {
        pub fn collect<'a, U: Op>(root: ONN<U>, out: &'a mut Vec<&U::Value>) {
            let Some(root) = root else {
                return;
            };
            unsafe {
                collect((*root.as_ptr()).left, out);
                out.push(&(*root.as_ptr()).node_value);
                collect((*root.as_ptr()).right, out);
            }
        }
        let mut out = vec![];
        collect::<U>(self.root, &mut out);
        out
    }
}

/// An adapter trait for specifying what to do during a structural change.
///
/// The [`update`](Op::update) method is called whenever a node is inserted, deleted, or rotated.
/// It receives the node's value and optional references to the left and right children's aggregated values,
/// allowing you to maintain tree-wide aggregates (e.g., sum, min, max) in O(log n) time.
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Op, Navi2};
///
/// struct Value {
///     val: i32,
///     sum: i32,
/// }
///
/// enum MyOp {}
/// impl Op for MyOp {
///     type Value = Value;
///     fn update(root: &mut Value, left: Option<&Value>, right: Option<&Value>) {
///         root.sum = root.val;
///         if let Some(l) = left { root.sum += l.sum; }
///         if let Some(r) = right { root.sum += r.sum; }
///     }
/// }
///
/// let mut tree = Tree::<MyOp>::new();
/// tree.insert(Value { val: 5, sum: 5 }, |_, _, _| Navi2::GoDownRight);
/// tree.insert(Value { val: 3, sum: 3 }, |_, _, _| Navi2::GoDownRight);
/// assert_eq!(tree.fold_all().unwrap().sum, 8);
/// ```
pub trait Op: Sized {
    type Value;
    fn update(center: &mut Self::Value, left: Option<&Self::Value>, right: Option<&Self::Value>);
}

/// A node of [`Tree`]. We made this public for the time being, expecting the need for the size of the left subtree when performing binary searches during [`insert`](Tree::insert) or [`remove`](Tree::remove) operations.
pub struct Node<U: Op> {
    node_value: U::Value,
    left: ONN<U>,
    right: ONN<U>,
    parent: ONN<U>,
}
impl<U: Op> Node<U> {
    fn update(&mut self) {
        unsafe {
            U::update(
                &mut self.node_value,
                self.left.map(|left| &(*left.as_ptr()).node_value),
                self.right.map(|right| &(*right.as_ptr()).node_value),
            )
        }
    }
}

fn merge2<U: Op>(left: ONN<U>, right: ONN<U>) -> ONN<U> {
    match (left, right) {
        (left, None) => left,
        (None, right) => right,
        (Some(mut left), Some(right)) => unsafe {
            (left, _) = find_and_splay(left, |_root, _left, _right| Navi3::GoDownRight);
            (*left.as_ptr()).right = Some(right);
            (*right.as_ptr()).parent = Some(left);
            (*left.as_ptr()).update();
            Some(left)
        },
    }
}

fn merge3<U: Op>(left: ONN<U>, center: NN<U>, right: ONN<U>) -> NN<U> {
    unsafe {
        if let Some(left) = left {
            (*left.as_ptr()).parent = Some(center);
        }
        if let Some(right) = right {
            (*right.as_ptr()).parent = Some(center);
        }
        (*center.as_ptr()).left = left;
        (*center.as_ptr()).right = right;
        (*center.as_ptr()).update();
        center
    }
}

fn split2<T, U: Op<Value = T>>(
    root: ONN<U>,
    mut f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2,
) -> (ONN<U>, ONN<U>) {
    let Some(root) = root else { return (None, None) };
    let (root, navi) = find_and_splay(root, |node, left, right| match f(node, left, right) {
        Navi2::GoDownRight => Navi3::GoDownRight,
        Navi2::GoDownLeft => Navi3::GoDownLeft,
    });
    unsafe {
        match navi {
            Navi3::GoDownRight => {
                let right = (*root.as_ptr()).right.take();
                if let Some(right) = right {
                    (*right.as_ptr()).parent = None;
                }
                (*root.as_ptr()).update();
                (Some(root), right)
            }
            Navi3::GoDownLeft => {
                let left = (*root.as_ptr()).left.take();
                if let Some(left) = left {
                    (*left.as_ptr()).parent = None;
                }
                (*root.as_ptr()).update();
                (left, Some(root))
            }
            Navi3::Found => unreachable!(),
        }
    }
}

enum Split3Result<U: Op> {
    Success(ONN<U>, NN<U>, ONN<U>),
    Failure(ONN<U>),
}

fn split3<T, U: Op<Value = T>>(
    root: ONN<U>,
    f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3,
) -> Split3Result<U> {
    let Some(root) = root else { return Split3Result::Failure(None) };
    let (root, navi3) = find_and_splay(root, f);
    if navi3 != Navi3::Found {
        return Split3Result::Failure(Some(root));
    }
    unsafe {
        let left = (*root.as_ptr()).left.take();
        if let Some(left) = left {
            (*left.as_ptr()).parent = None;
        }
        let right = (*root.as_ptr()).right.take();
        if let Some(right) = right {
            (*right.as_ptr()).parent = None;
        }
        (*root.as_ptr()).update();
        Split3Result::Success(left, root, right)
    }
}

fn splay<U: Op>(x: NN<U>) -> NN<U> {
    unsafe {
        while let Some(p) = (*x.as_ptr()).parent {
            if let Some(q) = (*p.as_ptr()).parent {
                if (*q.as_ptr()).left == Some(p) && (*p.as_ptr()).left == Some(x) {
                    // zig-zig: left-left
                    rotate_right(q);
                    rotate_right(p);
                } else if (*q.as_ptr()).right == Some(p) && (*p.as_ptr()).right == Some(x) {
                    // zig-zig: right-right
                    rotate_left(q);
                    rotate_left(p);
                } else {
                    // zig-zag
                    if (*p.as_ptr()).left == Some(x) {
                        rotate_right(p);
                    } else {
                        rotate_left(p);
                    }
                    if (*q.as_ptr()).left == Some(x) {
                        rotate_right(q);
                    } else {
                        rotate_left(q);
                    }
                }
            } else {
                // zig: parent is root
                if (*p.as_ptr()).left == Some(x) {
                    rotate_right(p);
                } else {
                    rotate_left(p);
                }
            }
        }
        x
    }
}
fn rotate_left<U: Op>(x: NN<U>) -> NN<U> {
    unsafe {
        let y = (*x.as_ptr()).right.unwrap();
        let c = (*y.as_ptr()).left;
        (*x.as_ptr()).right = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).left = Some(x);
        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);
        (*x.as_ptr()).update();
        (*y.as_ptr()).update();
        y
    }
}
fn rotate_right<U: Op>(x: NN<U>) -> NN<U> {
    unsafe {
        let y = (*x.as_ptr()).left.unwrap();
        let c = (*y.as_ptr()).right;
        (*x.as_ptr()).left = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).right = Some(x);
        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);
        (*x.as_ptr()).update();
        (*y.as_ptr()).update();
        y
    }
}
fn free_subtree<U: Op>(root: ONN<U>) {
    let mut stack = Vec::new();
    if let Some(r) = root {
        stack.push(r);
    }
    while let Some(node) = stack.pop() {
        unsafe {
            if let Some(left) = (*node.as_ptr()).left {
                stack.push(left);
            }
            if let Some(right) = (*node.as_ptr()).right {
                stack.push(right);
            }
            drop(Box::from_raw(node.as_ptr()));
        }
    }
}
fn find_and_splay<T, U: Op<Value = T>>(
    root: NN<U>,
    mut f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3,
) -> (NN<U>, Navi3) {
    unsafe {
        let mut node = root;
        let navi = loop {
            let node_ref = &(*node.as_ptr());
            match f(
                &node_ref.node_value,
                node_ref.left.map(|left| &(*left.as_ptr()).node_value),
                node_ref.right.map(|right| &(*right.as_ptr()).node_value),
            ) {
                Navi3::GoDownLeft => {
                    if let Some(left) = node_ref.left {
                        node = left;
                    } else {
                        break Navi3::GoDownLeft;
                    }
                }
                Navi3::GoDownRight => {
                    if let Some(right) = node_ref.right {
                        node = right;
                    } else {
                        break Navi3::GoDownRight;
                    }
                }
                Navi3::Found => {
                    break Navi3::Found;
                }
            }
        };
        (splay(node), navi)
    }
}
