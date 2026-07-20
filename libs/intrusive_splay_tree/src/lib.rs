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
//! use intrusive_splay_tree::{Tree, Op};
//!
//! struct Value { value: i32, sum: i32 }
//!
//! enum O {}
//! impl Op for O {
//!     type Value = Value;
//!     fn update(node: &mut Value, left: Option<&Value>, right: Option<&Value>) {
//!         node.sum = node.value;
//!         if let Some(l) = left { node.sum += l.sum; }
//!         if let Some(r) = right { node.sum += r.sum; }
//!     }
//! }
//!
//! let mut tree = Tree::<O>::new();
//! tree.insert_lower_bound_by_key(Value { value: 10, sum: 10 }, |v| v.value);
//! tree.insert_lower_bound_by_key(Value { value: 5, sum: 5 }, |v| v.value);
//!
//! // Query the entire tree's aggregate
//! assert_eq!(tree.fold_all().unwrap().sum, 15);
//! ```
//!
//! # Core Items
//!
//! - [`Tree<O>`]: The main splay tree structure
//! - [`Op`]: Trait for defining aggregation logic
//! - [`Navi2`]: Navigation enum for insert/split operations (never-terminating search)
//! - [`Navi3`]: Navigation enum for remove/get operations (can terminate early)
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

mod node;
use node::{Node, Split3Result, free_subtree, merge2, merge3, split2, split3};

type Nn<O> = NonNull<Node<O>>;
type Onn<O> = Option<NonNull<Node<O>>>;

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
/// enum O {}
/// impl Op for O {
///     type Value = i32;
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<O>::new();
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
            Ordering::Equal => {
                *index -= lsize;
                Self::GoDownRight
            }
            Ordering::Greater => {
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
/// enum O {}
/// impl Op for O {
///     type Value = i32;
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<O>::new();
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
/// use intrusive_splay_tree::{Op, Tree, Navi2, Navi3};
/// use std::cmp::Ordering;
///
/// // Boilerplates.
/// struct Value {
///     value: u32,
///     sum: u32,
/// }
///
/// enum O {}
/// impl Op for O {
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
/// let mut tree = Tree::<O>::new();
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
pub struct Tree<O: Op> {
    root: Onn<O>,
}

impl<O: Op> Default for Tree<O> {
    fn default() -> Self {
        Self { root: None }
    }
}

impl<O: Op> Drop for Tree<O> {
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
/// Access the aggregated value via `Deref` coercion (deref to `O::Value`).
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Op};
///
/// struct Value { value: i32, sum: i32 }
/// enum O {}
/// impl Op for O {
///     type Value = Value;
///     fn update(n: &mut Value, l: Option<&Value>, r: Option<&Value>) {
///         n.sum = n.value;
///         if let Some(l) = l { n.sum += l.sum; }
///         if let Some(r) = r { n.sum += r.sum; }
///     }
/// }
///
/// let mut tree = Tree::<O>::new();
/// tree.insert_lower_bound_by_key(Value { value: 5, sum: 5 }, |v| v.value);
///
/// // FoldEntry automatically restores the tree when dropped
/// if let Some(entry) = tree.fold_by_key(1..10, |v| v.value) {
///     println!("Sum: {}", entry.sum);
///     // Tree is restored here when `entry` is dropped
/// }
/// ```
pub struct FoldEntry<'a, O: Op> {
    tree: &'a mut Tree<O>,
    left: Onn<O>,
    center: Nn<O>,
    right: Onn<O>,
}
impl<'a, O: Op> FoldEntry<'a, O> {
    fn maybe_new(
        tree: &'a mut Tree<O>,
        left: Onn<O>,
        center: Onn<O>,
        right: Onn<O>,
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
impl<O: Op> Deref for FoldEntry<'_, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.center.as_ptr()).value }
    }
}
impl<O: Op> Drop for FoldEntry<'_, O> {
    fn drop(&mut self) {
        self.tree.root = merge2(merge2(self.left, Some(self.center)), self.right);
    }
}

impl<T, O: Op<Value = T>> Tree<O> {
    /// Creates a new empty tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let tree = Tree::<O>::new();
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
    /// struct Value { value: i32, sum: i32 }
    /// enum O {}
    /// impl Op for O {
    ///     type Value = Value;
    ///     fn update(n: &mut Value, l: Option<&Value>, r: Option<&Value>) {
    ///         n.sum = n.value;
    ///         if let Some(l) = l { n.sum += l.sum; }
    ///         if let Some(r) = r { n.sum += r.sum; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Value { value: 5, sum: 5 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Value { value: 10, sum: 10 }, |v| v.value);
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
    ) -> Option<FoldEntry<'_, O>> {
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = Value;
    ///     fn update(n: &mut Value, l: Option<&Value>, r: Option<&Value>) {
    ///         n.sum = n.key;
    ///         if let Some(l) = l { n.sum += l.sum; }
    ///         if let Some(r) = r { n.sum += r.sum; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
    ) -> Option<FoldEntry<'_, O>>
    where
        K: Borrow<Q>,
    {
        let root = self.root.take();
        let (lc, right) = match range.end_bound() {
            Bound::Unbounded => (root, None),
            Bound::Included(key) => split2(root, |center, _, _| {
                Navi2::upper_bound_by_key(key, center, &mut f)
            }),
            Bound::Excluded(key) => split2(root, |center, _, _| {
                Navi2::lower_bound_by_key(key, center, &mut f)
            }),
        };
        let (left, center) = match range.start_bound() {
            Bound::Unbounded => (None, root),
            Bound::Included(key) => split2(lc, |center, _, _| {
                Navi2::lower_bound_by_key(key, center, &mut f)
            }),
            Bound::Excluded(key) => split2(lc, |center, _, _| {
                Navi2::upper_bound_by_key(key, center, &mut f)
            }),
        };
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
    /// enum O {}
    /// impl Op for O {
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
    /// let mut tree = Tree::<O>::new();
    /// let values = [8, 1, 6, 3, 5, 4, 7];
    /// for &value in &values {
    ///     tree.push_back(Value { value, size: 1, sum: value });
    /// }
    ///
    /// let result = tree.fold_by_index(3..6, |v| v.size);
    /// assert_eq!(result.map(|e| e.sum), Some(3 + 5 + 4));
    /// ```
    pub fn fold_by_index(
        &mut self,
        range: impl RangeBounds<usize>,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<FoldEntry<'_, O>> {
        let root = self.root.take();
        let (root, right) = match range.end_bound() {
            Bound::Unbounded => (root, None),
            Bound::Included(&(mut index)) => split2(root, |_, left, _| {
                Navi2::upper_bound_by_index(&mut index, &mut size, left)
            }),
            Bound::Excluded(&(mut index)) => split2(root, |_, left, _| {
                Navi2::lower_bound_by_index(&mut index, &mut size, left)
            }),
        };
        let (left, center) = match range.start_bound() {
            Bound::Unbounded => (None, root),
            Bound::Included(&(mut index)) => split2(root, |_, left, _| {
                Navi2::lower_bound_by_index(&mut index, &mut size, left)
            }),
            Bound::Excluded(&(mut index)) => split2(root, |_, left, _| {
                Navi2::upper_bound_by_index(&mut index, &mut size, left)
            }),
        };
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
    ///     value: i32,
    ///     sum: i32,
    /// }
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = Value;
    ///     fn update(root: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         root.sum = root.value;
    ///         if let Some(left) = left {
    ///             root.sum += left.sum;
    ///         }
    ///         if let Some(right) = right {
    ///             root.sum += right.sum;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// for &value in &[10, 20, 30] {
    ///     tree.push_back(Value { value, sum: value });
    /// }
    /// assert_eq!(tree.fold_all().unwrap().sum, 60);
    /// ```
    pub fn fold_all(&self) -> Option<&T> {
        unsafe { self.root.map(|root| &(*root.as_ptr()).value) }
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
    /// struct Value { value: i32, size: usize }
    /// enum O {}
    /// impl Op for O {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Value { value: 1, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Value { value: 2, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Value { value: 3, size: 1 }, |v| v.value);
    ///
    /// let mut rest = tree.split_off_by_index(1, |v| v.size);
    /// assert_eq!(tree.collect().len(), 1);
    /// assert_eq!(rest.collect().len(), 2);
    /// ```
    pub fn split_off_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Self {
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
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Value = Value;
    ///     fn update(_: &mut Value, _: Option<&Value>, _: Option<&Value>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Value = Value;
    ///     fn update(_: &mut Value, _: Option<&Value>, _: Option<&Value>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree1 = Tree::<O>::new();
    /// tree1.insert_lower_bound_by_key(1, |v| *v);
    /// tree1.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let mut tree2 = Tree::<O>::new();
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
                value: node_value,
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
    /// struct Value { value: i32, size: usize }
    /// enum O {}
    /// impl Op for O {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_by_index(Value { value: 1, size: 1 }, 0, |v| v.size);
    /// tree.insert_by_index(Value { value: 3, size: 1 }, 1, |v| v.size);
    /// assert_eq!(tree.collect().len(), 2);
    /// ```
    pub fn insert_by_index(
        &mut self,
        node_value: T,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) {
        self.insert(node_value, |_center, left, _right| {
            Navi2::lower_bound_by_index(&mut index, &mut size, left)
        });
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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

    /// Inserts a new node at the front (left-most position) of the tree.
    ///
    /// This method always navigates left until reaching a leaf, inserting
    /// the new node as the left-most element. The tree is rebalanced via splaying.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_front(5);
    /// tree.push_front(2);
    ///
    /// assert_eq!(tree.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, node_value: T) {
        self.insert(node_value, |_, _, _| Navi2::GoDownLeft);
    }

    /// Inserts a new node at the back (right-most position) of the tree.
    ///
    /// This method always navigates right until reaching a leaf, inserting
    /// the new node as the right-most element. The tree is rebalanced via splaying.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_back(5);
    /// tree.push_back(7);
    ///
    /// assert_eq!(tree.back(), Some(&7));
    /// ```
    pub fn push_back(&mut self, node_value: T) {
        self.insert(node_value, |_, _, _| Navi2::GoDownRight);
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
                    let node_value = Box::from_raw(center.as_ptr()).value;
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
    /// struct Value { value: i32, size: usize }
    /// enum O {}
    /// impl Op for O {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Value { value: 1, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Value { value: 2, size: 1 }, |v| v.value);
    ///
    /// let removed = tree.remove_by_index(0, |v| v.size);
    /// assert_eq!(removed.map(|v| v.value), Some(1));
    /// ```
    pub fn remove_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<T> {
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let removed = tree.remove_by_key(&3, |v| *v);
    /// assert_eq!(removed, Some(3));
    /// ```
    pub fn remove_by_key<K: Ord + Borrow<Q>, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<T> {
        self.remove(|center, _left, _right| Navi3::by_key(probe, center, &mut f))
    }

    /// Removes and returns the minimum element in the tree (leftmost node).
    ///
    /// This method navigates to the leftmost node, removes it, and returns its value.
    /// Returns `None` if the tree is empty. The tree is rebalanced via splaying.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_back(5);
    /// tree.push_back(2);
    /// tree.push_back(7);
    ///
    /// assert_eq!(tree.pop_front(), Some(5));
    /// assert_eq!(tree.pop_front(), Some(2));
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.remove(
            |_, left, _| {
                if left.is_some() { Navi3::GoDownLeft } else { Navi3::Found }
            },
        )
    }

    /// Removes and returns the maximum element in the tree (rightmost node).
    ///
    /// This method navigates to the rightmost node, removes it, and returns its value.
    /// Returns `None` if the tree is empty. The tree is rebalanced via splaying.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_back(5);
    /// tree.push_back(2);
    /// tree.push_back(7);
    ///
    /// assert_eq!(tree.pop_back(), Some(7));
    /// assert_eq!(tree.pop_back(), Some(2));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.remove(
            |_, _, right| {
                if right.is_some() { Navi3::GoDownRight } else { Navi3::Found }
            },
        )
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
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
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
                    Some(&(*center.as_ptr()).value)
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
    /// struct Value { value: i32, size: usize }
    /// enum O {}
    /// impl Op for O {
    ///     type Value = Value;
    ///     fn update(center: &mut Value, left: Option<&Value>, right: Option<&Value>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Value { value: 1, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Value { value: 2, size: 1 }, |v| v.value);
    ///
    /// let found = tree.get_by_index(1, |v| v.size);
    /// assert_eq!(found.map(|v| v.value), Some(2));
    /// ```
    pub fn get_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<&T> {
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
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Value = Value;
    ///     fn update(_: &mut Value, _: Option<&Value>, _: Option<&Value>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Value { key: 5 }, |v| v.key);
    /// tree.insert_lower_bound_by_key(Value { key: 3 }, |v| v.key);
    ///
    /// let found = tree.get_by_key(&3, |v| v.key);
    /// assert_eq!(found.map(|v| v.key), Some(3));
    /// ```
    pub fn get_by_key<K: Ord + Borrow<Q>, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<&T> {
        self.get(|center, _left, _right| Navi3::by_key(probe, center, &mut f))
    }

    /// Returns a reference to the minimum element in the tree (leftmost node).
    ///
    /// This method navigates to the leftmost node in the tree, which contains
    /// the minimum value. Returns `None` if the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    /// tree.insert_lower_bound_by_key(7, |v| *v);
    ///
    /// assert_eq!(tree.front(), Some(&2));
    /// ```
    pub fn front(&mut self) -> Option<&T> {
        self.get(
            |_, left, _| {
                if left.is_some() { Navi3::GoDownLeft } else { Navi3::Found }
            },
        )
    }

    /// Returns a reference to the maximum element in the tree (rightmost node).
    ///
    /// This method navigates to the rightmost node in the tree, which contains
    /// the maximum value. Returns `None` if the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    /// tree.insert_lower_bound_by_key(7, |v| *v);
    ///
    /// assert_eq!(tree.back(), Some(&7));
    /// ```
    pub fn back(&mut self) -> Option<&T> {
        self.get(
            |_, _, right| {
                if right.is_some() { Navi3::GoDownRight } else { Navi3::Found }
            },
        )
    }

    /// Returns a vector of references to all node values in the tree, in sorted order (in-order traversal).
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    ///
    /// let values: Vec<_> = tree.collect().into_iter().copied().collect();
    /// assert_eq!(values, vec![1, 2, 3]);
    /// ```
    pub fn collect(&self) -> Vec<&T> {
        pub fn collect<O: Op>(root: Onn<O>, out: &mut Vec<&O::Value>) {
            let Some(root) = root else {
                return;
            };
            unsafe {
                collect((*root.as_ptr()).left, out);
                out.push(&(*root.as_ptr()).value);
                collect((*root.as_ptr()).right, out);
            }
        }
        let mut out = vec![];
        collect::<O>(self.root, &mut out);
        out
    }
}

/// An adapter trait for specifying what to do during a structural change.
///
/// The [`update`](Op::update) method is called whenever a node is inserted, deleted, or rotated.
/// It receives the node's value and optional references to the left and right children's aggregated values,
/// allowing you to maintain tree-wide aggregates (e.g., sum, min, max) in O(log n) time.
///
/// # Invariants
///
/// The `update` method must be associative and must not depend on tree structure or traversal order.
/// Implementations that violate this invariant will produce incorrect aggregation results.
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Op, Navi2};
///
/// struct Value {
///     value: i32,
///     sum: i32,
/// }
///
/// enum MyOp {}
/// impl Op for MyOp {
///     type Value = Value;
///     fn update(root: &mut Value, left: Option<&Value>, right: Option<&Value>) {
///         root.sum = root.value;
///         if let Some(l) = left { root.sum += l.sum; }
///         if let Some(r) = right { root.sum += r.sum; }
///     }
/// }
///
/// let mut tree = Tree::<MyOp>::new();
/// tree.insert(Value { value: 5, sum: 5 }, |_, _, _| Navi2::GoDownRight);
/// tree.insert(Value { value: 3, sum: 3 }, |_, _, _| Navi2::GoDownRight);
/// assert_eq!(tree.fold_all().unwrap().sum, 8);
/// ```
pub trait Op: Sized {
    type Value;
    fn update(center: &mut Self::Value, left: Option<&Self::Value>, right: Option<&Self::Value>);
}
