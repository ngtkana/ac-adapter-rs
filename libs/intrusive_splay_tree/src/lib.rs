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
//! struct Store { value: i32, sum: i32 }
//! impl Store {
//!     fn value(&self) -> i32 { self.value }
//! }
//!
//! enum O {}
//! impl Op for O {
//!     type Store = Store;
//!     fn update(node: &mut Store, left: Option<&Store>, right: Option<&Store>) {
//!         node.sum = node.value;
//!         if let Some(l) = left { node.sum += l.sum; }
//!         if let Some(r) = right { node.sum += r.sum; }
//!     }
//! }
//!
//! let mut tree = Tree::<O>::new();
//! tree.insert_lower_bound_by_key(Store { value: 10, sum: 10 }, Store::value);
//! tree.insert_lower_bound_by_key(Store { value: 5, sum: 5 }, Store::value);
//!
//! // Query the entire tree's aggregate
//! assert_eq!(tree.fold().unwrap().sum, 15);
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
    ops::{Bound, Deref, DerefMut, RangeBounds},
    ptr::NonNull,
};

mod node;
use node::{Node, Onn, Split3Result, free_subtree, merge2, merge3, split2, split3};

use crate::node::visit;

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
///     type Store = i32;
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
    fn by_index<T>(
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
///     type Store = i32;
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
    fn by_index<T>(
        index: &mut usize,
        size: &mut impl FnMut(&T) -> usize,
        left: Option<&T>,
    ) -> Self {
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
/// struct Store {
///     value: u32,
///     sum: u32,
/// }
///
/// enum O {}
/// impl Op for O {
///     type Store = Store;
///
///     fn update(root: &mut Self::Store, left: Option<&Self::Store>, right: Option<&Self::Store>) {
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
///     tree.insert(Store { value, sum: value }, |center, _left, _right| {
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
///     tree.collect(|value| value.value).as_slice(),
///     &[
///         10,
///         11,
///         13,
///     ],
/// );
///
/// // Folding. Only overall aggregation (`fold()`) is available.
/// assert_eq!(tree.fold().unwrap().sum, 34);
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

/// A mutable reference to a range of elements within a tree.
///
/// This type is returned by [`range_by_key`](Tree::range_by_key) and [`range_by_index`](Tree::range_by_index).
/// It provides temporary mutable access to a contiguous range of the tree while maintaining the overall tree structure.
/// When the entry is dropped, the range is automatically reintegrated into the tree.
///
/// # Invariants
///
/// The `RangeEntry` maintains the tree structure invariants:
/// - The tree is split into three parts: left (untouched), center (the range), and right (untouched)
/// - Modifying the center does not affect the left or right subtrees
/// - When dropped, all three parts are automatically merged back together
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Op};
///
/// enum O {}
/// impl Op for O {
///     type Store = i32;
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<O>::new();
/// tree.insert_lower_bound_by_key(1, |v| *v);
/// tree.insert_lower_bound_by_key(2, |v| *v);
/// tree.insert_lower_bound_by_key(3, |v| *v);
///
/// // Extract range [1, 3] and modify it
/// let mut range = tree.range_by_key(1..=3, |v| *v);
/// // Modifications to range stay within the range
/// ```
pub struct RangeEntry<'a, O: Op> {
    tree: &'a mut Tree<O>,
    left: Onn<O>,
    center: Tree<O>,
    right: Onn<O>,
}
impl<'a, O: Op> RangeEntry<'a, O> {
    fn new(tree: &'a mut Tree<O>, left: Onn<O>, center: Onn<O>, right: Onn<O>) -> Self {
        Self {
            tree,
            left,
            center: Tree { root: center },
            right,
        }
    }
}
impl<O: Op> Deref for RangeEntry<'_, O> {
    type Target = Tree<O>;

    fn deref(&self) -> &Self::Target {
        &self.center
    }
}
impl<O: Op> DerefMut for RangeEntry<'_, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.center
    }
}
impl<O: Op> Drop for RangeEntry<'_, O> {
    fn drop(&mut self) {
        self.tree.root = merge2(merge2(self.left, self.center.root.take()), self.right);
    }
}

impl<T, O: Op<Store = T>> Tree<O> {
    /// Creates a new empty tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let tree = Tree::<O>::new();
    /// assert!(tree.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns `true` if the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let tree = Tree::<O>::new();
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Returns the total size of the tree using the provided size function.
    ///
    /// The size function is typically used to compute aggregate size information
    /// (e.g., the sum of element counts if each element can span multiple indices).
    /// If the tree maintains size information via the [`Op`] trait, you can extract
    /// it from the root node's aggregate value.
    ///
    /// # Arguments
    ///
    /// * `size` - A closure that computes the size component of the aggregate value
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Store { size: usize }
    /// impl Store { fn size(&self) -> usize { self.size } }
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { size: 1 }, |_| 0);
    /// tree.insert_lower_bound_by_key(Store { size: 1 }, |_| 0);
    ///
    /// assert_eq!(tree.len(Store::size), 2);
    /// ```
    pub fn len(&self, size: impl Fn(&T) -> usize) -> usize {
        self.root
            .map_or(0, |root| unsafe { size(&(*root.as_ptr()).store) })
    }

    /// Extracts a range of elements by key bounds, returning a mutable reference to the range.
    ///
    /// This method splits the tree to isolate elements within the specified key range,
    /// giving you a [`RangeEntry`] that implements [`Deref`] and [`DerefMut`] to [`Tree<O>`].
    /// When the entry is dropped, the range is automatically reintegrated into the original tree.
    ///
    /// # Arguments
    ///
    /// * `range` - The range bounds (using standard Rust [`RangeBounds`] syntax: `..`, `1..`, `..3`, `1..3`, `1..=3`, etc.)
    /// * `f` - A closure that extracts a sortable key from each element
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// // Get elements in range [2, 3]
    /// let range = tree.range_by_key(2..=3, |v| *v);
    /// let collected = range.collect(|v| *v);
    /// ```
    pub fn range_by_key<K: Borrow<Q>, Q: ?Sized + Ord>(
        &mut self,
        range: impl RangeBounds<Q>,
        mut f: impl FnMut(&T) -> K,
    ) -> RangeEntry<'_, O> {
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
            Bound::Unbounded => (None, lc),
            Bound::Included(key) => split2(lc, |center, _, _| {
                Navi2::lower_bound_by_key(key, center, &mut f)
            }),
            Bound::Excluded(key) => split2(lc, |center, _, _| {
                Navi2::upper_bound_by_key(key, center, &mut f)
            }),
        };
        RangeEntry::new(self, left, center, right)
    }

    /// Extracts a range of elements by index bounds, returning a mutable reference to the range.
    ///
    /// This method splits the tree to isolate elements at indices within the specified range,
    /// giving you a [`RangeEntry`] that implements [`Deref`] and [`DerefMut`] to [`Tree<O>`].
    /// When the entry is dropped, the range is automatically reintegrated into the original tree.
    ///
    /// # Arguments
    ///
    /// * `range` - The index bounds (using standard Rust [`RangeBounds`] syntax)
    /// * `size` - A closure that computes the logical size of each element (often 1 for single-element nodes)
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Store { value: i32, size: usize }
    /// impl Store { fn size(&self) -> usize { self.size } }
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 10, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Store { value: 20, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Store { value: 30, size: 1 }, |v| v.value);
    ///
    /// // Get elements at indices [0, 2)
    /// let range = tree.range_by_index(0..2, Store::size);
    /// let collected = range.collect(|v| v.value);
    /// ```
    pub fn range_by_index(
        &mut self,
        range: impl RangeBounds<usize>,
        mut size: impl FnMut(&T) -> usize,
    ) -> RangeEntry<'_, O> {
        let root = self.root.take();
        let (root, right) = match range.end_bound() {
            Bound::Unbounded => (root, None),
            Bound::Included(&(mut index)) => {
                index += 1;
                split2(root, |_, left, _| {
                    Navi2::by_index(&mut index, &mut size, left)
                })
            }
            Bound::Excluded(&(mut index)) => split2(root, |_, left, _| {
                Navi2::by_index(&mut index, &mut size, left)
            }),
        };
        let (left, center) = match range.start_bound() {
            Bound::Unbounded => (None, root),
            Bound::Included(&(mut index)) => split2(root, |_, left, _| {
                Navi2::by_index(&mut index, &mut size, left)
            }),
            Bound::Excluded(&(mut index)) => {
                index += 1;
                split2(root, |_, left, _| {
                    Navi2::by_index(&mut index, &mut size, left)
                })
            }
        };
        RangeEntry::new(self, left, center, right)
    }

    /// Computes and returns the aggregate value of the entire tree.
    ///
    /// This method returns a reference to the aggregated value maintained at the tree's root.
    /// The aggregation is computed by the [`Op`] trait's [`update`](Op::update) method whenever
    /// the tree structure changes. This is O(1) since the aggregate is always kept up-to-date.
    ///
    /// Returns `None` if the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// struct Store { value: i32, sum: i32 }
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.sum = center.value;
    ///         if let Some(l) = left { center.sum += l.sum; }
    ///         if let Some(r) = right { center.sum += r.sum; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 5, sum: 5 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Store { value: 3, sum: 3 }, |v| v.value);
    ///
    /// assert_eq!(tree.fold().map(|v| v.sum), Some(8));
    /// ```
    pub fn fold(&self) -> Option<&T> {
        unsafe { self.root.map(|root| &(*root.as_ptr()).store) }
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
    ///     type Store = i32;
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
    /// assert_eq!(tree.collect(|_| ()).len(), 1);
    /// assert_eq!(right.collect(|_| ()).len(), 2);
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
    /// struct Store { value: i32, size: usize }
    /// impl Store {
    ///     fn value(&self) -> i32 { self.value }
    ///     fn size(&self) -> usize { self.size }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 1, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 2, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 3, size: 1 }, Store::value);
    ///
    /// let mut rest = tree.split_off_by_index(1, Store::size);
    /// assert_eq!(tree.len(Store::size), 1);
    /// assert_eq!(rest.len(Store::size), 2);
    /// ```
    pub fn split_off_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Self {
        self.split_off(|_center, left, _right| Navi2::by_index(&mut index, &mut size, left))
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
    /// struct Store { key: u32 }
    /// impl Store {
    ///     fn key(&self) -> u32 { self.key }
    /// }
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Store = Store;
    ///     fn update(_: &mut Store, _: Option<&Store>, _: Option<&Store>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { key: 1 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 2 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 3 }, Store::key);
    ///
    /// let mut ge = tree.split_off_lower_bound_by_key(&2, Store::key);
    /// assert_eq!(tree.collect(|_| ()).len(), 1);
    /// assert_eq!(ge.collect(|_| ()).len(), 2);
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
    /// struct Store { key: u32 }
    /// impl Store {
    ///    fn key(&self) -> u32 { self.key }
    /// }
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Store = Store;
    ///     fn update(_: &mut Store, _: Option<&Store>, _: Option<&Store>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { key: 1 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 2 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 3 }, Store::key);
    ///
    /// let mut gt = tree.split_off_upper_bound_by_key(&2, Store::key);
    /// assert_eq!(tree.collect(|_| ()).len(), 2);
    /// assert_eq!(gt.collect(|_| ()).len(), 1);
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
    ///     type Store = i32;
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
    /// assert_eq!(tree1.collect(|_| ()).len(), 3);
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
    ///     type Store = i32;
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
    /// assert_eq!(tree.collect(|_| ()).len(), 2);
    /// ```
    pub fn insert(&mut self, store: T, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2) {
        let (left, right) = split2(self.root.take(), f);
        let center = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(store)))) };
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
    /// struct Store { value: i32, size: usize }
    /// impl Store {
    ///     fn size(&self) -> usize { self.size }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_by_index(Store { value: 1, size: 1 }, 0, Store::size);
    /// tree.insert_by_index(Store { value: 3, size: 1 }, 1, Store::size);
    /// assert_eq!(tree.len(Store::size), 2);
    /// ```
    pub fn insert_by_index(
        &mut self,
        store: T,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) {
        self.insert(store, |_center, left, _right| {
            Navi2::by_index(&mut index, &mut size, left)
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
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    /// tree.insert_lower_bound_by_key(7, |v| *v);
    /// assert_eq!(tree.collect(|_| ()).len(), 3);
    /// ```
    pub fn insert_lower_bound_by_key<K: Ord>(&mut self, store: T, mut f: impl FnMut(&T) -> K) {
        let probe = f(&store);
        self.insert(store, |center, _left, _right| {
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
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_upper_bound_by_key(5, |v| *v);
    /// tree.insert_upper_bound_by_key(3, |v| *v);
    /// tree.insert_upper_bound_by_key(5, |v| *v);
    /// assert_eq!(tree.collect(|_| ()).len(), 3);
    /// ```
    pub fn insert_upper_bound_by_key<K: Ord>(&mut self, store: T, mut f: impl FnMut(&T) -> K) {
        let probe = f(&store);
        self.insert(store, |center, _left, _right| {
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
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_front(5);
    /// tree.push_front(2);
    ///
    /// assert_eq!(tree.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, store: T) {
        self.insert(store, |_, _, _| Navi2::GoDownLeft);
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
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_back(5);
    /// tree.push_back(7);
    ///
    /// assert_eq!(tree.back(), Some(&7));
    /// ```
    pub fn push_back(&mut self, store: T) {
        self.insert(store, |_, _, _| Navi2::GoDownRight);
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
    ///     type Store = i32;
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
    /// assert_eq!(tree.collect(|_| ()).len(), 1);
    /// ```
    pub fn remove(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3) -> Option<T> {
        unsafe {
            match split3(self.root.take(), f) {
                Split3Result::Success(left, center, right) => {
                    let store = Box::from_raw(center.as_ptr()).store;
                    self.root = merge2(left, right);
                    Some(store)
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
    /// struct Store { value: i32, size: usize }
    /// impl Store {
    ///     fn value(&self) -> i32 { self.value }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 1, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 2, size: 1 }, Store::value);
    ///
    /// let removed = tree.remove_by_index(0, |v| v.size);
    /// assert_eq!(removed.as_ref().map(Store::value), Some(1));
    /// ```
    pub fn remove_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<T> {
        self.remove(|_center, left, _right| Navi3::by_index(&mut index, &mut size, left))
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
    ///     type Store = i32;
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
    ///     type Store = i32;
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
    ///     type Store = i32;
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
    ///     type Store = i32;
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
                    Some(&(*center.as_ptr()).store)
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
    /// struct Store { value: i32, size: usize }
    /// impl Store {
    ///     fn value(&self) -> i32 { self.value }
    ///     fn size(&self) -> usize { self.size }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left { center.size += left.size; }
    ///         if let Some(right) = right { center.size += right.size; }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 1, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 2, size: 1 }, Store::value);
    ///
    /// let found = tree.get_by_index(1, Store::size);
    /// assert_eq!(found.map(Store::value), Some(2));
    /// ```
    pub fn get_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<&T> {
        self.get(|_center, left, _right| Navi3::by_index(&mut index, &mut size, left))
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
    /// struct Store { key: u32 }
    /// impl Store {
    ///     fn key(&self) -> u32 { self.key }
    /// }
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Store = Store;
    ///     fn update(_: &mut Store, _: Option<&Store>, _: Option<&Store>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { key: 5 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 3 }, Store::key);
    ///
    /// let found = tree.get_by_key(&3, Store::key);
    /// assert_eq!(found.map(Store::key), Some(3));
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
    ///     type Store = i32;
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
    ///     type Store = i32;
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

    /// Collects all elements from the tree into a vector, applying a transformation.
    ///
    /// This method performs an in-order traversal of the tree, collecting each element
    /// after applying the provided transformation function. The result is sorted in the
    /// tree's natural order (left-to-right in-order traversal).
    ///
    /// # Arguments
    ///
    /// * `f` - A closure that transforms each element value into the output type
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Op};
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    ///
    /// let values = tree.collect(|v| *v);
    /// assert_eq!(values, vec![1, 2, 3]);
    /// ```
    pub fn collect<U>(&self, f: impl Fn(&T) -> U) -> Vec<U> {
        let mut out = vec![];
        visit::<T, O>(self.root, &mut |store| out.push(f(store)));
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
/// struct Store {
///     value: i32,
///     sum: i32,
/// }
///
/// enum MyOp {}
/// impl Op for MyOp {
///     type Store = Store;
///     fn update(root: &mut Store, left: Option<&Store>, right: Option<&Store>) {
///         root.sum = root.value;
///         if let Some(l) = left { root.sum += l.sum; }
///         if let Some(r) = right { root.sum += r.sum; }
///     }
/// }
///
/// let mut tree = Tree::<MyOp>::new();
/// tree.insert(Store { value: 5, sum: 5 }, |_, _, _| Navi2::GoDownRight);
/// tree.insert(Store { value: 3, sum: 3 }, |_, _, _| Navi2::GoDownRight);
/// assert_eq!(tree.fold().unwrap().sum, 8);
/// ```
pub trait Op: Sized {
    type Store;
    fn update(center: &mut Self::Store, left: Option<&Self::Store>, right: Option<&Self::Store>);
}
