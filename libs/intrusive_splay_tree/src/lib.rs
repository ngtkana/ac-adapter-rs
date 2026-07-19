//! Intrusive spaly tree

use std::{borrow::Borrow, cmp::Ordering, ptr::NonNull};

type NN<U> = NonNull<Node<U>>;
type ONN<U> = Option<NonNull<Node<U>>>;

/// An enum used in a binary search that never stops, indicating whether to move left or right. This is used in [`insert`](Tree::insert).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Navi2 {
    GoDownLeft,
    GoDownRight,
}

/// An enum indicating whether to proceed left or right during a binary search that might terminate early. This is used in [`remove`](Tree::remove).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Navi3 {
    GoDownLeft,
    Found,
    GoDownRight,
}

/// A splay tree.
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Node, Update, Tree, Navi2, Navi3};
/// use std::cmp::Ordering;
///
/// // Boilerplates.
/// struct Value {
///     value: u32,
///     sum: u32,
/// }
///
/// enum U {}
/// impl Update for U {
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
pub struct Tree<U: Update> {
    root: ONN<U>,
}

impl<U: Update> Default for Tree<U> {
    fn default() -> Self {
        Self { root: None }
    }
}

impl<U: Update> Drop for Tree<U> {
    fn drop(&mut self) {
        free_subtree(self.root);
    }
}

impl<T, U: Update<Value = T>> Tree<U> {
    /// Creates a new empty tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Update};
    ///
    /// enum U {}
    /// impl Update for U {
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

    /// Returns a reference to the aggregated value of the entire tree, computed via [`Update::update`], if the tree is non-empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Update, Navi2};
    ///
    /// struct Value {
    ///     val: i32,
    ///     sum: i32,
    /// }
    ///
    /// enum U {}
    /// impl Update for U {
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

    pub fn split_off(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2) -> Self {
        let (left, right) = split2(self.root.take(), f);
        self.root = left;
        Self { root: right }
    }

    pub fn split_off_lower_bound_by_key<K, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Self
    where
        K: Borrow<Q>,
    {
        self.split_off(
            |center, _left, _right| match probe.cmp(f(center).borrow()) {
                Ordering::Less | Ordering::Equal => Navi2::GoDownLeft,
                Ordering::Greater => Navi2::GoDownRight,
            },
        )
    }

    pub fn split_off_upper_bound_by_key<K, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Self
    where
        K: Borrow<Q>,
    {
        self.split_off(
            |center, _left, _right| match probe.cmp(f(center).borrow()) {
                Ordering::Less => Navi2::GoDownLeft,
                Ordering::Equal | Ordering::Greater => Navi2::GoDownRight,
            },
        )
    }

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
    /// use intrusive_splay_tree::{Tree, Update, Navi2};
    ///
    /// enum U {}
    /// impl Update for U {
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

    /// Inserts a new node by extracting a key from the value and using standard comparison.
    ///
    /// This is a convenience wrapper around [`insert`](Self::insert) that compares the extracted key with the current node's key using `Ord`.
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Update};
    ///
    /// enum U {}
    /// impl Update for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_by_key(5, |v| *v);
    /// tree.insert_by_key(3, |v| *v);
    /// tree.insert_by_key(7, |v| *v);
    /// assert_eq!(tree.collect().len(), 3);
    /// ```
    pub fn insert_by_key<K: Ord>(&mut self, node_value: T, mut f: impl FnMut(&T) -> K) {
        let probe = f(&node_value);
        self.insert(node_value, |center, _left, _right| {
            match probe.cmp(&f(&center)) {
                Ordering::Less | Ordering::Equal => Navi2::GoDownLeft,
                Ordering::Greater => Navi2::GoDownRight,
            }
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
    /// use intrusive_splay_tree::{Tree, Update, Navi3};
    ///
    /// enum U {}
    /// impl Update for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_by_key(5, |v| *v);
    /// tree.insert_by_key(3, |v| *v);
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

    /// Removes a node by extracting a key from each node and comparing with a probe.
    ///
    /// This is a convenience wrapper around [`remove`](Self::remove) that extracts a key from each node's value
    /// and compares it with the probe using `Ord`. The probe type `Q` need not match the key type `K` exactly,
    /// as long as `K` implements `Borrow<Q>` (enabling `String` nodes to be searched by `&str`, for example).
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Update};
    ///
    /// enum U {}
    /// impl Update for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_by_key(5, |v| *v);
    /// tree.insert_by_key(3, |v| *v);
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
        self.remove(
            |center, _left, _right| match probe.cmp(f(&center).borrow()) {
                Ordering::Less => Navi3::GoDownLeft,
                Ordering::Equal => Navi3::Found,
                Ordering::Greater => Navi3::GoDownRight,
            },
        )
    }

    // TODO: change to &self, using Cell
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

    pub fn get_by_key<K: Ord, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<&T>
    where
        K: Borrow<Q>,
    {
        self.get(
            |center, _left, _right| match probe.cmp(f(&center).borrow()) {
                Ordering::Less => Navi3::GoDownLeft,
                Ordering::Equal => Navi3::Found,
                Ordering::Greater => Navi3::GoDownRight,
            },
        )
    }

    /// Returns a vector of references to all node values in the tree, in sorted order (in-order traversal).
    ///
    /// # Examples
    ///
    /// ```
    /// use intrusive_splay_tree::{Tree, Update};
    ///
    /// enum U {}
    /// impl Update for U {
    ///     type Value = i32;
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<U>::new();
    /// tree.insert_by_key(3, |v| *v);
    /// tree.insert_by_key(1, |v| *v);
    /// tree.insert_by_key(2, |v| *v);
    ///
    /// let values: Vec<_> = tree.collect().into_iter().copied().collect();
    /// assert_eq!(values, vec![1, 2, 3]);
    /// ```
    pub fn collect(&self) -> Vec<&T> {
        pub fn collect<'a, U: Update>(root: ONN<U>, out: &'a mut Vec<&U::Value>) {
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
/// The [`update`](Update::update) method is called whenever a node is inserted, deleted, or rotated.
/// It receives the node's value and optional references to the left and right children's aggregated values,
/// allowing you to maintain tree-wide aggregates (e.g., sum, min, max) in O(log n) time.
///
/// # Examples
///
/// ```
/// use intrusive_splay_tree::{Tree, Update, Navi2};
///
/// struct Value {
///     val: i32,
///     sum: i32,
/// }
///
/// enum MyUpdate {}
/// impl Update for MyUpdate {
///     type Value = Value;
///     fn update(root: &mut Value, left: Option<&Value>, right: Option<&Value>) {
///         root.sum = root.val;
///         if let Some(l) = left { root.sum += l.sum; }
///         if let Some(r) = right { root.sum += r.sum; }
///     }
/// }
///
/// let mut tree = Tree::<MyUpdate>::new();
/// tree.insert(Value { val: 5, sum: 5 }, |_, _, _| Navi2::GoDownRight);
/// tree.insert(Value { val: 3, sum: 3 }, |_, _, _| Navi2::GoDownRight);
/// assert_eq!(tree.fold_all().unwrap().sum, 8);
/// ```
pub trait Update: Sized {
    type Value;
    fn update(center: &mut Self::Value, left: Option<&Self::Value>, right: Option<&Self::Value>);
}

/// A node of [`Tree`]. We made this public for the time being, expecting the need for the size of the left subtree when performing binary searches during [`insert`](Tree::insert) or [`remove`](Tree::remove) operations.
pub struct Node<U: Update> {
    node_value: U::Value,
    left: ONN<U>,
    right: ONN<U>,
    parent: ONN<U>,
}
impl<U: Update> Node<U> {
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

fn merge2<U: Update>(left: ONN<U>, right: ONN<U>) -> ONN<U> {
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

fn merge3<U: Update>(left: ONN<U>, center: NN<U>, right: ONN<U>) -> NN<U> {
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

fn split2<T, U: Update<Value = T>>(
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

enum Split3Result<U: Update> {
    Success(ONN<U>, NN<U>, ONN<U>),
    Failure(ONN<U>),
}

fn split3<T, U: Update<Value = T>>(
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

fn splay<U: Update>(x: NN<U>) -> NN<U> {
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
fn rotate_left<U: Update>(x: NN<U>) -> NN<U> {
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
fn rotate_right<U: Update>(x: NN<U>) -> NN<U> {
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
fn free_subtree<U: Update>(root: ONN<U>) {
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
fn find_and_splay<T, U: Update<Value = T>>(
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
