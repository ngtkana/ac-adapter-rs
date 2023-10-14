#![warn(missing_docs)]
//! Containers for storing data in a red-black tree.

/// A red-black tree.
mod tree;

#[allow(dead_code)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

/// A node in a red-black tree.
trait Listen<T>: Sized {
    /// The type of the cache.
    type Cache;
    /// Callback for when the node is accessed down the tree.
    fn push(node: &mut Node<T, Self>);
    /// Callback for when the node is accessed up the tree.
    fn update(node: &mut Node<T, Self>);
}

#[allow(dead_code)]
/// A node in a red-black tree.
struct Node<T, L: Listen<T>> {
    pub value: T,
    pub left: *mut Node<T, L>,
    pub right: *mut Node<T, L>,
    pub parent: *mut Node<T, L>,
    pub color: Color,
    pub cache: L::Cache,
}

#[allow(dead_code)]
impl<T, L: Listen<T>> Node<T, L> {
    fn push(&mut self) { L::push(self); }

    fn update(&mut self) { L::update(self); }
}

/// A no-op callback.
pub struct Len;
impl<T> Listen<T> for Len {
    type Cache = usize;

    fn push(_node: &mut Node<T, Self>) {}

    fn update(node: &mut Node<T, Self>) {
        unsafe {
            node.cache = 1
                + node.left.as_ref().map_or(0, |n| n.cache)
                + node.right.as_ref().map_or(0, |n| n.cache);
        }
    }
}

/// A list based on a red-black tree.
pub struct Rblist<T>(tree::Tree<T, Len>);
