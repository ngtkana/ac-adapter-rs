#![warn(missing_docs)]
//! Containers for storing data in a red-black tree.

use std::ops;
use std::ptr;
use std::ptr::NonNull;

/// The core implementation of a red-black tree.
mod tree;

/// A color of a node in a red-black tree.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Color {
    Red,
    Black,
}

/// A callback for a node in a red-black tree.
trait Callback: Sized {
    /// The data stored in the node.
    type Data;
    /// The callback function called when it goes down the tree.
    fn push(node: Ptr<Self>);
    /// The callback function called when it goes up the tree.
    fn update(node: Ptr<Self>);
}

/// A trait for getting the length of a node in a red-black tree.
trait Len {
    fn len(&self) -> usize;
}

/// A node in a red-black tree.
#[allow(dead_code)]
struct Node<C: Callback> {
    data: C::Data,
    left: Option<Ptr<C>>,
    right: Option<Ptr<C>>,
    parent: Option<Ptr<C>>,
    color: Color,
}
/// Non-dangling pointer to a node in a red-black tree.
#[allow(dead_code)]
struct Ptr<C: Callback>(NonNull<Node<C>>);
#[allow(dead_code)]
impl<C: Callback> Ptr<C> {
    /// Create a new isolated red [`Ptr`] from a [`Callback::Data`].
    pub fn new(data: C::Data) -> Self {
        Self(
            NonNull::new(Box::into_raw(Box::new(Node {
                data,
                left: None,
                right: None,
                parent: None,
                color: Color::Red,
            })))
            .unwrap(),
        )
    }

    /// Give the ownership of the node to the caller.
    pub fn into_box(self) -> Box<Node<C>> { unsafe { Box::from_raw(self.0.as_ptr()) } }

    /// Get the node as a reference.
    pub fn as_ref(&self) -> &Node<C> { unsafe { self.0.as_ref() } }

    /// Get the node as a mutable reference.
    pub fn as_mut(&mut self) -> &mut Node<C> { unsafe { self.0.as_mut() } }

    /// Update the node.
    pub fn update(&mut self) { C::update(*self); }

    /// Returns `true` if the node is isolated.
    pub fn is_isolated_and_red(self) -> bool {
        self.as_ref().left.is_none()
            && self.as_ref().right.is_none()
            && self.as_ref().parent.is_none()
            && self.as_ref().color == Color::Red
    }

    /// Change the node to an isolated red node.
    pub fn isolate_and_red(&mut self) {
        self.as_mut().left = None;
        self.as_mut().right = None;
        self.as_mut().parent = None;
        self.as_mut().color = Color::Red;
    }
}
impl<C: Callback> Clone for Ptr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for Ptr<C> {}
impl<C: Callback> ops::Deref for Ptr<C> {
    type Target = Node<C>;

    fn deref(&self) -> &Self::Target { self.as_ref() }
}
impl<C: Callback> ops::DerefMut for Ptr<C> {
    fn deref_mut(&mut self) -> &mut Self::Target { self.as_mut() }
}
impl<C: Callback> PartialEq for Ptr<C> {
    fn eq(&self, other: &Self) -> bool { ptr::eq(self.as_ref(), other.as_ref()) }
}
impl<C: Callback> Eq for Ptr<C> {}

/// Get the color of a node.
fn color<C: Callback>(p: Option<Ptr<C>>) -> Color { p.map_or(Color::Black, |p| p.as_ref().color) }

/// Get the pointer to a node.
fn as_ptr<C: Callback>(p: Option<Ptr<C>>) -> *mut Node<C> {
    p.map_or(ptr::null_mut(), |p| p.0.as_ptr())
}
