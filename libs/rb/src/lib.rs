#![warn(missing_docs)]
//! Containers for storing data in a red-black tree.

/// The core implementation of a red-black tree.
mod tree;

/// A list based on a red-black tree.
mod list;

/// A list based on a red-black tree.
pub use list::List;

/// A trait for algebraic operations.
pub trait Op {
    /// The type of the value stored in the leaf nodes.
    type Value;
    /// The type of the lazy action stored in the internal nodes.
    type Lazy: PartialEq;

    /// Multiply two `Value`s.
    fn mul(_: &Self::Value, _: &Self::Value) -> Self::Value;

    /// Apply a `Lazy` action to a `Value`.
    fn apply(_: &mut Self::Value, _: &Self::Lazy);

    /// Compose two `Lazy` actions.
    fn compose(_: &mut Self::Lazy, _: &Self::Lazy);

    /// The identity of `Lazy` actions.
    fn identity() -> Self::Lazy;

    /// Check if a `Lazy` action is the identity.
    fn is_identity(lazy: &Self::Lazy) -> bool { *lazy == Self::identity() }

    /// Set a `Lazy` action to the identity.
    fn swap_with_identity(lazy: &mut Self::Lazy) -> Self::Lazy {
        let mut tmp = Self::identity();
        std::mem::swap(lazy, &mut tmp);
        tmp
    }
}
