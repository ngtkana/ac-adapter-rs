#![warn(missing_docs)]
//! Containers for storing data in a red-black tree.

/// The core implementation of a red-black tree.
mod tree;

/// A list based on a red-black tree.
mod list;

/// A trait for algebraic operations.
pub trait Op {
    /// The type of the value stored in the leaf nodes.
    type Value;
    /// The type of the value stored in the internal nodes.
    type Acc;
    /// The type of the lazy action stored in the internal nodes.
    type Lazy: PartialEq;

    /// Convert a `Value` to an `Acc`.
    fn to_acc(_: &Self::Value) -> Self::Acc;

    /// Multiply two `Acc`s.
    fn mul(_: &Self::Acc, _: &Self::Acc) -> Self::Acc;

    /// Apply a `Lazy` action to a `Value`.
    fn apply_on_value(_: &mut Self::Value, _: &Self::Lazy);

    /// Apply a `Lazy` action to an `Acc`.
    fn apply_on_acc(_: &mut Self::Acc, _: &Self::Lazy);

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
