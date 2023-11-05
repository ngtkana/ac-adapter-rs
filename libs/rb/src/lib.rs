//! Containers for storing data in a red-black tree.

/// Balancing algorithm of red-black trees.
mod balance;

/// Multimap based on red-black trees.
mod multimap;

pub use multimap::Multimap;
pub use multimap::MultimapOp;
pub use multimap::Multiset;
