//! Containers for storing data in a red-black tree.

/// Balancing algorithm of red-black trees.
mod balance;

/// Multimap based on red-black trees.
mod map;

mod seq;

pub use map::Multimap;
pub use map::MultimapOp;
pub use map::MultimapSeg;
pub use map::Multiset;
