//! Containers for storing data in a red-black tree.

/// Balancing algorithm of red-black trees.
mod balance;

/// Multimap based on red-black trees.
mod map;

pub use map::Multimap;
pub use map::Multiset;
pub use map::Segmap;
pub use map::SegmapOp;
