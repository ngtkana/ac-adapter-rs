//! Future and otherworldly Rust features.

mod binary_search;
mod bitmask_iterators;
mod bitmask_operations;
mod change_min_max;
mod numeric_traits;
mod pop_if;
mod slice_chunks;

pub use binary_search::BinarySearch;
pub use bitmask_iterators::bitmask_combinations;
pub use bitmask_iterators::bitmask_subsets;
pub use bitmask_operations::i2powm1;
pub use change_min_max::ChangeMinMax;
pub use numeric_traits::Unsigned;
pub use pop_if::PopIf;
pub use slice_chunks::SliceChunks;
