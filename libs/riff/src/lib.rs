//! Future and otherworldly Rust features.

mod bitmask_iterators;
mod bitmask_operations;
mod change_min_max;
mod lazy_lock;
mod numeric_traits;
mod pop_if;
mod slice_accum;
mod slice_binary_search;
mod slice_chunks;

pub use bitmask_iterators::bitmask_combinations;
pub use bitmask_iterators::bitmask_subsets;
pub use bitmask_operations::i2powm1;
pub use change_min_max::ChangeMinMax;
pub use lazy_lock::LazyLock;
pub use numeric_traits::Unsigned;
pub use pop_if::PopIf;
pub use slice_accum::SliceAccum;
pub use slice_binary_search::SliceBinarySearch;
pub use slice_chunks::SliceChunks;
