//! 競技プログラミング向けの雑多な拡張トレイト・関数を寄せ集めたクレート。
//!
//! 各機能は独立していて相互依存はほぼなく、必要なものだけを個別に使える。
//!
//! # 仕様
//!
//! - ビットマスク列挙: [`bitmask_combinations`], [`bitmask_subsets`], [`i2powm1`]
//! - min/max 更新: [`ChangeMinMax`]
//! - イテレータ拡張: [`IteratorSuccessors`]
//! - 遅延初期化: [`LazyLock`]
//! - 符号なし整数の抽象化: [`Unsigned`]
//! - スライス拡張: [`SliceAccum`]（累積和）, [`SliceBinarySearch`]（二分探索）,
//!   [`SliceChunks`]（chunk 化）

mod bitmask_iterators;
mod bitmask_operations;
mod change_min_max;
mod iterator_successors;
mod lazy_lock;
mod numeric_traits;
mod slice_accum;
mod slice_binary_search;
mod slice_chunks;

pub use bitmask_iterators::bitmask_combinations;
pub use bitmask_iterators::bitmask_subsets;
pub use bitmask_operations::i2powm1;
pub use change_min_max::ChangeMinMax;
pub use iterator_successors::IteratorSuccessors;
pub use lazy_lock::LazyLock;
pub use numeric_traits::Unsigned;
pub use slice_accum::SliceAccum;
pub use slice_binary_search::SliceBinarySearch;
pub use slice_chunks::SliceChunks;
