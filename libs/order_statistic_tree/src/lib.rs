//! An order-statistic map and set backed by a splay tree.
//!
//! Besides the usual [`std::collections::BTreeMap`]-like API, both [`OrderStatisticMap`] and
//! [`OrderStatisticSet`] support order-statistic queries (`nth`, `binary_search`, `lower_bound`,
//! `upper_bound`) in amortized `O(log n)`.

pub mod map;
pub mod set;

pub use map::{NoOp, Op, OrderStatisticMap};
pub use set::OrderStatisticSet;
