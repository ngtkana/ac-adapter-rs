pub mod gen;
pub mod utils;

use query_test::Query;
use std::{marker::PhantomData, ops::Range};

/// 特定のインデックスの要素を取得するクエリです。
pub struct Get<T>(PhantomData<T>);
impl<T> Query for Get<T> {
    type Param = usize;
    type Output = T;
    const NAME: &'static str = "get";
}

/// 特定のインデックスの要素を置き換えるクエリです。
pub struct Set<T>(PhantomData<T>);
impl<T> Query for Set<T> {
    type Param = (usize, T);
    type Output = ();
    const NAME: &'static str = "set";
}

/// 列のある範囲を単位元のある結合的な演算で畳み込みます。
pub struct Fold<T>(PhantomData<T>);
impl<T> Query for Fold<T> {
    type Param = Range<usize>;
    type Output = T;
    const NAME: &'static str = "fold";
}

/// `f(i) = (fold(start..i) <= value)` としたときに、`range.contains(i) && f(i) && !f(i + 1)` となる `i`
/// を一つ探します。
pub struct ForwardUpperBoundByKey<T, U, P>(PhantomData<(T, U, P)>);
impl<T, U, P: utils::Project<T, U>> Query for ForwardUpperBoundByKey<T, U, P> {
    type Param = (Range<usize>, U);
    type Output = usize;
    const NAME: &'static str = "forward_upper_bound_by_key";
}

/// `f(i) = (fold(i..end) <= value)` としたときに、`range.contains(i) && f(i) && !f(i + 1)` となる `i`
/// を一つ探します。
pub struct BackwardUpperBoundByKey<T, U, P>(PhantomData<(T, U, P)>);
impl<T, U, P: utils::Project<T, U>> Query for BackwardUpperBoundByKey<T, U, P> {
    type Param = (Range<usize>, U);
    type Output = usize;
    const NAME: &'static str = "backward_upper_bound_by_key";
}

/// 範囲作用をします。
pub struct RangeApply<T>(PhantomData<T>);
impl<T> Query for RangeApply<T> {
    type Param = (Range<usize>, T);
    type Output = ();
    const NAME: &'static str = "range_apply";
}
