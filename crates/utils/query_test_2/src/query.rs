use crate::{utils, Query};
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
/// `fold(start..end) <= value` なる最大の `end` を返します。
pub struct ForwardUpperBoundByKey<T, U, P>(PhantomData<(T, U, P)>);
impl<T, U, P: utils::Project<T, U>> Query for ForwardUpperBoundByKey<T, U, P> {
    type Param = (Range<usize>, U);
    type Output = usize;
    const NAME: &'static str = "forward_upper_bound_by_key";
}
