use crate::Query;
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
/// 広義単調増加な列の、ある要素以上となる最小の添字を返すクエリです。
pub struct LowerBoundByKey<T, U>(PhantomData<(T, U)>);
impl<T, U> Query for LowerBoundByKey<T, U> {
    type Param = U;
    type Output = ();
    const NAME: &'static str = "lower_bound_by_key";
}

/// 列のある範囲を単位元のある結合的な演算で畳み込みます。
pub struct Fold<T>(PhantomData<T>);
impl<T> Query for Fold<T> {
    type Param = Range<usize>;
    type Output = T;
    const NAME: &'static str = "fold";
}
/// 列のある非空な範囲がを結合的な演算で畳み込むか、空ならば `None` を返します。
pub struct FoldFirst<T>(PhantomData<T>);
impl<T> Query for FoldFirst<T> {
    type Param = Range<usize>;
    type Output = Option<T>;
    const NAME: &'static str = "fold_first";
}
