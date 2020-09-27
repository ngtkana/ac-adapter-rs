use crate::Query;
use std::marker::PhantomData;

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
    const NAME: &'static str = "lower bound_by_key";
}
