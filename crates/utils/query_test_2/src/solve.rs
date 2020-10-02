use crate::Query;

/// 値で回答します。
pub trait Solve<Q: Query> {
    #[allow(missing_docs)]
    fn solve(&self, param: Q::Param) -> Q::Output;
}
/// 自分を書き換えます。
pub trait Mutate<Q: Query> {
    #[allow(missing_docs)]
    fn mutate(&mut self, param: Q::Param);
}
/// 結果が正しければ `true`, 誤っていれば `false` を返します。
pub trait Judge<Q: Query> {
    fn judge(&self, param: Q::Param, output: Q::Output) -> bool;
}
