use crate::Query;

/// 値で回答します。
pub trait SolveValue2Value<Q: Query> {
    #[allow(missing_docs)]
    fn solve_value_to_value(&self, param: Q::Param) -> Q::Output;
}
/// 参照で回答します。
pub trait SolveGet<Q: Query> {
    #[allow(missing_docs)]
    fn solve_get(&self, param: Q::Param) -> &Q::Output;
}
/// 参照で回答します。
pub trait SolveRef2Value<Q: Query> {
    #[allow(missing_docs)]
    fn solve_ref_to_value(&self, param: Q::Param) -> &Q::Output;
}

/// 自分を書き換えます。
pub trait SolveMut<Q: Query> {
    #[allow(missing_docs)]
    fn solve_mut(&mut self, param: Q::Param);
}
