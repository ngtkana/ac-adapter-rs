use crate::Query;

/// 値で回答します。
pub trait Solve<Q: Query> {
    #[allow(missing_docs)]
    fn solve(&self, param: Q::Param) -> Q::Output;
}
/// 自分を書き換えて、値も返します。
pub trait SolveMut<Q: Query> {
    #[allow(missing_docs)]
    fn solve_mut(&mut self, param: Q::Param) -> Q::Output;
}
/// 自分を書き換えます。
pub trait Mutate<Q: Query<Output = ()>> {
    #[allow(missing_docs)]
    fn mutate(&mut self, param: Q::Param);
}
/// 結果が正しければ `true`, 誤っていれば `false` を返します。
pub trait Judge<Q: Query> {
    fn judge(&self, param: Q::Param, output: Q::Output) -> bool;
}

impl<Q: Query, T: Solve<Q>> SolveMut<Q> for T {
    fn solve_mut(&mut self, param: Q::Param) -> Q::Output {
        self.solve(param)
    }
}
