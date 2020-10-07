use std::fmt::Debug;

pub trait Element: Debug + Clone + PartialEq {}
impl<T: Debug + Clone + PartialEq> Element for T {}

pub trait Assoc {
    type Value: Element;
    fn op(lhs: Self::Value, rhs: Self::Value) -> Self::Value;
    fn op_left(lhs: &mut Self::Value, rhs: &Self::Value) {
        *lhs = Self::op(lhs.clone(), rhs.clone());
    }
    fn op_right(lhs: &Self::Value, rhs: &mut Self::Value) {
        *rhs = Self::op(lhs.clone(), rhs.clone());
    }
}
pub trait Identity: Assoc {
    fn identity() -> Self::Value;
}
