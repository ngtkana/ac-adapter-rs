pub mod arith;
pub mod ord;
pub mod prim;

use std::fmt::Debug;

pub trait Element: Debug + Clone + PartialEq {}
impl<T: Debug + Clone + PartialEq> Element for T {}

pub trait Assoc {
    type Value: Element;
    fn op(lhs: Self::Value, rhs: Self::Value) -> Self::Value;
    fn op_left(lhs: &mut Self::Value, rhs: Self::Value) {
        *lhs = Self::op(lhs.clone(), rhs);
    }
    fn op_right(lhs: Self::Value, rhs: &mut Self::Value) {
        *rhs = Self::op(lhs, rhs.clone());
    }
}
pub trait Identity: Assoc {
    fn identity() -> Self::Value;
}
pub trait Action {
    type Operator: Element;
    type Point: Element;
    fn op(operator: Self::Operator, point: Self::Point) -> Self::Point;
    fn op_assign(operator: Self::Operator, point: &mut Self::Point) {
        *point = Self::op(operator, point.clone())
    }
}
