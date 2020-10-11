pub mod arith;
pub mod ord;
pub mod prim;

use std::fmt::Debug;

pub trait Element: Debug + Clone + PartialEq {}
impl<T: Debug + Clone + PartialEq> Element for T {}

pub trait Assoc: std::fmt::Debug {
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
pub trait Action: Assoc {
    type Point: Element;
    fn act(a: Self::Value, x: Self::Point) -> Self::Point;
    fn act_assign(a: Self::Value, x: &mut Self::Point) {
        *x = Self::act(a, x.clone());
    }
}

// Option
impl<T: Assoc> Assoc for Option<T> {
    type Value = Option<T::Value>;
    fn op(lhs: Option<T::Value>, rhs: Option<T::Value>) -> Self::Value {
        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => Some(T::op(lhs, rhs)),
            (x, None) => x,
            (None, y) => y,
        }
    }
}
impl<T: Assoc> Identity for Option<T> {
    fn identity() -> Option<T::Value> {
        None
    }
}
impl<A: Action> Action for Option<A> {
    type Point = A::Point;
    fn act(a: Option<A::Value>, x: A::Point) -> A::Point {
        if let Some(a) = a {
            A::act(a, x)
        } else {
            x
        }
    }
}

// Tuple of two types
impl<T: Assoc, U: Assoc> Assoc for (T, U) {
    type Value = (T::Value, U::Value);
    fn op(lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        (T::op(lhs.0, rhs.0), U::op(lhs.1, rhs.1))
    }
}
impl<T: Identity, U: Identity> Identity for (T, U) {
    fn identity() -> <Self as Assoc>::Value {
        (T::identity(), U::identity())
    }
}
