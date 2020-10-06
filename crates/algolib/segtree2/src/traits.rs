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

#[derive(Debug, Clone, PartialEq)]
pub struct InversionValue {
    pub zeros: usize,
    pub ones: usize,
    pub inversion: usize,
}
pub struct InversionMerge {}
impl Assoc for InversionMerge {
    type Value = InversionValue;
    fn op(lhs: InversionValue, rhs: InversionValue) -> InversionValue {
        InversionValue {
            zeros: lhs.zeros + rhs.zeros,
            ones: lhs.ones + rhs.ones,
            inversion: lhs.inversion + rhs.inversion + lhs.ones * rhs.zeros,
        }
    }
}
