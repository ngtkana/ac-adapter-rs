//! ordered_float::NotNan の劣化版です。
//!
use std::cmp::{Ord, Ordering};
pub trait Float: PartialEq + PartialOrd {
    fn float_is_nan(&self) -> bool;
}
impl Float for f64 {
    fn float_is_nan(&self) -> bool {
        self.is_nan()
    }
}

#[derive(PartialEq, Debug, Default, Clone, Copy)]
pub struct NotNaN<T: Float>(T);
impl<T: Float> NotNaN<T> {
    pub fn from_float(value: T) -> Self {
        match value {
            ref value if value.float_is_nan() => panic!("これはなんですか？"),
            value => NotNaN(value),
        }
    }

    pub fn into_inner(self) -> T {
        self.0
    }
}
impl<T: Float> Eq for NotNaN<T> {}
impl<T: Float> Ord for NotNaN<T> {
    fn cmp(&self, other: &NotNaN<T>) -> Ordering {
        match self.partial_cmp(&other) {
            Some(ord) => ord,
            None => unreachable!(),
        }
    }
}
impl<T: Float> PartialOrd for NotNaN<T> {
    fn partial_cmp(&self, other: &NotNaN<T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
