use super::{
    arith::{One, Zero},
    ord::{MaxValue, MinValue},
};

macro_rules! int {
    ($ty:ident, $($tt:tt)*) => {
        impl Zero for $ty {
            fn zero() -> Self {
                0
            }
        }
        impl One for $ty {
            fn one() -> Self {
                1
            }
        }
        impl MinValue for $ty {
            fn min_value() -> Self {
                std::$ty::MIN
            }
        }
        impl MaxValue for $ty {
            fn max_value() -> Self {
                std::$ty::MAX
            }
        }
        int!{$($tt)*}
    };
    () => ()
}

int! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

macro_rules! float {
    ($ty:ident, $($tt:tt)*) => {
        impl Zero for $ty {
            fn zero() -> Self {
                0.
            }
        }
        impl One for $ty {
            fn one() -> Self {
                1.
            }
        }
        float!{$($tt)*}
    };
    () => ()
}

float! {
    f32, f64,
}
