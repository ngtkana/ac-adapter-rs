use super::{
    binary::{Add, Mul},
    Commut, One, OpN, Zero,
};

macro_rules! zero {
    (int) => {
        0
    };
    (float) => {
        0.
    };
}
macro_rules! one {
    (int) => {
        1
    };
    (float) => {
        1.
    };
}
macro_rules! num {
    (@kind $kind:ident @type $T:ty) => {
        impl Zero for $T {
            fn zero() -> $T {
                zero!($kind)
            }
        }
        impl One for $T {
            fn one() -> $T {
                one!($kind)
            }
        }
        impl Commut for Add<$T> {}
        impl OpN for Add<$T> {
            fn op_n(self, n: u64) -> Self {
                Add(self.0 * n as $T)
            }
        }
        impl Commut for Mul<$T> {}
    };
}

macro_rules! int {
    ($($T:ty,)*) => {
        $( num! { @kind int @type $T } )*
    };
}

macro_rules! float {
    ($($T:ty,)*) => {
        $( num! { @kind float @type $T } )*
    };
}

int! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

float! {
    f32, f64,
}
