use super::{
    binary::{Add, Mul},
    Commut, MaxValue, MinValue, One, OpN, Zero,
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
macro_rules! impl_zero {
    (@kind $kind:ident @type $T:ident) => {
        impl Zero for $T {
            fn zero() -> $T {
                zero!($kind)
            }
        }
    };
}
macro_rules! impl_one {
    (@kind $kind:ident @type $T:ident) => {
        impl One for $T {
            fn one() -> $T {
                one!($kind)
            }
        }
    };
}
macro_rules! impl_min_value {
    ($T:ident) => {
        impl MinValue for $T {
            fn min_value() -> Self {
                std::$T::MIN
            }
        }
    };
}
macro_rules! impl_max_value {
    ($T:ident) => {
        impl MaxValue for $T {
            fn max_value() -> Self {
                std::$T::MAX
            }
        }
    };
}
macro_rules! impl_commut_add {
    ($T:ident) => {
        impl Commut for Add<$T> {}
    };
}
macro_rules! impl_commut_mul {
    ($T:ident) => {
        impl Commut for Mul<$T> {}
    };
}
macro_rules! impl_op_n_add {
    ($T:ident) => {
        impl OpN for Add<$T> {
            fn op_n(self, n: u64) -> Self {
                Add(self.0 * n as $T)
            }
        }
    };
}
macro_rules! impl_op_n_mul {
    (@kind int @type $T:ident) => {
        impl OpN for Mul<$T> {
            fn op_n(self, n: u64) -> Self {
                Mul(self.0.pow(n as u32))
            }
        }
    };
    (@kind float @type $T:ident) => {
        impl OpN for Mul<$T> {
            fn op_n(self, n: u64) -> Self {
                Mul(self.0.powi(n as i32))
            }
        }
    };
}

macro_rules! int {
    ($T:ident, $($rest:ident,)*) => {
        impl_zero! { @kind int @type $T }
        impl_one! { @kind int @type $T }
        impl_min_value! { $T }
        impl_max_value! { $T }
        impl_commut_add! { $T }
        impl_commut_mul! { $T }
        impl_op_n_add! { $T }
        impl_op_n_mul! { @kind int @type $T }
        int! { $($rest,)* }
    };
    () => ()
}

macro_rules! float {
    ($T:ident, $($rest:ident,)*) => {
        impl_zero! { @kind float @type $T }
        impl_one! { @kind float @type $T }
        impl_commut_add! { $T }
        impl_commut_mul! { $T }
        impl_op_n_add! { $T }
        impl_op_n_mul! { @kind float @type $T }
        float! { $($rest,)* }
    };
    () => ()
}

int! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

float! {
    f32, f64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_impl::assert_impl;

    #[test]
    fn test_impl() {
        assert_impl!(Zero: u32, f32);
        assert_impl!(One: u32, f32);
        assert_impl!(MinValue: u32);
        assert_impl!(MaxValue: u32);
        assert_impl!(!MinValue: f32);
        assert_impl!(!MaxValue: f32);
        assert_impl!(Commut: Add<u32>, Add<f32>);
        assert_impl!(Commut: Mul<u32>, Mul<f32>);
        assert_impl!(OpN: Add<u32>, Add<f32>);
        assert_impl!(OpN: Mul<u32>, Mul<f32>);
    }
}
