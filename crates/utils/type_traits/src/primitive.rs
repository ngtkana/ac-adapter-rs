use super::{One, Zero};

macro_rules! int {
    ($($T:ty,)*) => {
        $(
            impl Zero for $T {
                fn zero() -> $T {
                    0
                }
                fn times(self, n: u64) -> $T {
                    self * n as $T
                }
                fn from_u64(n: u64) -> $T {
                    n as $T
                }
            }
            impl One for $T {
                fn one() -> $T {
                    1
                }
            }
        )*
    }
}

int! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}
