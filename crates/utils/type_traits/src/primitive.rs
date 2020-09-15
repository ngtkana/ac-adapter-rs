use super::{One, Zero};

macro_rules! int {
    ($($T:ty,)*) => {
        $(
            impl Zero for $T {
                #[inline]
                fn zero() -> $T {
                    0
                }
            }
            impl One for $T {
                #[inline]
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
