pub trait Pow {
    fn is_nonzero(&self) -> bool;
    fn is_odd(&self) -> bool;
    fn div2(&mut self);
}

pub fn binary<T>(mut a: T, mut b: impl Pow, init: T, f: impl Fn(&T, &T) -> T) -> T {
    let mut ans = init;
    while b.is_nonzero() {
        if b.is_odd() {
            ans = f(&ans, &a);
        }
        a = f(&a, &a);
        b.div2();
    }
    ans
}

macro_rules! impl_pow {
    ($($T:ty),* $(,)?) => {$(
        impl Pow for $T {
            fn is_nonzero(&self) -> bool {
                *self != 0
            }
            fn is_odd(&self) -> bool {
                self.rem_euclid(2) == 1
            }
            fn div2(&mut self) {
                *self = self.div_euclid(2);
            }
        }
    )*}
}

impl_pow! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

#[cfg(test)]
mod tests {
    use {super::binary, test_case::test_case};

    #[test_case(0 => "".to_owned())]
    #[test_case(1 => "abc".to_owned())]
    #[test_case(2 => "abcabc".to_owned())]
    #[test_case(3 => "abcabcabc".to_owned())]
    #[test_case(4 => "abcabcabcabc".to_owned())]
    #[test_case(5 => "abcabcabcabcabc".to_owned())]
    fn test_cat(n: i32) -> String {
        binary("abc".to_owned(), n, String::new(), |s, t| {
            s.chars().chain(t.chars()).collect::<String>()
        })
    }
}
