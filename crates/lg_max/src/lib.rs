//! lg library to quiet `{integer}::MAX` down to `"*"`.
use std::fmt::Debug;

/// A Wrapper to quiet `{integer}::MAX` down to `"*"`.
pub struct QuietMax<T>(pub T);
impl<T: Debug> Debug for QuietMax<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            format!("{:?}", self.0)
                .replace("18446744073709551615", "*") // u64
                .replace("9223372036854775807", "*") // i64
                .replace("-9223372036854775808", "*") // i64
                .replace("4294967295", "*") // i32
                .replace("-4294967296", "*") // i32
                .replace("2147483647", "*") // i32
                .replace("None", "*")
                .replace("Some", "")
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn to_string<T: Debug>(t: T) -> String {
        format!("{:?}", QuietMax(t))
    }

    #[test]
    fn test() {
        assert_eq!(&to_string(std::usize::MAX), "*");
        assert_eq!(&to_string(std::isize::MAX), "*");
        assert_eq!(&to_string(std::u64::MAX), "*");
        assert_eq!(&to_string(std::i64::MAX), "*");
        assert_eq!(&to_string(std::u32::MAX), "*");
        assert_eq!(&to_string(std::i32::MAX), "*");
    }
}
