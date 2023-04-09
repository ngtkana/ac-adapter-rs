//! lg library to quiet `{integer}::MAX` down to `"_"`.
use std::fmt::Debug;

/// A Wrapper to quiet `{integer}::MAX` down to `"_"`.
pub struct QuietMax<T>(pub T);
impl<T: Debug> Debug for QuietMax<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            format!("{:?}", self.0)
                .replace("18446744073709551615", "_") // u64
                .replace("9223372036854775807", "_") // i64
                .replace("4294967295", "_") // i32
                .replace("2147483647", "_") // i32
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
        assert_eq!(&to_string(std::usize::MAX), "_");
        assert_eq!(&to_string(std::isize::MAX), "_");
        assert_eq!(&to_string(std::u64::MAX), "_");
        assert_eq!(&to_string(std::i64::MAX), "_");
        assert_eq!(&to_string(std::u32::MAX), "_");
        assert_eq!(&to_string(std::i32::MAX), "_");
    }
}
