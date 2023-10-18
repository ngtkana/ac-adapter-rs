use std::fmt::Display;
use std::fmt::Write;

/// スペース区切りの文字列にします。
pub fn implode_space<I>(iter: I) -> String
where
    I: IntoIterator,
    I::Item: Display,
{
    implode(iter, " ")
}

/// `separator` 区切りの文字列にします。
pub fn implode<I>(iter: I, separator: &str) -> String
where
    I: IntoIterator,
    I::Item: Display,
{
    let mut w = String::new();
    let mut iter = iter.into_iter();
    if let Some(head) = iter.next() {
        write!(&mut w, "{}", &head).unwrap();
        for elm in iter {
            write!(&mut w, "{}{}", separator, &elm).unwrap();
        }
    }
    w
}

#[cfg(test)]
mod tests {
    use super::implode_space;
    use std::fmt::Display;
    use test_case::test_case;

    #[test_case(&Vec::new() => "")]
    #[test_case(&[42] => "42")]
    #[test_case(&[42, 43] => "42 43")]
    #[test_case(&[42, 43, 44] => "42 43 44")]
    fn test_space(slice: &[i32]) -> String { implode_space(slice.iter()) }

    struct MaybeEmpty(Option<i32>);
    impl Display for MaybeEmpty {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if let Some(x) = self.0 {
                write!(f, "{}", x)?;
            }
            Ok(())
        }
    }
    #[test_case(&Vec::new() => "")]
    #[test_case(&[MaybeEmpty(None)] => "")]
    #[test_case(&[MaybeEmpty(None), MaybeEmpty(None)] => " ")]
    #[test_case(&[MaybeEmpty(Some(42)), MaybeEmpty(None)] => "42 ")]
    #[test_case(&[MaybeEmpty(None), MaybeEmpty(Some(42))] => " 42")]
    fn test_space_maybe_empty(slice: &[MaybeEmpty]) -> String { implode_space(slice.iter()) }
}
