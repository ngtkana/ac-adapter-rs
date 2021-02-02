use std::fmt::{self, Debug, Display, Formatter};

/// Formats `&[bool]` bitwise to `0` or `1`.
///
/// # Example
///
/// ```
/// use dbg::BitSlice;
/// assert_eq!(format!("{}", BitSlice(&[false, true, false])), "010".to_owned());
/// ```
pub struct BitSlice<'a>(pub &'a [bool]);

impl<'a> Display for BitSlice<'a> {
    fn fmt(&self, w: &mut Formatter) -> fmt::Result {
        write!(
            w,
            "{}",
            self.0
                .iter()
                .map(|&b| if b { '1' } else { '0' })
                .collect::<String>()
        )
    }
}
impl<'a> Debug for BitSlice<'a> {
    fn fmt(&self, w: &mut Formatter) -> fmt::Result {
        write!(w, "{}", self)
    }
}

#[cfg(test)]
mod tests {
    use {super::BitSlice, test_case::test_case};

    #[test_case(&[] => "")]
    #[test_case(&[false] => "0")]
    #[test_case(&[true] => "1")]
    #[test_case(&[false, false] => "00")]
    #[test_case(&[false, true] => "01")]
    #[test_case(&[true, false] => "10")]
    #[test_case(&[true, true] => "11")]
    fn test_bitest(slice: &[bool]) -> String {
        format!("{}", BitSlice(slice))
    }
}
