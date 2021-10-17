use std::fmt::Display;

pub fn space<I, T>(iter: I) -> String
where
    T: Display,
    I: IntoIterator<Item = T>,
{
    let mut string = String::new();
    let mut iter = iter.into_iter();
    if let Some(head) = iter.next() {
        string.push_str(&format!("{}", head));
        for elm in iter {
            string.push_str(&format!(" {}", elm));
        }
    }
    string
}

#[cfg(test)]
mod tests {
    use {super::space, test_case::test_case};

    #[test_case(&Vec::new() => "")]
    #[test_case(&[42] => "42")]
    #[test_case(&[42, 43] => "42 43")]
    #[test_case(&[42, 43, 44] => "42 43 44")]
    fn test_space(slice: &[i32]) -> String {
        space(slice.iter())
    }
}
