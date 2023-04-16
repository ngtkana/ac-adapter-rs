//! Formatter of iterator of `bool`.

use std::{borrow::Borrow, fmt::Debug};

pub struct S(String);
impl Debug for S {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.0)
    }
}

pub fn format<B, I>(iter: I) -> S
where
    B: Borrow<bool>,
    I: IntoIterator<Item = B>,
{
    S(format!(
        "[{}]",
        iter.into_iter()
            .map(|b| ['.', '#'][*(b.borrow()) as usize])
            .collect::<String>(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::BTreeSet, iter::empty};

    pub fn format1<B, I>(iter: I) -> String
    where
        B: Borrow<bool>,
        I: IntoIterator<Item = B>,
    {
        format!("{:?}", format(iter))
    }

    #[test]
    fn test_format() {
        assert_eq!(format1([false]).as_str(), "[.]");
        assert_eq!(format1([true]).as_str(), "[#]");
        assert_eq!(format1([false, true]).as_str(), "[.#]");
        assert_eq!(format1([true, false]).as_str(), "[#.]");
    }

    #[test]
    fn test_generics() {
        assert_eq!(format1(<[bool; 0]>::default()).as_str(), "[]");
        assert_eq!(format1(<[bool; 0]>::default()).as_str(), "[]");
        assert_eq!(format1(<[&bool; 0]>::default()).as_str(), "[]");
        assert_eq!(format1(<[bool; 0]>::default().as_slice()).as_str(), "[]");
        assert_eq!(format1(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(format1(Vec::<&bool>::new()).as_str(), "[]");
        assert_eq!(format1(Vec::<&mut bool>::new()).as_str(), "[]");
        assert_eq!(format1(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(format1(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(format1(BTreeSet::<bool>::new()).as_str(), "[]");
        assert_eq!(format1(empty::<bool>()).as_str(), "[]");
        assert_eq!(format1(empty::<bool>()).as_str(), "[]");
        assert_eq!(format1(empty::<&bool>()).as_str(), "[]");
        assert_eq!(format1(empty::<&bool>()).as_str(), "[]");
    }
}
