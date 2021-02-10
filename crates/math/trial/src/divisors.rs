use super::Value;

/// Takes an unsigned integer and returns an iterator to yield all the divisors of it.
///
/// # Note
///
/// The order of the return value is not necessarily ascending, but ordered in "alternating" order.
/// (eg. 1, 36, 2, 18, 3, 12, 4, 9)
///
/// # Example
///
/// Basic usage:
/// ```
/// use trial::divisors;
///
/// let mut iter = divisors(12u32);
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(12));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(6));
/// assert_eq!(iter.next(), Some(3));
/// assert_eq!(iter.next(), Some(4));
/// assert_eq!(iter.next(), None);
/// ```
pub fn divisors<T: Value>(n: T) -> Divisors<T> {
    Divisors {
        n,
        d: T::zero(),
        rev: false,
    }
}
/// [See the document of a function `divisors`](`divisors`)
pub struct Divisors<T> {
    n: T,
    d: T,
    rev: bool,
}
impl<T: Value> Iterator for Divisors<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let Self { n, d, rev } = self;
        if *rev {
            *rev = false;
            Some(*n / *d)
        } else {
            (*d).increment();
            while *d * *d <= *n && !(*d).divides(*n) {
                (*d).increment();
            }
            if *n < *d * *d {
                None
            } else {
                if *n != *d * *d {
                    *rev = true;
                }
                Some(*d)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use {super::divisors, test_case::test_case};

    #[test_case(0 => Vec::<u32>::new())]
    #[test_case(1 => vec![1])]
    #[test_case(2 => vec![1, 2])]
    #[test_case(3 => vec![1, 3])]
    #[test_case(4 => vec![1, 4, 2])]
    #[test_case(5 => vec![1, 5])]
    #[test_case(6 => vec![1, 6, 2, 3])]
    #[test_case(12 => vec![1, 12, 2, 6, 3, 4])]
    #[test_case(36 => vec![1, 36, 2, 18, 3, 12, 4, 9, 6])]
    fn test_divisors(n: u32) -> Vec<u32> {
        divisors(n).collect()
    }
}
