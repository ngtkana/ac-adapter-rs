use {super::Value, std::mem::replace};

/// Takes an unsigned integer and returns an iterator to yield all the pairs of a prime factor of
/// it and the multiplicity of it.
///
/// # Note
///
/// Return value is ordered in ascending order of the prime factors.
///
///
/// # Example
///
/// Basic usage:
/// ```
/// use trial::prime_factors;
///
/// let mut iter = prime_factors(60u32);
/// assert_eq!(iter.next(), Some((2, 2)));
/// assert_eq!(iter.next(), Some((3, 1)));
/// assert_eq!(iter.next(), Some((5, 1)));
/// assert_eq!(iter.next(), None);
/// ```
pub fn prime_factors<T: Value>(n: T) -> PrimeFactors<T> {
    assert_ne!(n, T::zero(), "Cannot call `prime_factors` by `0`.");
    PrimeFactors { n, p: T::one() }
}

/// [See the document of a function `prime_factors`](`prime_factors`)
pub struct PrimeFactors<T> {
    n: T,
    p: T,
}
impl<T: Value> Iterator for PrimeFactors<T> {
    type Item = (T, usize);
    fn next(&mut self) -> Option<Self::Item> {
        let Self { n, p } = self;
        while *p * *p <= *n {
            (*p).increment();
            let mut multi = 0;
            while (*p).divides(*n) {
                *n /= *p;
                multi += 1;
            }
            if multi != 0 {
                return Some((*p, multi));
            }
        }
        if *n == T::one() {
            None
        } else {
            Some((replace(n, T::one()), 1))
        }
    }
}

#[cfg(test)]
mod tests {
    use {super::prime_factors, test_case::test_case};

    #[test_case(1 => Vec::<(u32, usize)>::new())]
    #[test_case(2 => vec![(2, 1)])]
    #[test_case(3 => vec![(3, 1)])]
    #[test_case(4 => vec![(2, 2)])]
    #[test_case(5 => vec![(5, 1)])]
    #[test_case(6 => vec![(2, 1), (3, 1)])]
    #[test_case(12 => vec![(2, 2), (3, 1)])]
    #[test_case(36 => vec![(2, 2), (3, 2)])]
    fn test_divisors(n: u32) -> Vec<(u32, usize)> {
        prime_factors(n).collect()
    }
}
