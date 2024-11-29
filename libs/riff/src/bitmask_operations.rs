use crate::Unsigned;

/// Returns $2^n - 1$.
///
/// # Examples
/// ```
/// use crate::i2powm1;
/// assert_eq!(i2powm1::<u32>(0), 0);
/// assert_eq!(i2powm1::<u32>(1), 1);
/// assert_eq!(i2powm1::<u32>(2), 3);
/// assert_eq!(i2powm1::<u32>(3), 7);
/// ```
pub fn i2powm1<T: Unsigned>(n: u32) -> T {
    T::MAX >> (T::BITS - n)
}
