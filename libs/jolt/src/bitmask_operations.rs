use crate::Unsigned;

/// Returns $2^n - 1$.
///
/// # Examples
/// ```
/// use riff::i2powm1;
/// assert_eq!(i2powm1::<u32>(0), 0);
/// assert_eq!(i2powm1::<u32>(1), 1);
/// assert_eq!(i2powm1::<u32>(2), 3);
/// assert_eq!(i2powm1::<u32>(3), 7);
/// assert_eq!(i2powm1::<u32>(31), 0x7FFF_FFFF);
/// assert_eq!(i2powm1::<u32>(32), 0xFFFF_FFFF);
/// ```
pub fn i2powm1<T: Unsigned>(n: u32) -> T {
    if n == T::bit_length() {
        T::MAX
    } else {
        (T::ONE << n) - T::ONE
    }
}
