use crate::Unsigned;

/// $2^n - 1$ を計算する。
///
/// `n` がビット幅 `T::bit_length()` に等しいときは `T::MAX` を返す（左シフトのオーバーフローを回避）。
///
/// # 例
/// ```
/// use riff::i2powm1;
/// assert_eq!(i2powm1::<u32>(2), 3); // 2^2 - 1 = 3
/// assert_eq!(i2powm1::<u32>(32), 0xffff_ffff); // ビット幅ちょうど：オーバーフロー回避
/// ```
pub fn i2powm1<T: Unsigned>(n: u32) -> T {
    if n == T::bit_length() {
        T::MAX
    } else {
        (T::ONE << n) - T::ONE
    }
}
