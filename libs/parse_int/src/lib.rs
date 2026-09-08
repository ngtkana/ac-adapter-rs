//! 符号なし10進数のバイト列を高速に整数へ変換する。
//!
//! `str::parse` は符号・基数・オーバーフローなど汎用パースの分岐を含むぶん遅い。
//! 桁がすべて `b'0'..=b'9'` であることが分かっている場合、各バイトを1桁として
//! ホーナー法で `result = result * 10 + digit` を繰り返すだけで変換できる。
//!
//! # 仕様
//!
//! - [`fast_parse_u64`][]: バイト列 $s = s_0 s_1 \ldots s_{n-1}$（各 $s_i$ は `b'0'..=b'9'`）を
//!   10進数とみなし、$\sum_{i} (s_i - \mathtt{b'0'}) \cdot 10^{n-1-i}$ を返す
//!
//! 先頭のゼロ埋めや空スライスも受け付けるが、`b'0'..=b'9'` 以外のバイトを含む場合や
//! `u64` の範囲を超える場合の挙動は未規定。
//!
//! # 例
//!
//! ```
//! use parse_int::fast_parse_u64;
//! assert_eq!(fast_parse_u64(b"1234"), 1234);
//! assert_eq!(fast_parse_u64(b"0042"), 42);
//! ```
//!
//! # 計算量
//!
//! - [`fast_parse_u64`][]: $O(n)$（$n$ はバイト列の長さ）

/// バイト列 $s_0 s_1 \ldots s_{n-1}$（各 $s_i$ は `b'0'..=b'9'`）を10進数として `u64` に変換する。
///
/// # 例
///
/// ```
/// use parse_int::fast_parse_u64;
/// assert_eq!(fast_parse_u64(b"1234"), 1234);
/// ```
pub fn fast_parse_u64(slice: &[u8]) -> u64 {
    let mut result = 0u64;
    for &x in slice {
        result = result * 10 + u64::from(x - b'0');
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tests_fast_parse_u64() {
        for x in 0..10000 {
            let s = x.to_string();
            let result = fast_parse_u64(s.as_bytes());
            assert_eq!(result, x);
        }
    }
}
