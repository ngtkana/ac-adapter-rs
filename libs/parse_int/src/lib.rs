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
