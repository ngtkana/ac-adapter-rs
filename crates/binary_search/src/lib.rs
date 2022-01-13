pub fn binary_search_u8(mut lower: u8, mut upper: u8, mut f: impl FnMut(u8) -> bool) -> u8 {
    assert!(lower < upper);
    assert!(!f(lower) && f(upper));
    while lower + 1 < upper {
        let mid = lower + (upper - lower) / 2;
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
    upper
}

pub fn binary_search_i8(mut lower: i8, mut upper: i8, mut f: impl FnMut(i8) -> bool) -> i8 {
    assert!(lower < upper);
    assert!(!f(lower) && f(upper));
    while lower + 1 < upper {
        let mid = if lower <= 0 && 0 <= upper {
            (lower + upper) / 2
        } else {
            lower + (upper - lower) / 2
        };
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
    upper
}

pub fn exponential_search_u8(mut f: impl FnMut(u8) -> bool) -> Option<u8> {
    if f(0) {
        return Some(0);
    }
    let mut lower = 0;
    let mut upper = 1;
    while !f(upper) {
        lower = upper;
        if upper <= std::u8::MAX / 2 {
            upper *= 2;
        } else if upper == std::u8::MAX {
            return None;
        } else {
            upper = upper >> 1 | 1 << 7;
        }
    }
    Some(binary_search_u8(lower, upper, f))
}

pub fn exponential_search_i8(mut f: impl FnMut(i8) -> bool) -> Option<i8> {
    let mut lower;
    let mut upper;
    if f(0) {
        lower = -1;
        upper = 0;
        while f(lower) {
            upper = lower;
            if lower == std::i8::MIN {
                return Some(std::i8::MIN);
            }
            lower *= 2;
        }
    } else {
        lower = 0;
        upper = 1;
        while !f(upper) {
            lower = upper;
            if upper <= std::i8::MAX / 2 {
                upper *= 2;
            } else if upper == std::i8::MAX {
                return None;
            } else {
                upper = upper >> 1 | 1 << 6;
            }
        }
    }
    while lower + 1 < upper {
        let mid = lower + (upper - lower) / 2;
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
    Some(upper)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use std::{collections::HashMap, mem::swap};

    #[test]
    fn test_exponential_search_u8() {
        for expected in 0..=255 {
            let result = exponential_search_u8(|x| expected <= x);
            assert_eq!(result, Some(expected));
        }
        let result = exponential_search_u8(|_| false);
        assert_eq!(result, None);
    }

    #[test]
    fn test_exponential_search_i8() {
        for expected in -128..=127 {
            let result = exponential_search_i8(|x| expected <= x);
            assert_eq!(result, Some(expected));
        }
        let result = exponential_search_i8(|_| false);
        assert_eq!(result, None);
    }

    #[test]
    fn test_binary_search_u8() {
        for expected in 1..=255 {
            let result = binary_search_u8(0, 255, |x| expected <= x);
            assert_eq!(result, expected);
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let mut lower = rng.gen_range(0..255);
            let mut upper = rng.gen_range(0..=255);
            if lower >= upper {
                swap(&mut lower, &mut upper);
                upper += 1;
            }
            let mut memo = HashMap::<u8, bool>::from_iter(vec![(lower, false), (upper, true)]);
            let f = |x| *memo.entry(x).or_insert_with(|| rng.gen_bool(0.5));
            let result = binary_search_u8(lower, upper, f);
            assert!((lower + 1..=upper).contains(&result));
            assert!(memo[&result]);
            assert!(!memo[&(result - 1)]);
        }
    }

    #[test]
    fn test_binary_search_i8() {
        for expected in -127..=127 {
            let result = binary_search_i8(-128, 127, |x| expected <= x);
            assert_eq!(result, expected);
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let mut lower = rng.gen_range(-128..127);
            let mut upper = rng.gen_range(-128..=127);
            if lower >= upper {
                swap(&mut lower, &mut upper);
                upper += 1;
            }
            let mut memo = HashMap::<i8, bool>::from_iter(vec![(lower, false), (upper, true)]);
            let f = |x| *memo.entry(x).or_insert_with(|| rng.gen_bool(0.5));
            let result = binary_search_i8(lower, upper, f);
            assert!((lower + 1..=upper).contains(&result));
            assert!(memo[&result]);
            assert!(!memo[&(result - 1)]);
        }
    }
}
