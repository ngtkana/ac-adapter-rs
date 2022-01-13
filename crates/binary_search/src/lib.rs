use std::{
    fmt::Debug,
    ops::{Add, Div, Mul, Neg, Sub},
};

pub trait Float:
    Sized
    + Copy
    + PartialOrd
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
    const INFINITY: Self;
    const NEG_INFINITY: Self;
    fn sqrt(self) -> Self;
}
impl Float for f32 {
    const ZERO: Self = 0.0;
    const ONE: Self = 1.0;
    const INFINITY: Self = std::f32::INFINITY;
    const NEG_INFINITY: Self = std::f32::NEG_INFINITY;
    fn sqrt(self) -> Self {
        self.sqrt()
    }
}
impl Float for f64 {
    const ZERO: Self = 0.0;
    const ONE: Self = 1.0;
    const INFINITY: Self = std::f64::INFINITY;
    const NEG_INFINITY: Self = std::f64::NEG_INFINITY;
    fn sqrt(self) -> Self {
        self.sqrt()
    }
}

pub fn exponential_search_floating<T: Float>(mut f: impl FnMut(T) -> bool) -> T {
    let mut lower;
    let mut upper;
    if f(T::ZERO) {
        if f(-T::ONE) {
            lower = -T::ONE - T::ONE;
            upper = -T::ONE;
            while f(lower) {
                upper = lower;
                lower = -lower * lower;
                if lower == T::NEG_INFINITY {
                    return T::NEG_INFINITY;
                }
            }
        } else {
            lower = -T::ONE;
            upper = -T::ONE / (T::ONE + T::ONE);
            while !f(upper) {
                lower = upper;
                upper = -upper * upper;
                if upper == T::ZERO {
                    return T::ZERO;
                }
            }
        }
        while lower < upper + upper {
            let mid = lower * (upper / lower).sqrt();
            if f(mid) {
                upper = mid;
            } else {
                lower = mid;
            }
        }
        debug_assert_eq!(lower, upper + upper);
    } else {
        if f(T::ONE) {
            lower = T::ONE / (T::ONE + T::ONE);
            upper = T::ONE;
            while f(lower) {
                upper = lower;
                lower = lower * lower;
            }
        } else {
            lower = T::ONE;
            upper = T::ONE + T::ONE;
            while !f(upper) {
                lower = upper;
                upper = upper * upper;
                if upper == T::INFINITY {
                    return T::INFINITY;
                }
            }
        }
        while lower + lower < upper {
            let mid = lower * (upper / lower).sqrt();
            if f(mid) {
                upper = mid;
            } else {
                lower = mid;
            }
        }
        debug_assert_eq!(lower + lower, upper);
    }
    loop {
        let mid = lower + (upper - lower) / (T::ONE + T::ONE);
        if lower == mid || mid == upper {
            return upper;
        }
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
}

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
    fn test_exponential_search_f64() {
        use std::f64::{EPSILON, INFINITY, MAX, MIN_POSITIVE, NEG_INFINITY};

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let expected: f64 = if rng.gen_bool(0.5) { 1.0 } else { -1.0 }
                * 2_f64.powf(rng.gen_range(-512.0..512.0));
            let mut count = 0;
            let result = exponential_search_floating(|x| {
                count += 1;
                expected <= x
            });
            assert!(count <= 72);
            assert_eq!(result, expected);
        }

        for &(threshold, expected) in &[
            // 正確に計算できるもの
            (0.0, 0.0),
            (-0.0, 0.0),
            (INFINITY, INFINITY),
            (NEG_INFINITY, NEG_INFINITY),
            (EPSILON, EPSILON),
            (MAX.sqrt(), MAX.sqrt()),
            (-MAX.sqrt(), -MAX.sqrt()),
            (MIN_POSITIVE, MIN_POSITIVE),
            (-MIN_POSITIVE, -MIN_POSITIVE),
            // できないもの
            (MAX.sqrt() * 1.000000000001, INFINITY),
            (-MAX.sqrt() * 1.000000000001, NEG_INFINITY),
        ] {
            let result = exponential_search_floating(|x| threshold <= x);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_exponential_search_f32() {
        use std::f32::{EPSILON, INFINITY, MAX, MIN_POSITIVE, NEG_INFINITY};

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let expected: f32 =
                if rng.gen_bool(0.5) { 1.0 } else { -1.0 } * 2_f32.powf(rng.gen_range(-63.0..63.0));
            let mut count = 0;
            let result = exponential_search_floating(|x| {
                count += 1;
                expected <= x
            });
            assert!(count <= 72);
            assert_eq!(result, expected);
        }

        for &(threshold, expected) in &[
            // 正確に計算できるもの
            (0.0, 0.0),
            (-0.0, 0.0),
            (INFINITY, INFINITY),
            (NEG_INFINITY, NEG_INFINITY),
            (EPSILON, EPSILON),
            (MAX.sqrt(), MAX.sqrt()),
            (-MAX.sqrt(), -MAX.sqrt()),
            (MIN_POSITIVE, MIN_POSITIVE),
            (-MIN_POSITIVE, -MIN_POSITIVE),
            // できないもの
            (MAX.sqrt() * 1.000001, INFINITY),
            (-MAX.sqrt() * 1.000001, NEG_INFINITY),
        ] {
            let result = exponential_search_floating(|x| threshold <= x);
            assert_eq!(result, expected);
        }
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
