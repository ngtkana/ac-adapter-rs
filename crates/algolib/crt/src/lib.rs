#![warn(missing_docs)]
//! 中国剰余定理をします。

use std::mem;

/// 中国剰余定理をします。
///
/// # 戻り値
///
/// `z % m == i` が `z % mi == xi for i in 0..n` と同値になるような `x`, `m` の組を返します。
#[allow(clippy::many_single_char_names)]
pub fn crt(xm: &[(u64, u64)]) -> Option<(u64, u64)> {
    xm.iter()
        .try_fold((0, 1), |(x0, m0), &(x1, m1)| {
            let (option_x, m) = crt_impl(x0, m0, x1 as i64, m1 as i64);
            option_x.map(|x| (x, m))
        })
        .map(|(x, m)| (x as u64, m as u64))
}

// これの答えです。
// ans = x0 ( mod m0 )
// ans = x1 ( mod m1 )
#[allow(clippy::many_single_char_names)]
fn crt_impl(x0: i64, m0: i64, x1: i64, m1: i64) -> (Option<i64>, i64) {
    let dx = x1 - x0;
    let (a_inv, g) = mod_inverse_gcd(m0, m1);
    let l = m0 / g * m1;
    let res = if dx % g == 0 {
        let b = dx / g;
        let m = m1 / g;
        let k = b * a_inv % m;
        let k = if k < 0 { k + m } else { k };
        Some(x0 + m0 * k)
    } else {
        None
    };
    (res, l)
}

// TODO: 一般の符号あり整数型を受け取れるようにしたいです。
#[allow(clippy::many_single_char_names)]
fn mod_inverse_gcd(x: i64, m: i64) -> (i64, i64) {
    let mut x = x;
    let mut y = m;
    let mut u = 1;
    let mut v = 0;
    while x != 0 {
        let q = y / x;
        y -= q * x;
        v -= q * u;
        mem::swap(&mut x, &mut y);
        mem::swap(&mut u, &mut v);
    }
    let res = if v < 0 { v + m } else { v };
    (res, y)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use test_case::test_case;

    fn gcd_brute(x: i64, y: i64) -> i64 {
        (1..=x.min(y))
            .rev()
            .find(|&i| x % i == 0 && y % i == 0)
            .unwrap()
    }

    fn lcm_brute(x: i64, y: i64) -> i64 {
        x * y / gcd_brute(x, y)
    }

    fn crt_impl_brute(x0: i64, m0: i64, x1: i64, m1: i64) -> (Option<i64>, i64) {
        let l = lcm_brute(m0, m1);
        ((0..l).find(|&i| i % m0 == x0 && i % m1 == x1), l)
    }

    #[test]
    fn test_crt_impl_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..120 {
            let m0 = rng.gen_range(2, 30);
            let x0 = rng.gen_range(0, m0);
            let m1 = rng.gen_range(2, 30);
            let x1 = rng.gen_range(0, m1);
            let expected = crt_impl_brute(x0, m0, x1, m1);
            println!(
                "x0 = {}, m0 = {}, x1 = {}, m1 = {}, expected = {:?}",
                x0, m0, x1, m1, expected
            );
            let result = crt_impl(x0, m0, x1, m1);
            assert_eq!(expected, result);
        }
    }

    fn crt_brute(a: &[(u64, u64)]) -> Option<(u64, u64)> {
        let l = a.iter().fold(1, |l, &(_, m)| lcm_brute(l, m as i64));
        (0..l)
            .map(|x| x as u64)
            .find(|&x| a.iter().all(|&(y, m)| x % m == y))
            .map(|x| (x, l as u64))
    }

    #[test_case(&[(2, 3), (3, 5), (2, 7)] => Some((23, 105)))]
    fn test_crt_hand(a: &[(u64, u64)]) -> Option<(u64, u64)> {
        crt(a)
    }

    #[test]
    fn test_crt_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..50 {
            let n = rng.gen_range(0, 6);
            let a = std::iter::repeat_with(|| {
                let m = rng.gen_range(2, 10);
                let x = rng.gen_range(0, m);
                (x, m)
            })
            .take(n)
            .collect::<Vec<_>>();
            let expected = crt_brute(&a);
            println!("a = {:?}, expected = {:?}", &a, expected);
            let result = crt(&a);
            assert_eq!(expected, result);
        }
    }
}
