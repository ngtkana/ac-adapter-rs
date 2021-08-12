use std::mem::swap;

pub fn ext_euclid_modinv(a: u64, b: u64) -> u64 {
    if a == 1 {
        1
    } else {
        b - (b * ext_euclid_modinv(b % a, a) - 1) / a
    }
}

pub fn berlekamp_massey_fp(a: i64, p: i64) -> [i64; 2] {
    let mut u0 = 0_i64;
    let mut v0 = 1_i64;
    let mut w0 = a * u0 + p * v0;
    let mut u1 = 1_i64;
    let mut v1 = 0_i64;
    let mut w1 = a * u1 + p * v1;
    while p <= w0 * w0 {
        let q = w0 / w1;
        u0 -= q * u1;
        v0 -= q * v1;
        w0 -= q * w1;
        swap(&mut u0, &mut u1);
        swap(&mut v0, &mut v1);
        swap(&mut w0, &mut w1);
    }
    [w0, u0]
}

#[cfg(test)]
mod tests {
    use super::{berlekamp_massey_fp, ext_euclid_modinv};
    const SMALL_PRIMES: [u64; 168] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
        283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
        509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
        751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
    ];

    #[test]
    fn test_ext_euclid_modinv() {
        for p in SMALL_PRIMES {
            for x in 1..p {
                let y = ext_euclid_modinv(x, p);
                assert!((1..p).contains(&y));
                assert_eq!(x * y % p, 1);
            }
        }
    }

    #[test]
    fn test_berlekamp_massey_fp() {
        for p in SMALL_PRIMES.iter().map(|&p| p as i64) {
            for a in 1..p {
                let [x, y] = berlekamp_massey_fp(a, p);
                assert!(0 <= x && x <= (p as f64).sqrt() as i64 && x * x != p);
                assert!(y.abs() <= (p as f64).sqrt() as i64);
                assert_eq!(x.rem_euclid(p), (a * y).rem_euclid(p));
            }
        }
    }
}
