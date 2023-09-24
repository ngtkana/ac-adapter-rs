use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
use std::ops::Sub;

pub fn cipolla_sqrt<T: Unsigned>(a: T, p: T) -> Option<T> {
    let a = a % p;
    if p == T::TWO {
        Some(a)
    } else if a == T::ZERO {
        Some(T::ZERO)
    } else if binary_exponentiation(a, p / T::TWO, T::ONE, |x, y| x * y % p) != T::ONE {
        None
    } else {
        let mut b = T::ZERO;
        loop {
            let sqgen = (b * b + p - a) % p;
            if binary_exponentiation(sqgen, p / T::TWO, T::ONE, |x, y| x * y % p) != T::ONE {
                return Some(
                    binary_exponentiation(
                        [b, T::ONE],
                        (p + T::ONE) / T::TWO,
                        [T::ONE, T::ZERO],
                        |x, y| {
                            [
                                (x[0] * y[0] + (x[1] * y[1]) % p * sqgen) % p,
                                (x[0] * y[1] + x[1] * y[0]) % p,
                            ]
                        },
                    )[0],
                );
            }
            b = b + T::ONE;
        }
    }
}

fn binary_exponentiation<T: Unsigned, U: Copy>(
    mut a: U,
    mut n: T,
    id: U,
    mut f: impl FnMut(U, U) -> U,
) -> U {
    let mut ans = id;
    while n != T::ZERO {
        if n % T::TWO == T::ONE {
            ans = f(ans, a);
        }
        a = f(a, a);
        n = n / T::TWO;
    }
    ans
}

pub trait Unsigned:
    Sized
    + Clone
    + Copy
    + PartialEq
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
}

macro_rules! impl_unsigned {
    ($($T:ty),+) => {$(
        impl Unsigned for $T {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const TWO: Self = 2;
        }
    )+}
}
impl_unsigned! {u8, u16, u32, u64, u128, usize}

#[cfg(test)]
mod tests {
    use super::cipolla_sqrt;

    #[test]
    fn test_sqrt_all() {
        let mut sieve = [false; 100];
        let sieve_len = sieve.len();
        for p in 2..sieve_len {
            if sieve[p] {
                continue;
            }
            // 素数 p を順にテストです。
            let mut count = 0;
            for y in 1..p {
                if let Some(x) = cipolla_sqrt(y, p) {
                    assert_eq!(x * x % p, y);
                    count += 1;
                }
            }
            // 平方剰余の個数は ceil(p / 2) 個
            assert_eq!(count, p / 2);
            (p * p..)
                .step_by(p)
                .take_while(|&q| q < sieve_len)
                .for_each(|q| sieve[q] = true);
        }
    }
}
