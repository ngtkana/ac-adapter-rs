pub const fn fpu<const P: u64>(value: usize) -> Fp<P> {
    Fp::new(value as u64)
}

pub const fn fp<const P: u64>(value: u64) -> Fp<P> {
    Fp::new(value)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Fp<const P: u64> {
    value: u64,
}

impl<const P: u64> Fp<P> {
    pub const fn new(value: u64) -> Self {
        Self { value: value % P }
    }
    pub const fn mul(self, rhs: Self) -> Self {
        Self {
            value: self.value * rhs.value % P,
        }
    }
    pub const fn pow(mut self: Self, mut exp: u64) -> Self {
        if exp == 0 {
            return fp(1);
        }
        let mut ans = fp(1);
        while exp != 1 {
            if exp & 1 == 1 {
                ans = ans.mul(self);
            }
            self = self.mul(self);
            exp >>= 1;
        }
        ans.mul(self)
    }
    pub const fn inv(self) -> Self {
        const fn euclid(a: i64, m: i64) -> i64 {
            if a == 1 {
                1
            } else {
                m + (1 - m * euclid(m % a, a)) / a
            }
        }
        Self {
            value: euclid(self.value as i64, P as i64) as u64,
        }
    }
}

impl<const P: u64> std::fmt::Debug for Fp<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        pub const fn berlekamp_massey(a: i64, p: i64) -> [i64; 2] {
            let mut u0 = 0;
            let mut v0 = 1_i64;
            let mut w0 = a * u0 + p * v0;
            let mut u1 = 1;
            let mut v1 = 0;
            let mut w1 = a * u1 + p * v1;
            while p <= w0 * w0 {
                let q = w0 / w1;
                u0 -= q * u1;
                v0 -= q * v1;
                w0 -= q * w1;
                std::mem::swap(&mut u0, &mut u1);
                std::mem::swap(&mut v0, &mut v1);
                std::mem::swap(&mut w0, &mut w1);
            }
            [w0, u0]
        }
        if self.value == 0 {
            return write!(f, "0");
        }
        let [mut num, mut den] = berlekamp_massey(self.value as i64, P as i64);
        if den < 0 {
            num = -num;
            den = -den;
        }
        if den == 1 {
            write!(f, "{num}")
        } else {
            write!(f, "{num}/{den}")
        }
    }
}

impl<const P: u64> std::fmt::Display for Fp<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// ==========================================
// Arithmetic
// ==========================================
impl<const P: u64> std::ops::Add for Fp<P> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}
impl<const P: u64> std::ops::AddAssign for Fp<P> {
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
        if P <= self.value {
            self.value -= P;
        }
    }
}
impl<const P: u64> std::ops::Sub for Fp<P> {
    type Output = Self;
    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}
impl<const P: u64> std::ops::SubAssign for Fp<P> {
    fn sub_assign(&mut self, rhs: Self) {
        if self.value < rhs.value {
            self.value += P;
        }
        self.value -= rhs.value;
    }
}
impl<const P: u64> std::ops::Mul for Fp<P> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}
impl<const P: u64> std::ops::MulAssign for Fp<P> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}
impl<const P: u64> std::ops::Div for Fp<P> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}
impl<const P: u64> std::ops::DivAssign for Fp<P> {
    fn div_assign(&mut self, rhs: Self) {
        *self = (*self) / rhs
    }
}

impl<const P: u64> std::ops::Neg for Fp<P> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.value == 0 {
            self
        } else {
            Self {
                value: P - self.value,
            }
        }
    }
}

// ==========================================
// Iterators
// ==========================================
impl<const P: u64> std::iter::Sum for Fp<P> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(fp(0), |acc, item| acc + item)
    }
}

impl<'a, const P: u64> std::iter::Sum<&'a Self> for Fp<P> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(fp(0), |acc, &item| acc + item)
    }
}
impl<const P: u64> std::iter::Product for Fp<P> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(fp(1), |acc, x| acc * x)
    }
}
impl<'a, const P: u64> std::iter::Product<&'a Self> for Fp<P> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().product()
    }
}
