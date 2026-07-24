//! Prime field arithmetic for $𝔽_P$ modular computations.
//!
//! This crate provides a fixed-size finite field implementation parameterized by a prime
//! modulus `P`. It supports all standard arithmetic operations (addition, subtraction,
//! multiplication, division, and negation) along with exponentiation and modular inverse
//! computation. The implementation uses compile-time constants for the prime, making it
//! efficient for competitive programming and mathematical algorithms.
//!
//! # Features
//!
//! - Basic arithmetic: addition, subtraction, multiplication, division, negation
//! - Fast exponentiation: binary exponentiation in $O(\log n)$ time
//! - Modular inverse: via extended Euclidean algorithm in $O(\log P)$ time
//! - Const-friendly: most operations can run at compile time
//! - Iterator support: `Sum` and `Product` traits for iterators
//! - Debug formatting: displays elements as rational approximations (simplified fractions)
//!
//! # Examples
//!
//! ```
//! use fp::{fp, Fp};
//!
//! // Operations in $𝔽_{1009}$
//! const P: u64 = 1009;
//!
//! let a = fp::<P>(123);
//! let b = fp::<P>(456);
//!
//! // Arithmetic operations
//! let sum = a + b;
//! let product = a * b;
//! let quotient = a / b;      // $a \cdot b^{-1} \bmod P$
//!
//! // Exponentiation
//! let power = a.pow(100);    // $a^{100} \bmod P$
//! ```
//!
//! # Safety
//!
//! This library assumes `P` is a prime number. If `P` is composite, modular inverse
//! computation produces undefined results. Always verify that your constant parameter
//! is prime.
//!
//! # Complexity Summary
//!
//! - Constructor: $O(1)$
//! - Addition/Subtraction: $O(1)$
//! - Multiplication/Division: $O(1)$
//! - Exponentiation: $O(\log n)$
//! - Modular inverse: $O(\log P)$

/// Constructs an element of $𝔽_P$ from a `usize` value.
///
/// The input is automatically reduced modulo `P` to ensure the result is in
/// the valid range $[0, P)$.
///
/// # Examples
///
/// ```
/// use fp::{fpu, fp};
///
/// const P: u64 = 1009;
/// let a = fpu::<P>(2000);  // Normalized to 2000 mod 1009 = 991
/// assert_eq!(a, fp::<P>(991));
/// ```
pub const fn fpu<const P: u64>(value: usize) -> Fp<P> {
    Fp::new(value as u64)
}

/// Constructs an element of $𝔽_P$ from a `u64` value.
///
/// The input is automatically reduced modulo `P` to ensure the result is in
/// the valid range $[0, P)$. Use this when `usize` is inconvenient.
///
/// # Examples
///
/// ```
/// use fp::fp;
///
/// const P: u64 = 1009;
/// let a = fp::<P>(123);
/// let b = fp::<P>(1132);  // 1132 mod 1009 = 123
/// assert_eq!(a, b);
/// ```
pub const fn fp<const P: u64>(value: u64) -> Fp<P> {
    Fp::new(value)
}

/// An element of the prime field 𝔽_P = {0, 1, 2, ..., P-1}.
///
/// This struct represents a single element of a finite field modulo a prime `P`.
/// The parameter `P` is fixed at compile time as a const generic. The struct
/// implements `Copy` and `Clone`, allowing it to be used with value semantics.
///
/// Most operations on `Fp<P>` are `const` functions, enabling computation at
/// compile time.
///
/// # Examples
///
/// ```
/// use fp::fp;
///
/// const P: u64 = 1009;
/// let x = fp::<P>(100);
/// let y = fp::<P>(200);
/// let z = x + y;  // Addition in 𝔽_{1009}
/// assert_eq!(z, fp::<P>(300));
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Fp<const P: u64> {
    value: u64,
}

impl<const P: u64> Fp<P> {
    /// Constructs an element of 𝔽_P by reducing `value` modulo `P`.
    ///
    /// This is a const function and may be evaluated at compile time.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::{Fp, fp};
    ///
    /// const P: u64 = 1009;
    /// let a = Fp::<P>::new(2000);
    /// assert_eq!(a, fp::<P>(991));  // 2000 mod 1009 = 991
    /// ```
    pub const fn new(value: u64) -> Self {
        Self { value: value % P }
    }

    /// Multiplies two elements: (self × rhs) mod P.
    ///
    /// Time complexity: O(1)
    ///
    /// This is a const function and may be evaluated at compile time.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::fp;
    ///
    /// const P: u64 = 1009;
    /// let a = fp::<P>(123);
    /// let b = fp::<P>(456);
    /// let c = a.mul(b);
    /// assert_eq!(c, a * b);  // Equivalent to using the `*` operator
    /// ```
    pub const fn mul(self, rhs: Self) -> Self {
        Self {
            value: self.value * rhs.value % P,
        }
    }

    /// Computes self^exp mod P using binary exponentiation.
    ///
    /// Returns 1 if exp = 0. Uses the binary exponentiation algorithm for
    /// fast computation of large powers.
    ///
    /// Time complexity: O(log exp)
    ///
    /// This is a const function and may be evaluated at compile time.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::fp;
    ///
    /// const P: u64 = 1009;
    /// let a = fp::<P>(2);
    /// let result = a.pow(10);  // 2^10 ≡ 1024 ≡ 15 (mod 1009)
    /// assert_eq!(result, fp::<P>(15));
    /// ```
    pub const fn pow(mut self, mut exp: u64) -> Self {
        if exp == 0 {
            return Self::new(1);
        }
        let mut ans = Self::new(1);
        while exp != 1 {
            if exp & 1 == 1 {
                ans = ans.mul(self);
            }
            self = self.mul(self);
            exp >>= 1;
        }
        ans.mul(self)
    }

    /// Computes the modular inverse self^{-1} mod P.
    ///
    /// If P is prime and self ≠ 0, returns the unique element `inv` such that
    /// self × inv ≡ 1 (mod P). Uses the extended Euclidean algorithm internally.
    ///
    /// Time complexity: O(log P)
    ///
    /// # Panics or Undefined Behavior
    ///
    /// If `self.value == 0` or if `P` is not prime, behavior is undefined.
    /// Always ensure `P` is prime before using this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::fp;
    ///
    /// const P: u64 = 1009;
    /// let a = fp::<P>(123);
    /// let inv_a = a.inv();
    /// assert_eq!(a * inv_a, fp::<P>(1));  // 123 × 123^{-1} ≡ 1 (mod 1009)
    /// ```
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

/// Debug formatting displays the element as a rational approximation.
///
/// When `Debug` is printed, the value is represented as a simplified fraction num/den
/// or integer, computed via Berlekamp–Massey algorithm to find the smallest numerator
/// and denominator. For zero, it prints "0". This representation can be useful for
/// understanding the structure of field elements when they correspond to rational numbers.
///
/// # Examples
///
/// ```
/// use fp::fp;
///
/// const P: u64 = 1009;
/// let a = fp::<P>(2);
/// let inv_a = a.inv();
/// // 2^{-1} mod 1009 displayed as rational approximation "1/2"
/// assert_eq!(format!("{:?}", inv_a), "1/2");
/// // Negation of the inverse: -(1/2) = -1/2
/// assert_eq!(format!("{:?}", -inv_a), "-1/2");
/// ```
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

/// Display formatting shows the raw modular value in [0, P).
///
/// This is useful for compact display of the field element as a plain integer.
/// Use this when you want to see the actual residue value.
///
/// # Examples
///
/// ```
/// use fp::fp;
///
/// const P: u64 = 1009;
/// let a = fp::<P>(123);
/// assert_eq!(a.to_string(), "123");
/// let b = fp::<P>(2000);  // 2000 mod 1009 = 991
/// assert_eq!(b.to_string(), "991");
/// ```
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
#[allow(clippy::suspicious_arithmetic_impl)]
impl<const P: u64> std::ops::Div for Fp<P> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}
impl<const P: u64> std::ops::DivAssign for Fp<P> {
    fn div_assign(&mut self, rhs: Self) {
        *self = (*self) / rhs;
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
        iter.fold(Self::new(0), |acc, item| acc + item)
    }
}

impl<'a, const P: u64> std::iter::Sum<&'a Self> for Fp<P> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new(0), |acc, &item| acc + item)
    }
}
impl<const P: u64> std::iter::Product for Fp<P> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(1), |acc, x| acc * x)
    }
}
impl<'a, const P: u64> std::iter::Product<&'a Self> for Fp<P> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().product()
    }
}
