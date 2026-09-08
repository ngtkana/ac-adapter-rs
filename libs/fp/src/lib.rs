//! 素体 $\mathbb{F}_P$ 上の四則演算・べき乗・逆元。
//!
//! `P` を `const` 型パラメータとして固定し、$\{0, 1, \ldots, P-1\}$ 上の演算を提供。
//! 加減乗は `u64`/`u128` の範囲内で完結し、逆元は拡張ユークリッド互除法で求める。
//! ほぼすべての操作が `const fn` のため、コンパイル時計算にも使える。
//!
//! # 仕様
//!
//! - 型: `Fp<const P: u64>`（`P` は素数）
//! - 生成: `fp_new::<P>(u64)`, `fpu::<P>(usize)` — 値を $\bmod P$ に還元
//! - 演算: `+`, `-`, `*`, `/`（`/` は逆元との乗算）, 単項 `-`
//! - `pow(e)`: $a^e \bmod P$
//! - `inv()`: $a^{-1} \bmod P$（$a \neq 0$ が前提）
//! - `Debug`: 有理数近似 `num/den`（Berlekamp–Massey で最小分子分母を復元）
//! - `Display`: 剰余値 $[0, P)$ をそのまま表示
//!
//! # 例
//!
//! ```
//! use fp::fp_new;
//! const P: u64 = 1009;
//! let a = fp_new::<P>(123);
//! assert_eq!(a * a.inv(), fp_new::<P>(1));
//! assert_eq!(a.pow(100), a.pow(99) * a);
//! ```
//!
//! # 計算量
//!
//! - 四則演算: $O(1)$
//! - `pow(e)`: $O(\log e)$
//! - `inv()`: $O(\log P)$

/// $\mathbb{F}_P$ の要素を `usize` から生成。自動的に mod P に削減。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// use fp::fpu;
/// const P: u64 = 1009;
/// assert_eq!(fpu::<P>(2000), fp_new::<P>(991)); // 2000 mod 1009
/// ```
pub const fn fpu<const P: u64>(value: usize) -> Fp<P> {
    Fp::new(value as u64)
}

/// $\mathbb{F}_P$ の要素を `u64` から生成。自動的に mod P に削減。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// const P: u64 = 1009;
/// assert_eq!(fp_new::<P>(123), fp_new::<P>(1132)); // 1132 mod 1009 = 123
/// ```
pub const fn fp_new<const P: u64>(value: u64) -> Fp<P> {
    Fp::new(value)
}

/// 素体 $\mathbb{F}_P$ の要素。$(0, 1, \ldots, P-1)$ 上の値を表現。
///
/// `const P: u64` で素数を固定。ほぼすべての操作は `const fn` 対応。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// const P: u64 = 1009;
/// let x = fp_new::<P>(100);
/// let y = fp_new::<P>(200);
/// assert_eq!(x + y, fp_new::<P>(300)); // $\mathbb{F}_{1009}$ 上の加算
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Fp<const P: u64> {
    value: u64,
}

impl<const P: u64> Fp<P> {
    /// 値を mod P に削減して $\mathbb{F}_P$ の要素を生成。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// const P: u64 = 1009;
    /// assert_eq!(fp_new::<P>(2000), fp_new::<P>(991));
    /// ```
    pub const fn new(value: u64) -> Self {
        Self { value: value % P }
    }

    pub const fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
        if P <= self.value {
            self.value -= P;
        }
    }

    pub const fn value(self) -> u64 {
        self.value
    }

    /// 乗算 $(a \times b) \bmod P$、$O(1)$。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// const P: u64 = 1009;
    /// let a = fp_new::<P>(123);
    /// let b = fp_new::<P>(456);
    /// assert_eq!(a.mul(b), a * b);
    /// ```
    pub const fn mul(self, rhs: Self) -> Self {
        Self {
            value: (self.value as u128 * rhs.value as u128 % P as u128) as u64,
        }
    }

    /// べき乗 $a^e \bmod P$、二進法で $O(\log e)$。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// const P: u64 = 1009;
    /// assert_eq!(fp_new::<P>(2).pow(10), fp_new::<P>(15)); // $2^{10} \equiv 15 \pmod{1009}$
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

    /// 逆元 $a^{-1} \bmod P$。拡張ユークリッドで $O(\log P)$。
    ///
    /// $a \times a^{-1} \equiv 1 \pmod{P}$ を満たす $a^{-1}$ を返す。
    /// 前提：$P$ は素数、$a \neq 0$。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// const P: u64 = 1009;
    /// let a = fp_new::<P>(123);
    /// assert_eq!(a * a.inv(), fp_new::<P>(1));
    /// ```
    pub const fn inv(self) -> Self {
        const fn euclid(a: i128, m: i128) -> i128 {
            if a == 1 {
                1
            } else {
                m + (1 - m * euclid(m % a, a)) / a
            }
        }
        Self {
            value: euclid(self.value as i128, P as i128) as u64,
        }
    }
}

/// Debug：有理近似で表示。Berlekamp-Massey で最小の分子分母を計算。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// const P: u64 = 1009;
/// assert_eq!(format!("{:?}", fp_new::<P>(2).inv()), "1/2"); // $2^{-1}$ を 1/2 で表示
/// ```
impl<const P: u64> std::fmt::Debug for Fp<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        pub const fn berlekamp_massey(a: i128, p: i128) -> [i128; 2] {
            let mut u0 = 0;
            let mut v0 = 1_i128;
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
        let [mut num, mut den] = berlekamp_massey(self.value as i128, P as i128);
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

/// Display：剰余値 $[0, P)$ をそのまま表示。
///
/// # 例
///
/// ```
/// use fp::fp_new;
/// const P: u64 = 1009;
/// assert_eq!(fp_new::<P>(123).to_string(), "123");
/// assert_eq!(fp_new::<P>(2000).to_string(), "991"); // 2000 mod 1009
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
        self.add_assign(rhs);
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
