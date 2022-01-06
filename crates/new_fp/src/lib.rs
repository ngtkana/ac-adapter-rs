use std::{
    fmt::{Debug, Display},
    hash::Hash,
    iter::{successors, Product, Sum},
    marker::PhantomData,
    mem::swap,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

define_fp! {
    1_000_000_007;
    pub enum M1000000007;
    pub type F1000000007;
}
define_fp! {
    998_244_353, 3; // 119 * 2 ^ 23 + 1
    pub enum M998244353;
    pub type F998244353;
}
define_fp! {
    1_012_924_417, 5; // 483 * 2 ^ 21 + 1
    pub enum M1012924417;
    pub type F1012924417;
}
define_fp! {
    924_844_033, 5; // 441 * 2 ^ 21 + 1
    pub enum M924844033;
    pub type F924844033;
}

/// 有限体型の実装するトレイトです。[`define_fp!`] マクロを使いましょう。
pub trait Mod {
    /// 法
    ///
    /// # Examples
    ///
    /// ```
    /// use new_fp::define_fp;
    /// define_fp!(13);
    /// assert_eq!(F::P, 13);
    /// ```
    const P: u64; // ……ほう。
}
/// FFT に使えそうな法に実装するトレイトです。[`define_fp!`] マクロを使いましょう。
pub trait Fft: Mod {
    /// 原子根
    ///
    /// # Examples
    ///
    /// ```
    /// use new_fp::{define_fp, fp};
    /// define_fp!(5, 2);
    /// assert_eq!(F::ROOT, fp!(2));
    /// ```
    const ROOT: u64;
}

/// [`Mod`] を実装した型 `$m` と、型エイリアス `$f = Fp<$m>` を定義します。
///
/// # Examples
///
/// ## 基本
///
/// ```
/// use new_fp::{define_fp, fp, Mod};
/// define_fp!(13);
/// assert_eq!(F::P, 13);
/// assert_eq!(M::P, 13);
/// ```
///
/// ## 原子根付き
/// ```
/// use new_fp::{define_fp, fp, Mod, Fft};
/// define_fp!(13, 2);
/// assert_eq!(F::P, 13);
/// assert_eq!(M::P, 13);
/// assert_eq!(F::ROOT, fp!(2));
/// assert_eq!(M::ROOT, 2);
/// ```
///
/// ## 型名付き
/// ```
/// use new_fp::{define_fp, fp, Mod, Fft};
/// define_fp!(13; pub enum M13; pub type F13);
/// assert_eq!(F13::P, 13);
/// assert_eq!(M13::P, 13);
///
/// define_fp!(13, 2; pub enum M13_2; pub type F13_2);
/// assert_eq!(F13_2::P, 13);
/// assert_eq!(M13_2::P, 13);
/// assert_eq!(F13_2::ROOT, fp!(2));
/// assert_eq!(M13_2::ROOT, 2);
/// ```
#[macro_export]
macro_rules! define_fp {
    ($p:expr) => {
        $crate::define_fp! { $p; enum M; type F }
    };
    ($p:expr, $root:expr) => {
        $crate::define_fp! { $p, $root; enum M; type F }
    };
    (
        $p:expr;
        $vism:vis enum $m:ident;
        $visf:vis type $f:ident$(;)?
    ) => {
        $vism enum $m {}
        impl $crate::Mod for $m {
            const P: u64 = $p;
        }
        $visf type $f = $crate::Fp<$m>;
    };
    (
        $p:expr, $root:expr;
        $vism:vis enum $m:ident;
        $visf:vis type $f:ident$(;)?
    ) => {
        $crate::define_fp! { $p; $vism enum $m; $visf type $f }
        impl $crate::Fft for $m {
            const ROOT: u64 = $root;
        }
    };
}

/// [`Fp`] 型のオブジェクトを構築します。
///
/// # 使い方
///
/// １つ式を入れると、それで [`Fp::from()`] を呼びます。
///
/// ```
/// use new_fp::{fp, define_fp};
/// define_fp!(13);
///
/// // リテラル
/// let a: F = fp!(6);
/// assert_eq!(a.value(), 6);
///
/// // 式
/// assert_eq!(fp!(2 + 3), F::new(5));
///
/// // 変数
/// let x: i16 = -3;
/// assert_eq!(fp!(x), F::new(10));
/// ```
///
/// セミコロン区切りで２つ整数を入れると、順に分子、分母とする分数を構築します。
///
/// ```
/// use new_fp::{fp, define_fp};
/// define_fp!(13);
///
/// assert_eq!(fp!(2; 3), F::new(2) / F::new(3));
/// ```
#[macro_export]
macro_rules! fp {
    ($num:expr; $den:expr) => {
        $crate::Fp::from($num) / $crate::Fp::from($den)
    };
    ($value:expr) => {
        $crate::Fp::from($value)
    };
}

pub struct Fp<M>(u64, PhantomData<fn() -> M>);
impl<M: Fft> Fp<M> {
    /// 原子根
    pub const ROOT: Self = Self(M::ROOT, PhantomData);
}
impl<M: Mod> Fp<M> {
    /// 法です。[`Mod::P`] へのショートカットです。
    ///
    /// # Example
    ///
    /// ```
    /// use new_fp::{define_fp};
    ///
    /// define_fp!(7);
    /// assert_eq!(F::P, 7);
    ///
    /// define_fp! { 11; enum M11; type F11 }
    /// assert_eq!(F11::P, 11);
    /// ```
    pub const P: u64 = M::P;
    pub fn new(value: u64) -> Self {
        Self(value % Self::P, PhantomData)
    }
    /// 整数に戻します。
    ///
    /// # Example
    ///
    /// ```
    /// use new_fp::{define_fp};
    ///
    /// define_fp!(7);
    /// let x = F::new(13).value();
    /// assert_eq!(x, 6);
    /// ```
    pub fn value(self) -> u64 {
        self.0
    }
    /// 逆数を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use new_fp::{define_fp, fp};
    ///
    /// define_fp!(7);
    /// let x = F::new(3).inv();
    /// assert_eq!(x, fp!(5));
    /// ```
    pub fn inv(self) -> Self {
        let mut x = Self::P as i64;
        let mut y = self.0 as i64;
        let mut u = 0;
        let mut v = 1;
        while y != 0 {
            let q = x / y;
            x -= y * q;
            u -= v * q;
            swap(&mut x, &mut y);
            swap(&mut u, &mut v);
        }
        debug_assert_eq!(x, 1);
        debug_assert_eq!(v.abs(), Self::P as i64);
        debug_assert!(u.abs() < Self::P as i64);
        if u < 0 {
            u += Self::P as i64;
        }
        Self(u as u64, PhantomData)
    }
    /// `self` の `exp` 乗を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use new_fp::{define_fp, fp};
    ///
    /// define_fp!(7);
    /// let x = F::new(3).inv();
    /// assert_eq!(x, fp!(5));
    /// ```
    pub fn pow(mut self, mut exp: u64) -> Self {
        let mut res = Self(1, PhantomData);
        if exp != 0 {
            while exp != 1 {
                if exp % 2 == 1 {
                    res *= self;
                }
                exp /= 2;
                self *= self;
            }
            res *= self;
        }
        res
    }
}
impl<M: Mod> Copy for Fp<M> {}
impl<M: Mod> Clone for Fp<M> {
    fn clone(&self) -> Self {
        Self(self.0, self.1)
    }
}
impl<M: Mod> PartialEq for Fp<M> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
impl<M: Mod> Display for Fp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}
impl<M: Mod> Eq for Fp<M> {}
impl<M: Mod> Default for Fp<M> {
    fn default() -> Self {
        Self(0, PhantomData)
    }
}
impl<M: Mod> Hash for Fp<M> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}
impl<M: Mod> Debug for Fp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
        if self.0 == 0 {
            return write!(f, "0");
        }
        let [mut num, mut den] = berlekamp_massey_fp(self.0 as i64, M::P as i64);
        if den < 0 {
            num = -num;
            den = -den;
        }
        if den == 1 {
            write!(f, "{}", num)
        } else {
            write!(f, "{}/{}", num, den)
        }
    }
}
macro_rules! impl_from_large_int {
    ($($T:ty), *$(,)?) => {$(
        impl<M: Mod> From<$T> for Fp<M> {
            fn from(x: $T) -> Self {
                Self::new(x.rem_euclid(M::P as _) as u64)
            }
        }
    )*}
}
impl_from_large_int! {
    i8, i16, i32, i64,
    u128, usize,
    i128, isize,
}
macro_rules! impl_from_small_int {
    ($($T: ty), *$(,)?) => {$(
        impl<M: Mod> From<$T> for Fp<M> {
            fn from(x: $T) -> Self {
                Self::new(x as u64)
            }
        }
    )*}
}
impl_from_small_int! {
    u8, u16, u32, u64,
}

impl<M: Mod, T: Into<Fp<M>>> AddAssign<T> for Fp<M> {
    fn add_assign(&mut self, rhs: T) {
        self.0 += rhs.into().0;
        if M::P <= self.0 {
            self.0 -= M::P;
        }
    }
}
impl<M: Mod, T: Into<Fp<M>>> SubAssign<T> for Fp<M> {
    fn sub_assign(&mut self, rhs: T) {
        let rhs = rhs.into().0;
        if self.0 < rhs {
            self.0 += M::P;
        }
        self.0 -= rhs;
    }
}
impl<M: Mod, T: Into<Fp<M>>> MulAssign<T> for Fp<M> {
    fn mul_assign(&mut self, rhs: T) {
        self.0 *= rhs.into().0;
        self.0 %= Self::P;
    }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl<M: Mod, T: Into<Fp<M>>> DivAssign<T> for Fp<M> {
    fn div_assign(&mut self, rhs: T) {
        *self *= rhs.into().inv();
    }
}
impl<M: Mod> Neg for Fp<M> {
    type Output = Fp<M>;
    fn neg(self) -> Self::Output {
        if self.0 == 0 {
            self
        } else {
            Self(Self::P - self.0, PhantomData)
        }
    }
}
impl<M: Mod> Neg for &Fp<M> {
    type Output = Fp<M>;
    fn neg(self) -> Self::Output {
        -*self
    }
}

macro_rules! forward_ops {
    ($((
        $trait:ident,
        $trait_assign:ident,
        $fn:ident,
        $fn_assign:ident$(,)?
    )),* $(,)?) => {$(
        impl<M: Mod> $trait_assign<&Fp<M>> for Fp<M> {
            fn $fn_assign(&mut self, rhs: &Fp<M>) {
                self.$fn_assign(*rhs);
            }
        }
        impl<M: Mod, T: Into<Fp<M>>> $trait<T> for Fp<M> {
            type Output = Fp<M>;
            fn $fn(mut self, rhs: T) -> Self::Output {
                self.$fn_assign(rhs.into());
                self
            }
        }
        impl<M: Mod> $trait<&Fp<M>> for Fp<M> {
            type Output = Fp<M>;
            fn $fn(self, rhs: &Fp<M>) -> Self::Output {
                self.$fn(*rhs)
            }
        }
        impl<M: Mod, T: Into<Fp<M>>> $trait<T> for &Fp<M> {
            type Output = Fp<M>;
            fn $fn(self, rhs: T) -> Self::Output {
                (*self).$fn(rhs.into())
            }
        }
        impl<M: Mod> $trait<&Fp<M>> for &Fp<M> {
            type Output = Fp<M>;
            fn $fn(self, rhs: &Fp<M>) -> Self::Output {
                (*self).$fn(*rhs)
            }
        }
    )*};
}
forward_ops! {
    (Add, AddAssign, add, add_assign),
    (Sub, SubAssign, sub, sub_assign),
    (Mul, MulAssign, mul, mul_assign),
    (Div, DivAssign, div, div_assign),
}
impl<M: Mod> Sum for Fp<M> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(0), |b, x| b + x)
    }
}
impl<M: Mod> Product for Fp<M> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(1), |b, x| b * x)
    }
}
impl<'a, M: Mod> Sum<&'a Self> for Fp<M> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new(0), |b, x| b + x)
    }
}
impl<'a, M: Mod> Product<&'a Self> for Fp<M> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new(1), |b, x| b * x)
    }
}

/// 階乗を順に返すイテレータを生成します。
///
/// # Examples
///
/// ```
/// use new_fp::{fact_iter, define_fp, fp};
/// define_fp!(13);
///
/// let mut fact = fact_iter::<M>();
/// assert_eq!(fact.next(), Some(fp!(1)));
/// assert_eq!(fact.next(), Some(fp!(1)));
/// assert_eq!(fact.next(), Some(fp!(2)));
/// assert_eq!(fact.next(), Some(fp!(6)));
/// assert_eq!(fact.next(), Some(fp!(24)));
/// ```
pub fn fact_iter<M: Mod>() -> impl Iterator<Item = Fp<M>> {
    (1..).scan(Fp::new(1), |state, x| {
        let ans = *state;
        *state *= x;
        Some(ans)
    })
}

/// 階乗とその逆数を前計算します。
///
/// # Examples
///
/// ```
/// use new_fp::{fact_build, define_fp, fp};
/// define_fp!(13);
///
/// let fact = fact_build::<M>(3);
/// assert_eq!(fact.0[0], vec![fp!(1), fp!(1), fp!(2)]);
/// assert_eq!(fact.0[1], vec![fp!(1), fp!(1), fp!(1; 2)]);
/// ```
///
#[allow(clippy::missing_panics_doc)]
pub fn fact_build<M: Mod>(n: usize) -> FactTable<M> {
    FactTable(if n == 0 {
        [Vec::new(), Vec::new()]
    } else {
        let fact = fact_iter::<M>().take(n).collect::<Vec<_>>();
        let mut fact_inv = vec![fact.last().unwrap().inv(); n];
        (1..n).rev().for_each(|i| fact_inv[i - 1] = fact_inv[i] * i);
        [fact, fact_inv]
    })
}

/// [`fact_build`] の戻り値型で、階乗とその逆数のテーブルを管理しています。
///
/// # Examples
///
/// ```
/// use new_fp::{fact_build, define_fp, fp};
/// define_fp!(13);
///
/// let fact = fact_build::<M>(4);
///
/// assert_eq!(fact.0[0], vec![fp!(1), fp!(1), fp!(2), fp!(6)]);
/// assert_eq!(fact.0[1], vec![fp!(1), fp!(1), fp!(1; 2), fp!(1; 6)]);
/// ```
///
///
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct FactTable<M: Mod>(pub [Vec<Fp<M>>; 2]);
impl<M: Mod> FactTable<M> {
    /// k ≤ n < len ならば binom(n, k) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_fp, fp};
    /// define_fp!(13);
    /// let fact = fact_build::<M>(5);
    ///
    /// assert_eq!(fact.binom(4, 0), fp!(1));
    /// assert_eq!(fact.binom(4, 1), fp!(4));
    /// assert_eq!(fact.binom(4, 2), fp!(6));
    /// ```
    pub fn binom(&self, n: usize, k: usize) -> Fp<M> {
        assert!(n < self.0[0].len());
        assert!(k <= n);
        self.0[0][n] * self.0[1][k] * self.0[1][n - k]
    }
    /// i + j < len ならば binom(i + j, i) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_fp, fp};
    /// define_fp!(13);
    /// let fact = fact_build::<M>(5);
    ///
    /// assert_eq!(fact.binom2(0, 4), fp!(1));
    /// assert_eq!(fact.binom2(1, 3), fp!(4));
    /// assert_eq!(fact.binom2(2, 2), fp!(6));
    /// ```
    pub fn binom2(&self, i: usize, j: usize) -> Fp<M> {
        self.binom(i + j, i)
    }
    /// 0 ≤ k ≤ n < len ならば 1 / binom(n, k) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_fp, fp};
    /// define_fp!(13);
    /// let fact = fact_build::<M>(5);
    ///
    /// assert_eq!(fact.binom_inv(4, 0), fp!(1; 1));
    /// assert_eq!(fact.binom_inv(4, 1), fp!(1; 4));
    /// assert_eq!(fact.binom_inv(4, 2), fp!(1; 6));
    /// ```
    pub fn binom_inv(&self, n: u64, k: u64) -> Fp<M> {
        let n = n as usize;
        let k = k as usize;
        assert!(n < self.0[0].len());
        assert!(k <= n);
        self.0[1][n] * self.0[0][k] * self.0[0][n - k]
    }
    /// 0 ≤ n < len ならば binom(n, k) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_fp, fp};
    /// define_fp!(13);
    /// let fact = fact_build::<M>(5);
    ///
    /// // `binom` と同じ
    /// assert_eq!(fact.binom_or_zero(4, 0), fp!(1));
    /// assert_eq!(fact.binom_or_zero(4, 1), fp!(4));
    /// assert_eq!(fact.binom_or_zero(4, 2), fp!(6));
    ///
    /// // `k` が範囲外なると `0` を返します。
    /// assert_eq!(fact.binom_or_zero(4, 5), fp!(0));
    /// assert_eq!(fact.binom_or_zero(4, -1), fp!(0));
    /// ```
    pub fn binom_or_zero(&self, n: usize, k: isize) -> Fp<M> {
        assert!(n < self.0[0].len() as usize);
        if (0..=n as isize).contains(&k) {
            self.binom(n, k as usize)
        } else {
            Fp::new(0)
        }
    }
}

/// 二項係数 binom(n, k) を、n ごとにまとめて返すイテレータを生成します。
///
/// # Examples
///
/// ```
/// use new_fp::{binom_iter, define_fp, fp};
/// define_fp!(13);
///
/// let mut binom = binom_iter::<M>();
/// assert_eq!(binom.next(), Some(vec![fp!(1)]));
/// assert_eq!(binom.next(), Some(vec![fp!(1), fp!(1)]));
/// assert_eq!(binom.next(), Some(vec![fp!(1), fp!(2), fp!(1)]));
/// assert_eq!(binom.next(), Some(vec![fp!(1), fp!(3), fp!(3), fp!(1)]));
/// ```
pub fn binom_iter<M: Mod>() -> impl Iterator<Item = Vec<Fp<M>>> {
    successors(Some(vec![Fp::new(1)]), |last| {
        let mut crr = last.clone();
        crr.push(Fp::new(0));
        crr[1..].iter_mut().zip(last).for_each(|(x, &y)| *x += y);
        Some(crr)
    })
}

/// [`fft`] を用いて畳み込み（多項式乗算）を行います。
///
/// # Examples
///
/// ```
/// use new_fp::{convolution, fp, F998244353 as F};
///
/// let a: Vec<F> = vec![fp!(1), fp!(2), fp!(3), fp!(4)];
/// let b: Vec<F> = vec![fp!(5), fp!(6), fp!(7), fp!(8), fp!(9)];
/// let c = convolution(a, b);
/// let expected: Vec<F> = vec![
///     fp!(5),
///     fp!(16),
///     fp!(34),
///     fp!(60),
///     fp!(70),
///     fp!(70),
///     fp!(59),
///     fp!(36),
/// ];
/// assert_eq!(&c, &expected);
/// ```
pub fn convolution<M: Fft>(mut a: Vec<Fp<M>>, mut b: Vec<Fp<M>>) -> Vec<Fp<M>> {
    if a.is_empty() || b.is_empty() {
        Vec::new()
    } else {
        let n = a.len() + b.len() - 1;
        a.resize(n.next_power_of_two(), Fp::new(0));
        b.resize(n.next_power_of_two(), Fp::new(0));
        fft(&mut a);
        fft(&mut b);
        let mut c = a.into_iter().zip(b).map(|(x, y)| x * y).collect::<Vec<_>>();
        ifft(&mut c);
        c.truncate(n);
        c
    }
}

/// 3 つの NTT-friendly 素数を用いて任意 mod でコンボリューションします。
///
/// # Examples
///
/// ```
/// use new_fp::{anymod_convolution, fp, define_fp};
/// define_fp!(71);
///
/// let a: Vec<F> = vec![fp!(1), fp!(2), fp!(3), fp!(4)];
/// let b: Vec<F> = vec![fp!(5), fp!(6), fp!(7), fp!(8), fp!(9)];
/// let c = anymod_convolution(&a, &b);
/// let expected: Vec<F> = vec![
///     fp!(5),
///     fp!(16),
///     fp!(34),
///     fp!(60),
///     fp!(70),
///     fp!(70),
///     fp!(59),
///     fp!(36),
/// ];
/// assert_eq!(&c, &expected);
/// ```
pub fn anymod_convolution<M: Mod>(a: &[Fp<M>], b: &[Fp<M>]) -> Vec<Fp<M>> {
    type Fp1 = F998244353;
    type Fp2 = F1012924417;
    type Fp3 = F924844033;
    let v1 = convolution(
        a.iter().map(|&x| Fp1::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp1::new(x.value())).collect::<Vec<_>>(),
    );
    let v2 = convolution(
        a.iter().map(|&x| Fp2::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp2::new(x.value())).collect::<Vec<_>>(),
    );
    let v3 = convolution(
        a.iter().map(|&x| Fp3::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp3::new(x.value())).collect::<Vec<_>>(),
    );
    v1.into_iter()
        .zip(v2)
        .zip(v3)
        .map(|((e1, e2), e3)| {
            let x1 = e1;
            let x2 = (e2 - Fp2::new(x1.value())) * Fp2::new(Fp1::P).inv();
            let x3 = ((e3 - Fp3::new(x1.value())) * Fp3::new(Fp1::P).inv() - Fp3::new(x2.value()))
                * Fp3::new(Fp2::P).inv();
            Fp::new(x1.value())
                + Fp::new(x2.value()) * Fp::new(Fp1::P)
                + Fp::new(x3.value()) * Fp::new(Fp1::P) * Fp::new(Fp2::P)
        })
        .collect::<Vec<_>>()
}
/// [`fft`] の逆関数です。
///
/// # Examples
///
/// ```
/// use new_fp::{define_fp, ifft, fp};
///
/// define_fp!(17, 3);
///
/// let r = fp!(13); // pow(3, 1/4)
/// let mut a = vec![
///     fp!(15),
///     fp!(-5),
///     fp!(-3) + r * fp!(-6),
///     fp!(-3) - r * fp!(-6),
/// ];
/// ifft(&mut a);
///
/// let expected: Vec<F> = vec![
///     fp!(1),
///     fp!(2),
///     fp!(4),
///     fp!(8),
/// ];
/// assert_eq!(&a, &expected);
/// ```
pub fn ifft<M: Fft>(a: &mut [Fp<M>]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    let root = Fp::ROOT.pow((M::P - 1) / a.len() as u64);
    let mut roots = successors(Some(root.inv()), |x| Some(x * x))
        .take(n.trailing_zeros() as usize + 1)
        .collect::<Vec<_>>();
    roots.reverse();
    let fourth = Fp::ROOT.pow((M::P - 1) / 4).inv();
    let mut quarter = 1_usize;
    if n.trailing_zeros() % 2 == 1 {
        for a in a.chunks_mut(2) {
            let x = a[0];
            let y = a[1];
            a[0] = x + y;
            a[1] = x - y;
        }
        quarter = 2;
    }
    while quarter != n {
        let fft_len = quarter * 4;
        let root = roots[fft_len.trailing_zeros() as usize];
        for a in a.chunks_mut(fft_len) {
            let mut c = Fp::new(1);
            for (((i, j), k), l) in (0..)
                .zip(quarter..)
                .zip(quarter * 2..)
                .zip(quarter * 3..)
                .take(quarter)
            {
                let c2 = c * c;
                let x = a[i] + c2 * a[j];
                let y = a[i] - c2 * a[j];
                let z = c * (a[k] + c2 * a[l]);
                let w = fourth * c * (a[k] - c2 * a[l]);
                a[i] = x + z;
                a[j] = y + w;
                a[k] = x - z;
                a[l] = y - w;
                c *= root;
            }
        }
        quarter = fft_len;
    }
    let d = Fp::from(a.len()).inv();
    a.iter_mut().for_each(|x| *x *= d);
}

/// 長さ２冪の配列のFFT を、ビットリバースを直さずに行います。
///
/// # Examples
///
/// ```
/// use new_fp::{define_fp, fft, fp};
///
/// define_fp!(17, 3);
///
/// let mut a: Vec<F> = vec![
///     fp!(1),
///     fp!(2),
///     fp!(4),
///     fp!(8),
/// ];
/// fft(&mut a);
///
/// // Mod 17 での３冪
/// //    i | 0  1  2  3  4  5  6  7  8 ...
/// // ---------------------------------
/// //  3^i | 1  3  9 10 13  5 15 11 16 ...
/// let r = fp!(13); // pow(3, 1/4)
///
/// let expected = vec![
///     fp!(15),
///     fp!(-5),
///     fp!(-3) + r * fp!(-6),
///     fp!(-3) - r * fp!(-6),
/// ];
/// assert_eq!(&a, &expected);
/// ```
pub fn fft<M: Fft>(a: &mut [Fp<M>]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    let mut root = Fp::ROOT.pow((M::P - 1) / a.len() as u64);
    let fourth = Fp::ROOT.pow((M::P - 1) / 4);
    let mut fft_len = n;
    while 4 <= fft_len {
        let quarter = fft_len / 4;
        for a in a.chunks_mut(fft_len) {
            let mut c = Fp::new(1);
            for (((i, j), k), l) in (0..)
                .zip(quarter..)
                .zip(quarter * 2..)
                .zip(quarter * 3..)
                .take(quarter)
            {
                let c2 = c * c;
                let x = a[i] + a[k];
                let y = a[j] + a[l];
                let z = a[i] - a[k];
                let w = fourth * (a[j] - a[l]);
                a[i] = x + y;
                a[j] = c2 * (x - y);
                a[k] = c * (z + w);
                a[l] = c2 * c * (z - w);
                c *= root;
            }
        }
        root *= root;
        root *= root;
        fft_len = quarter;
    }
    if fft_len == 2 {
        for a in a.chunks_mut(2) {
            let x = a[0];
            let y = a[1];
            a[0] = x + y;
            a[1] = x - y;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::iter::repeat_with;

    use rand::{prelude::StdRng, Rng, SeedableRng};

    use super::*;
    define_fp!(13);

    #[test]
    #[allow(unused_imports)]
    fn test_visibility() {
        mod internal {
            use super::*;
            define_fp! { 17; pub enum M17; pub type F17 }
            define_fp! { 19; pub enum M19; type _F19 }
        }
        use internal::*;
        assert_eq!(F17::P, 17);
        assert_eq!(M17::P, 17);
        assert_eq!(M19::P, 19);
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_fmt() {
        define_fp!(998244353);
        for num in 1..100_u64 {
            for den in 1..100_u64 {
                let x: F = fp!(num; den);
                let s = format!("{:?}", x);
                if num % den == 0 {
                    let restored = s.parse::<u64>().unwrap();
                    assert_eq!(num, den * restored);
                } else {
                    let v = s.split('/').collect::<Vec<_>>();
                    assert_eq!(v.len(), 2);
                    let a = v[0].parse::<u64>().unwrap();
                    let b = v[1].parse::<u64>().unwrap();
                    assert_eq!(num * b, den * a);
                }
            }
        }
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_add() {
        assert_eq!(F::new(6) + F::new(8), F::new(1));
        assert_eq!(F::new(6) + &F::new(8), F::new(1));
        assert_eq!(&F::new(6) + F::new(8), F::new(1));
        assert_eq!(&F::new(6) + &F::new(8), F::new(1));
        let mut a = F::new(6);
        a += Fp::new(8);
        assert_eq!(a, F::new(1));
        let mut a = F::new(6);
        a += &Fp::new(8);
        assert_eq!(a, F::new(1));
        let mut a = F::new(6);
        a += 8;
        assert_eq!(a, F::new(1));
        let mut a = F::new(6);
        a += 8_usize;
        assert_eq!(a, F::new(1));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_sub() {
        assert_eq!(F::new(6) - F::new(8), F::new(11));
        assert_eq!(F::new(6) - &F::new(8), F::new(11));
        assert_eq!(&F::new(6) - F::new(8), F::new(11));
        assert_eq!(&F::new(6) - &F::new(8), F::new(11));
        let mut a = F::new(6);
        a -= Fp::new(8);
        assert_eq!(a, F::new(11));
        let mut a = F::new(6);
        a -= &Fp::new(8);
        assert_eq!(a, F::new(11));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_mul() {
        assert_eq!(F::new(6) * F::new(8), F::new(9));
        assert_eq!(F::new(6) * &F::new(8), F::new(9));
        assert_eq!(&F::new(6) * F::new(8), F::new(9));
        assert_eq!(&F::new(6) * &F::new(8), F::new(9));
        let mut a = F::new(6);
        a *= Fp::new(8);
        assert_eq!(a, F::new(9));
        let mut a = F::new(6);
        a *= &Fp::new(8);
        assert_eq!(a, F::new(9));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_div() {
        assert_eq!(F::new(6) / F::new(8), F::new(4));
        assert_eq!(F::new(6) / &F::new(8), F::new(4));
        assert_eq!(&F::new(6) / F::new(8), F::new(4));
        assert_eq!(&F::new(6) / &F::new(8), F::new(4));
        let mut a = F::new(6);
        a /= Fp::new(8);
        assert_eq!(a, F::new(4));
        let mut a = F::new(6);
        a /= &Fp::new(8);
        assert_eq!(a, F::new(4));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_neg() {
        assert_eq!(-F::new(6), F::new(7));
        assert_eq!(-&F::new(6), F::new(7));
    }

    #[test]
    fn test_sum() {
        let a: [F; 3] = [fp!(10), fp!(11), fp!(12)];
        assert_eq!(a.iter().sum::<F>(), fp!(33));
        assert_eq!(a.iter().copied().sum::<F>(), fp!(33));
    }

    #[test]
    fn test_product() {
        let a: [F; 3] = [fp!(10), fp!(11), fp!(12)];
        assert_eq!(a.iter().product::<F>(), fp!(1320));
        assert_eq!(a.iter().copied().product::<F>(), fp!(1320));
    }

    #[test]
    fn test_primroot() {
        define_fp!(998244353, 3);
        assert_eq!(F::ROOT, fp!(3));
    }

    #[test]
    fn test_anymod_convolution() {
        type F = F1000000007;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let l = rng.gen_range(0..10);
            let m = rng.gen_range(0..10);
            let a = repeat_with(|| F::new(rng.gen_range(0..F::P)))
                .take(l)
                .collect::<Vec<_>>();
            let b = repeat_with(|| F::new(rng.gen_range(0..F::P)))
                .take(m)
                .collect::<Vec<_>>();
            let result = anymod_convolution(&a, &b);
            let expected = if a.is_empty() || b.is_empty() {
                Vec::new()
            } else {
                let mut c = vec![fp!(0); (l + m).saturating_sub(1)];
                for (i, &x) in a.iter().enumerate() {
                    for (j, &y) in b.iter().enumerate() {
                        c[i + j] += x * y;
                    }
                }
                c
            };
            assert_eq!(result, expected);
        }
    }
}
