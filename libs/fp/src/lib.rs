/// 自動素数 mod・高速フーリエ変換ライブラリ
///
use std::{
    fmt::{Debug, Display},
    hash::Hash,
    iter::{once, repeat, successors, FromIterator, Product, Sum},
    marker::PhantomData,
    mem::{swap, take},
    ops::{
        Add, AddAssign, Deref, DerefMut, Div, DivAssign, Index, Mul, MulAssign, Neg, Sub, SubAssign,
    },
};

// TODO: マクロで定義するとバンドラさんに壊されしまいます。
crate::define_fp! {
    const P: u64 = 1_000_000_007;
    pub type M1000000007 = M;
    pub type F1000000007 = F;
}
crate::define_fp! {
    const P: u64 = 998_244_353;
    const ROOT: u64 = 3;
    pub type M998244353 = M;
    pub type F998244353 = F;
    pub type Fps998244353 = Fps;
}
crate::define_fp! {
    const P: u64 = 1_012_924_417;
    const ROOT: u64 = 5;
    pub type M1012924417 = M;
    pub type F1012924417 = F;
    pub type Fps1012924417 = Fps;
}
crate::define_fp! {
    const P: u64 = 924_844_033;
    const ROOT: u64 = 5;
    pub type M924844033 = M;
    pub type F924844033= F;
    pub type Fps924844033 = Fps;
}

/// A wrapper trait of a modulus.
pub trait Mod {
    const P: u64;
}
/// A wrapper trait of a primitive root.
pub trait Fft: Mod {
    const ROOT: u64;
}

/// Define consts and types.
#[macro_export]
macro_rules! define_fp {
    (
        $visp:vis const P: u64 = $p:expr;
        $vism:vis type $m:ident = M;
        $visf:vis type $f:ident = F;
    ) => {
        #[allow(dead_code)]
        $vism enum $m {}
        impl $crate::Mod for $m {
            const P: u64 = $p;
        }
        #[allow(dead_code)]
        $visf type $f = $crate::Fp<$m>;
    };
    (
        $visp:vis const P: u64 = $p:expr;
        $visr:vis const ROOT: u64 = $root:expr;
        $vism:vis type $m:ident = M;
        $visf:vis type $f:ident = F;
        $visfps:vis type $fps:ident = Fps;
    ) => {
        $crate::define_fp! {
            $visp const P: u64 = $p;
            $vism type $m = M;
            $visf type $f = F;
        }
        impl $crate::Fft for $m {
            const ROOT: u64 = $root;
        }
        #[allow(dead_code)]
        $visfps type $fps = $crate::Fpsp<$m>;
    };
}

/// Creater an object of type [`Fp`].
///
/// # Examples
///
/// ```
/// use fp::{fp, define_fp};
/// define_fp! {
///     const P: u64 = 13;
///     type M = M;
///     type F = F;
/// }
///
/// let x: i16 = -3;
/// assert_eq!(fp!(x), F::new(10));
///
/// // Fractions
/// assert_eq!(fp!(2; 3), F::new(2) / F::new(3));
///
/// // Conditions
/// assert_eq!(fp!(2; if true), F::new(2));
/// assert_eq!(fp!(2; if false), F::new(0));
///
/// let mut called = false;
/// let mut f = || {
///     called = true;
///     2
/// };
/// assert_eq!(fp!(f(); if false), F::new(0));
/// assert!(!called); // f is not evaluated
///
/// let mut f = || {
///     called = true;
///     2
/// };
/// assert_eq!(fp!(f(); if true), F::new(2));
/// assert!(called); // f is evaluated
///
/// // Nested fp!s
/// let x: F = fp!(fp!(2));
/// assert_eq!(x / 3, fp!(2; 3));
/// ```
#[macro_export]
macro_rules! fp {
    ($value:expr; if $cond:expr) => {
        if $cond {
            fp!($value)
        } else {
            fp!(0)
        }
    };
    ($num:expr; $den:expr) => {
        $crate::Fp::from($num) / $crate::Fp::from($den)
    };
    ($value:expr) => {
        $crate::Fp::from($value)
    };
}
/// Create an object of [`Fpsp`].
///
/// # Examples
///
/// ```
/// use fp::{define_fp, fp, fps};
/// define_fp! {
///     const P: u64 = 17;
///     const ROOT: u64 = 3;
///     type M = M;
///     type F = F;
///     type Fps = Fps;
/// };
///
/// let _: Fps = fps![];
/// let _: Fps = fps![42];
/// let _: Fps = fps![42, 43];
/// let _: Fps = fps![42; 10];
///
/// let _: Fps = fps![fp!(42), fp!(43)];
/// let _: Fps = fps![fp!(42); 10];
///
/// let _: Fps = fps![fp!(42; 16), fp!(1), 6, fp!(fp!(4; 2)), F::new(4)];
/// ```
#[macro_export]
macro_rules! fps {
    () => (
        $crate::Fpsp(Vec::new())
    );
    ($elem:expr; $n:expr) => (
        $crate::Fpsp(vec![$crate::fp!($elem); $n])
    );
    ($($x:expr),+ $(,)?) => (
        $crate::Fpsp(vec![$($crate::fp!($x)),+])
    );
}

pub struct Fp<M>(u64, PhantomData<fn() -> M>);
impl<M: Fft> Fp<M> {
    /// The primitive root
    pub const ROOT: Self = Self(M::ROOT, PhantomData);
}
impl<M: Mod> Fp<M> {
    pub const P: u64 = M::P;
    pub fn new(value: u64) -> Self {
        Self(value % Self::P, PhantomData)
    }
    pub fn m1pow(pow: u32) -> Self {
        Self(
            match pow % 2 {
                0 => 1,
                1 => Self::P - 1,
                _ => unreachable!(),
            },
            PhantomData,
        )
    }
    pub fn value(self) -> u64 {
        self.0
    }
    pub fn inv(self) -> Self {
        assert_ne!(self.0, 0, "Cannot invert `0`.");
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
    u8, u16, u32, u64, bool,
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

macro_rules! fp_forward_ops {
    ($(
        $trait:ident,
        $trait_assign:ident,
        $fn:ident,
        $fn_assign:ident,
    )*) => {$(
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
fp_forward_ops! {
    Add, AddAssign, add, add_assign,
    Sub, SubAssign, sub, sub_assign,
    Mul, MulAssign, mul, mul_assign,
    Div, DivAssign, div, div_assign,
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

pub fn fact_iter<M: Mod>() -> impl Iterator<Item = Fp<M>> {
    (1..).scan(Fp::new(1), |state, x| {
        let ans = *state;
        *state *= x;
        Some(ans)
    })
}

#[allow(clippy::missing_panics_doc)]
pub fn fact_build<M: Mod>(n: usize) -> FactTable<M> {
    if n == 0 {
        FactTable(Vec::new(), Vec::new())
    } else {
        let fact = fact_iter::<M>().take(n).collect::<Vec<_>>();
        let mut fact_inv = vec![fact.last().unwrap().inv(); n];
        (1..n).rev().for_each(|i| fact_inv[i - 1] = fact_inv[i] * i);
        FactTable(fact, fact_inv)
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct FactTable<M: Mod>(pub Vec<Fp<M>>, pub Vec<Fp<M>>);
impl<M: Mod, I> Index<I> for FactTable<M>
where
    Vec<Fp<M>>: Index<I>,
{
    type Output = <Vec<Fp<M>> as Index<I>>::Output;
    fn index(&self, index: I) -> &Self::Output {
        &self.0[index]
    }
}
impl<M: Mod> FactTable<M> {
    pub fn binom(&self, n: usize, k: usize) -> Fp<M> {
        assert!(n < self.0.len());
        assert!(k <= n);
        self.0[n] * self.1[k] * self.1[n - k]
    }
    pub fn binom2(&self, i: usize, j: usize) -> Fp<M> {
        self.binom(i + j, i)
    }
    pub fn binom_inv(&self, n: u64, k: u64) -> Fp<M> {
        let n = n as usize;
        let k = k as usize;
        assert!(n < self.0.len());
        assert!(k <= n);
        self.1[n] * self.0[k] * self.0[n - k]
    }
    pub fn binom_or_zero(&self, n: usize, k: isize) -> Fp<M> {
        assert!(n < self.0.len());
        if (0..=n as isize).contains(&k) {
            self.binom(n, k as usize)
        } else {
            Fp::new(0)
        }
    }
}

pub fn binom_iter<M: Mod>() -> impl Iterator<Item = Vec<Fp<M>>> {
    successors(Some(vec![Fp::new(1)]), |last| {
        let mut crr = last.clone();
        crr.push(Fp::new(0));
        crr[1..].iter_mut().zip(last).for_each(|(x, &y)| *x += y);
        Some(crr)
    })
}

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

pub struct Fpsp<M>(pub Vec<Fp<M>>);
impl<M: Fft> Fpsp<M> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn truncated(&self, len: usize) -> Self {
        self.iter().copied().take(len).collect()
    }
    pub fn resized(&self, len: usize) -> Self {
        self.iter()
            .copied()
            .chain(repeat(fp!(0)))
            .take(len)
            .collect()
    }
    pub fn derivative(&self) -> Self {
        self.iter()
            .enumerate()
            .skip(1)
            .map(|(i, &x)| fp!(i) * x)
            .collect()
    }
    pub fn integral(&self) -> Self {
        once(fp!(0))
            .chain(self.iter().enumerate().map(|(i, &x)| x / fp!(i + 1)))
            .collect()
    }
    pub fn inv(&self, precision: usize) -> Self {
        assert!(
            !self.is_empty() && self[0] != fp!(0),
            "Cannot invert an FPS `0`"
        );
        newton_by(precision, self[0].inv(), |g, d| {
            (-&g * self.truncated(d) + 2) * g
        })
    }
    pub fn log(&self, precision: usize) -> Self {
        assert!(
            !self.is_empty() && self[0] == fp!(1),
            "Cannot take a log of an FPS with constant term other than `1`"
        );
        (self.derivative().truncated(precision) * self.inv(precision))
            .integral()
            .resized(precision)
    }
    pub fn exp(&self, precision: usize) -> Self {
        assert!(
            !self.is_empty() && self[0] == fp!(0),
            "Cannot take an exp of an FPS with constant term other than `0`"
        );
        newton_by(precision, fp!(1), |g, d| {
            (self.truncated(d) + 1 - g.log(d)) * g
        })
    }
}
pub fn newton_by<M: Fft>(
    precision: usize,
    init: Fp<M>,
    rec: impl Fn(Fpsp<M>, usize) -> Fpsp<M>,
) -> Fpsp<M> {
    let mut ans = Fpsp(vec![init]);
    while ans.len() != precision {
        let d = ans.len() * 2;
        ans = rec(ans, d).resized(d.min(precision))
    }
    ans
}
impl<M: Fft> Deref for Fpsp<M> {
    type Target = Vec<Fp<M>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<M: Fft> DerefMut for Fpsp<M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl<M: Fft> Clone for Fpsp<M> {
    fn clone(&self) -> Self {
        Self(self.to_vec())
    }
}
impl<M: Fft, T: Into<Fp<M>>> FromIterator<T> for Fpsp<M> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(iter.into_iter().map(Into::into).collect())
    }
}
impl<M: Fft> AddAssign<&Fpsp<M>> for Fpsp<M> {
    fn add_assign(&mut self, rhs: &Fpsp<M>) {
        self.0.iter_mut().zip(&rhs.0).for_each(|(x, &y)| *x += y);
        if self.len() < rhs.len() {
            self.0.extend(rhs.0[self.len()..].iter().copied());
        }
    }
}
impl<M: Fft> AddAssign<&Fp<M>> for Fpsp<M> {
    fn add_assign(&mut self, rhs: &Fp<M>) {
        if self.is_empty() {
            self.0.push(*rhs);
        } else {
            self[0] += *rhs;
        }
    }
}
impl<M: Fft> SubAssign<&Fpsp<M>> for Fpsp<M> {
    fn sub_assign(&mut self, rhs: &Fpsp<M>) {
        self.0.iter_mut().zip(&rhs.0).for_each(|(x, &y)| *x -= y);
        if self.len() < rhs.len() {
            self.0.extend(rhs.0[self.len()..].iter().map(|&x| -x));
        }
    }
}
impl<M: Fft> SubAssign<&Fp<M>> for Fpsp<M> {
    fn sub_assign(&mut self, rhs: &Fp<M>) {
        if self.is_empty() {
            self.0.push(-*rhs);
        } else {
            self[0] -= *rhs;
        }
    }
}
impl<M: Fft> Neg for Fpsp<M> {
    type Output = Fpsp<M>;
    fn neg(mut self) -> Self::Output {
        self.0.iter_mut().for_each(|x| *x = -*x);
        self
    }
}
impl<M: Fft> Neg for &Fpsp<M> {
    type Output = Fpsp<M>;
    fn neg(self) -> Self::Output {
        self.0.iter().map(|&x| -x).collect()
    }
}
macro_rules! fps_forward_ops_borrow {
    ($(
        $trait:ident,
        $trait_assign: ident,
        $fn:ident,
        $fn_assign:ident,
    )*) => {$(
        impl<M: Fft> $trait_assign for Fpsp<M> {
            fn $fn_assign(&mut self, rhs: Self) {
                self.$fn_assign(&rhs)
            }
        }
        impl<M: Fft, T: Into<Fp<M>>> $trait_assign<T> for Fpsp<M> {
            fn $fn_assign(&mut self, rhs: T) {
                self.$fn_assign(&rhs.into())
            }
        }
        impl<M: Fft> $trait for Fpsp<M> {
            type Output = Fpsp<M>;
            fn $fn(mut self, rhs: Fpsp<M>) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }
        impl<M: Fft> $trait<&Fpsp<M>> for Fpsp<M> {
            type Output = Fpsp<M>;
            fn $fn(mut self, rhs: &Fpsp<M>) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }
        impl<M: Fft> $trait<&Fp<M>> for Fpsp<M> {
            type Output = Fpsp<M>;
            fn $fn(mut self, rhs: &Fp<M>) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }
        impl<M: Fft, T: Into<Fp<M>>> $trait<T> for Fpsp<M> {
            type Output = Fpsp<M>;
            fn $fn(mut self, rhs: T) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }
    )*};
}
fps_forward_ops_borrow! {
    Add, AddAssign, add, add_assign,
    Sub, SubAssign, sub, sub_assign,
}
impl<M: Fft> Mul<Fpsp<M>> for Fpsp<M> {
    type Output = Fpsp<M>;
    fn mul(self, rhs: Fpsp<M>) -> Self::Output {
        Fpsp(convolution(self.0, rhs.0))
    }
}
impl<M: Fft> MulAssign<&Fp<M>> for Fpsp<M> {
    fn mul_assign(&mut self, rhs: &Fp<M>) {
        self.0.iter_mut().for_each(|x| *x *= *rhs);
    }
}
impl<M: Fft> MulAssign<Fpsp<M>> for Fpsp<M> {
    fn mul_assign(&mut self, rhs: Fpsp<M>) {
        *self = take(self).mul(rhs)
    }
}
impl<M: Fft, T: Into<Fp<M>>> MulAssign<T> for Fpsp<M> {
    fn mul_assign(&mut self, rhs: T) {
        self.mul_assign(&rhs.into());
    }
}
impl<M: Fft> Mul<&Fp<M>> for Fpsp<M> {
    type Output = Fpsp<M>;
    fn mul(mut self, rhs: &Fp<M>) -> Self::Output {
        self.mul_assign(rhs);
        self
    }
}
impl<M: Fft, T: Into<Fp<M>>> Mul<T> for Fpsp<M> {
    type Output = Fpsp<M>;
    fn mul(mut self, rhs: T) -> Self::Output {
        self.mul_assign(rhs);
        self
    }
}

impl<M: Fft> Debug for Fpsp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl<M: Fft> PartialEq for Fpsp<M> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
impl<M: Fft> Eq for Fpsp<M> {}
impl<M: Fft> Default for Fpsp<M> {
    fn default() -> Self {
        Self(Vec::new())
    }
}
impl<M: Fft> Hash for Fpsp<M> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use std::iter::repeat_with;
    type Fps = Fps998244353;

    define_fp! {
        const P: u64 = 13;
        type M13 = M;
        type F13 = F;
    }
    define_fp! {
        const P: u64 = 17;
        type M17 = M;
        type F17 = F;
    }
    define_fp! {
        const P: u64 = 19;
        type M19 = M;
        type F19 = F;
    }

    #[test]
    #[allow(unused_imports)]
    fn test_visibility() {
        assert_eq!(F17::P, 17);
        assert_eq!(M17::P, 17);
        assert_eq!(M19::P, 19);
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_fmt() {
        for num in 1..100_u64 {
            for den in 1..100_u64 {
                let x: F998244353 = fp!(num; den);
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
        assert_eq!(F13::new(6) + F13::new(8), F13::new(1));
        assert_eq!(F13::new(6) + &F13::new(8), F13::new(1));
        assert_eq!(&F13::new(6) + F13::new(8), F13::new(1));
        assert_eq!(&F13::new(6) + &F13::new(8), F13::new(1));
        let mut a = F13::new(6);
        a += F13::new(8);
        assert_eq!(a, F13::new(1));
        let mut a = F13::new(6);
        a += &F13::new(8);
        assert_eq!(a, F13::new(1));
        let mut a = F13::new(6);
        a += 8;
        assert_eq!(a, F13::new(1));
        let mut a = F13::new(6);
        a += 8_usize;
        assert_eq!(a, F13::new(1));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_sub() {
        assert_eq!(F13::new(6) - F13::new(8), F13::new(11));
        assert_eq!(F13::new(6) - &F13::new(8), F13::new(11));
        assert_eq!(&F13::new(6) - F13::new(8), F13::new(11));
        assert_eq!(&F13::new(6) - &F13::new(8), F13::new(11));
        let mut a = F13::new(6);
        a -= F13::new(8);
        assert_eq!(a, F13::new(11));
        let mut a = F13::new(6);
        a -= &F13::new(8);
        assert_eq!(a, F13::new(11));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_mul() {
        assert_eq!(F13::new(6) * F13::new(8), F13::new(9));
        assert_eq!(F13::new(6) * &F13::new(8), F13::new(9));
        assert_eq!(&F13::new(6) * F13::new(8), F13::new(9));
        assert_eq!(&F13::new(6) * &F13::new(8), F13::new(9));
        let mut a = F13::new(6);
        a *= F13::new(8);
        assert_eq!(a, F13::new(9));
        let mut a = F13::new(6);
        a *= &F13::new(8);
        assert_eq!(a, F13::new(9));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_div() {
        assert_eq!(F13::new(6) / F13::new(8), F13::new(4));
        assert_eq!(F13::new(6) / &F13::new(8), F13::new(4));
        assert_eq!(&F13::new(6) / F13::new(8), F13::new(4));
        assert_eq!(&F13::new(6) / &F13::new(8), F13::new(4));
        let mut a = F13::new(6);
        a /= F13::new(8);
        assert_eq!(a, F13::new(4));
        let mut a = F13::new(6);
        a /= &F13::new(8);
        assert_eq!(a, F13::new(4));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_neg() {
        assert_eq!(-F13::new(6), F13::new(7));
        assert_eq!(-&F13::new(6), F13::new(7));
    }

    #[test]
    fn test_sum() {
        let a: [F13; 3] = [fp!(10), fp!(11), fp!(12)];
        assert_eq!(a.iter().sum::<F13>(), fp!(33));
        assert_eq!(a.iter().copied().sum::<F13>(), fp!(33));
    }

    #[test]
    fn test_product() {
        let a: [F13; 3] = [fp!(10), fp!(11), fp!(12)];
        assert_eq!(a.iter().product::<F13>(), fp!(1320));
        assert_eq!(a.iter().copied().product::<F13>(), fp!(1320));
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

    #[test]
    #[allow(clippy::op_ref)]
    fn test_fps_add() {
        let result: Fps = fps![2, 3] + fps![4, 5];
        assert_eq!(result, fps![6, 8]);

        let result: Fps = fps![2, 3] + &fps![4, 5];
        assert_eq!(result, fps![6, 8]);

        let mut result: Fps = fps![2, 3];
        result += fps![4, 5];
        assert_eq!(result, fps![6, 8]);

        let mut result: Fps = fps![2, 3];
        result += &fps![4, 5];
        assert_eq!(result, fps![6, 8]);

        let result: Fps = fps![2, 3] + fps![4, -3];
        assert_eq!(result, fps![6, 0]);

        let result: Fps = fps![2, 3] + fps![-2, -3];
        assert_eq!(result, fps![0, 0]);

        let result: Fps = fps![2, 3] + fps![4, 5, 6];
        assert_eq!(result, fps![6, 8, 6]);

        let result: Fps = fps![2, 3, 4] + fps![4, 5];
        assert_eq!(result, fps![6, 8, 4]);

        let result: Fps = fps![] + fps![];
        assert_eq!(result, fps![]);

        let result: Fps = fps![2, 3, 4] + fp!(3);
        assert_eq!(result, fps![5, 3, 4]);

        let result: Fps = fps![2, 3, 4] + 3;
        assert_eq!(result, fps![5, 3, 4]);

        let result: Fps = fps![2, 3, 4] + &fp!(3);
        assert_eq!(result, fps![5, 3, 4]);

        let mut result: Fps = fps![2, 3, 4];
        result += fp!(3);
        assert_eq!(result, fps![5, 3, 4]);

        let mut result: Fps = fps![2, 3, 4];
        result += 3;
        assert_eq!(result, fps![5, 3, 4]);

        let mut result: Fps = fps![2, 3, 4];
        result += &fp!(3);
        assert_eq!(result, fps![5, 3, 4]);
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_fps_sub() {
        let result: Fps = fps![2, 3] - fps![4, 5];
        assert_eq!(result, fps![-2, -2]);

        let result: Fps = fps![2, 3] - &fps![4, 5];
        assert_eq!(result, fps![-2, -2]);

        let mut result: Fps = fps![2, 3];
        result -= fps![4, 5];
        assert_eq!(result, fps![-2, -2]);

        let mut result: Fps = fps![2, 3];
        result -= &fps![4, 5];
        assert_eq!(result, fps![-2, -2]);

        let result: Fps = fps![2, 3] - fps![4, 3];
        assert_eq!(result, fps![-2, 0]);

        let result: Fps = fps![2, 3] - fps![2, 3];
        assert_eq!(result, fps![0, 0]);

        let result: Fps = fps![2, 3] - fps![4, 5, 6];
        assert_eq!(result, fps![-2, -2, -6]);

        let result: Fps = fps![2, 3, 4] - fps![4, 5];
        assert_eq!(result, fps![-2, -2, 4]);

        let result: Fps = fps![] - fps![];
        assert_eq!(result, fps![]);

        let result: Fps = fps![2, 3, 4] - fp!(3);
        assert_eq!(result, fps![-1, 3, 4]);

        let result: Fps = fps![2, 3, 4] - 3;
        assert_eq!(result, fps![-1, 3, 4]);

        let result: Fps = fps![2, 3, 4] - &fp!(3);
        assert_eq!(result, fps![-1, 3, 4]);

        let mut result: Fps = fps![2, 3, 4];
        result -= fp!(3);
        assert_eq!(result, fps![-1, 3, 4]);

        let mut result: Fps = fps![2, 3, 4];
        result -= 3;
        assert_eq!(result, fps![-1, 3, 4]);

        let mut result: Fps = fps![2, 3, 4];
        result -= &fp!(3);
        assert_eq!(result, fps![-1, 3, 4]);
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_fps_mul() {
        let result: Fps = fps![2, 3] * fps![4, 5];
        assert_eq!(result, fps![8, 22, 15]);

        let result: Fps = fps![2, 3] * fp![4];
        assert_eq!(result, fps![8, 12]);

        let result: Fps = fps![2, 3] * &fp![4];
        assert_eq!(result, fps![8, 12]);

        let result: Fps = fps![2, 3] * 4;
        assert_eq!(result, fps![8, 12]);

        let mut result: Fps = fps![2, 3];
        result *= fps![4, 5];
        assert_eq!(result, fps![8, 22, 15]);

        let mut result: Fps = fps![2, 3];
        result *= fps![4];
        assert_eq!(result, fps![8, 12]);

        let mut result: Fps = fps![2, 3];
        result *= 4;
        assert_eq!(result, fps![8, 12]);
    }

    #[test]
    fn test_inv() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let l = rng.gen_range(0..10);
            let m = rng.gen_range(0..10);
            let a = repeat_with(|| F998244353::new(rng.gen_range(0..F998244353::P)))
                .take(l)
                .collect::<Fps>();
            if l == 0 || m == 0 || a[0] == fp!(0) {
                continue;
            }
            let result = a.inv(m);
            let should_be_one = (a * result).resized(m);
            let mut expected = fps![0; m];
            expected[0] = fp!(1);
            assert_eq!(should_be_one, expected);
        }
    }

    #[test]
    fn test_exp() {
        fn brute(a: &Fps, precision: usize) -> Fps {
            let mut aug = fps![1];
            let mut ans = Fps::new();
            for i in 0..precision {
                ans += &aug;
                aug = (aug * a.clone() * fp!(1; i + 1)).truncated(precision);
            }
            ans.resized(precision)
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let l = rng.gen_range(1..10);
            let m = rng.gen_range(0..10);
            let a = once(fp!(0))
                .chain(repeat_with(|| {
                    F998244353::new(rng.gen_range(0..F998244353::P))
                }))
                .take(l)
                .collect::<Fps>();
            let result = a.exp(m);
            let expected = brute(&a, m);
            assert_eq!(&result, &expected);
        }
    }
}
