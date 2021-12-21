//! ログのつく CHT です。
//!
//! # TODO
//!
//! - ログのつかない方
//! - 浮動小数点数
//! - Concave 版を -1 倍ではなく反転で
//! - 各アイテムのドキュメントを書く
//!
//! # できること
//!
//! - 本体: [`Cht`]
//! - マーカー
//!   - トレイト（ユーザーが実装する必要なし）: [`ConvexOrConcave`]
//!   - 凸: [`Convex`]
//!   - 凹: [`Concave`]
//! - 二次式
//!   - 式: [`Quadratic`]
//!   - 変数: [`X`]
//!
//!
//! # Examples
//!
//! ```
//! use cht::{Cht, Concave, X};
//!
//! // 初期化
//! // この時点で `eval`, `multieval` を呼ぶとパニックします。
//! let mut cht = Cht::<Concave>::new();
//!
//! // 1 + x + x^2 を追加
//! cht.add(1 + X + X * X);
//! assert_eq!(cht.multieval(0..5), vec![1, 3, 7, 13, 21]);
//!
//! // (1 - 2x) * (1 - 3x) - 5x^2 を追加
//! cht.add((1 - 2 * X) * (1 - 3 * X) - 5 * X * X);
//! assert_eq!(cht.multieval(0..5), vec![1, -3, -5, -5, -3]);
//! assert_eq!(cht.eval(-1), 1);
//! ```
//!

use std::{
    borrow::Borrow,
    collections::BTreeSet,
    fmt::Debug,
    i64::{MAX, MIN},
    marker::PhantomData,
    ops::{Add, Mul, Neg, Sub},
};

pub trait ConvexOrConcave {}
/// 凸関数を管理する方であるというマーカー
pub enum Convex {}
/// 凹関数を管理する方であるというマーカー
pub enum Concave {}
impl ConvexOrConcave for Convex {}
impl ConvexOrConcave for Concave {}

/// 本体
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Cht<C: ConvexOrConcave> {
    base: ChtBase,
    coeff_at_two: i64,
    __marker: PhantomData<fn(C) -> C>,
}
impl Cht<Convex> {
    pub fn new() -> Self {
        Self {
            base: Default::default(),
            coeff_at_two: 0,
            __marker: PhantomData,
        }
    }
    pub fn multieval(&self, xs: impl Iterator<Item = i64>) -> Vec<i64> {
        xs.map(|x| self.eval(x)).collect()
    }
    pub fn collect_lines(&self) -> Vec<(i64, i64)> {
        self.base
            .set
            .iter()
            .map(|&seg| (seg.line.p, -seg.line.q))
            .collect()
    }
    pub fn eval(&self, x: i64) -> i64 {
        self.base.eval(x) + self.coeff_at_two * x * x
    }
    pub fn add(&mut self, quadratic: Quadratic) {
        let Quadratic([zeroth, first, second]) = quadratic;
        if self.base.set.is_empty() {
            self.coeff_at_two = second;
        } else {
            assert_eq!(
                self.coeff_at_two, second,
                "added a expression with different `second` from the before.",
            )
        }
        self.base.add(first, zeroth)
    }
}
impl Cht<Concave> {
    pub fn new() -> Self {
        Self {
            base: Default::default(),
            coeff_at_two: 0,
            __marker: PhantomData,
        }
    }
    pub fn multieval(&self, xs: impl Iterator<Item = i64>) -> Vec<i64> {
        xs.map(|x| self.eval(x)).collect()
    }
    pub fn collect_lines(&self) -> Vec<(i64, i64)> {
        self.base
            .set
            .iter()
            .map(|&seg| (-seg.line.p, seg.line.q))
            .collect()
    }
    pub fn eval(&self, x: i64) -> i64 {
        -self.base.eval(x) + self.coeff_at_two * x * x
    }
    pub fn add(&mut self, quadratic: Quadratic) {
        let Quadratic([zeroth, first, second]) = quadratic;
        if self.base.set.is_empty() {
            self.coeff_at_two = second;
        } else {
            assert_eq!(
                self.coeff_at_two, second,
                "added a expression with different `second` from the before.",
            )
        }
        self.base.add(-first, -zeroth)
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq)]
struct ChtBase {
    set: BTreeSet<Segment>,
}
impl ChtBase {
    fn eval(&self, x: i64) -> i64 {
        assert!(
            !self.set.is_empty(),
            "empty maximum is the negative infinity"
        );
        self.set.range(Max(x)..).next().unwrap().line.eval(x)
    }
    pub fn add(&mut self, tilt: i64, intercept: i64) {
        let q = -intercept;
        let p = tilt;
        if !self.set.is_empty()
            && self.set.range(p..).next().map_or(false, |seg| {
                if seg.min.0 == MIN {
                    seg.line.p == p && seg.line.q <= q
                } else {
                    seg.line.q - seg.line.p * seg.min.0 <= q - p * seg.min.0
                }
            })
        {
            return;
        }
        self.set.take(&p);
        let line = Line { p, q };
        while let Some(&seg1) = self.set.range(..p).next_back() {
            if seg1.min.0 == MIN || line.eval(seg1.min.0) < seg1.line.eval(seg1.min.0) {
                break;
            }
            self.set.remove(&seg1);
        }
        while let Some(&seg1) = self.set.range(p..).next() {
            if seg1.max.0 == MAX || line.eval(seg1.max.0) < seg1.line.eval(seg1.max.0) {
                break;
            }
            self.set.remove(&seg1);
        }
        if let Some(&seg1) = self.set.range(..p).next_back() {
            self.set.remove(&seg1);
            match seg1.line.brace(line) {
                Err(x) => {
                    debug_assert!(seg1.min.0 < x);
                    self.set.insert(Segment {
                        max: Max(x),
                        ..seg1
                    });
                }
                Ok(brace) => {
                    if seg1.min.0 < brace.min.0 {
                        self.set.insert(Segment {
                            max: Max(brace.min.0),
                            ..seg1
                        });
                    }
                    self.set.insert(brace);
                }
            }
        }
        if let Some(&seg1) = self.set.range(p..).next() {
            self.set.remove(&seg1);
            match line.brace(seg1.line) {
                Err(x) => {
                    debug_assert!(x < seg1.max.0);
                    self.set.insert(Segment {
                        min: Min(x),
                        ..seg1
                    });
                }
                Ok(brace) => {
                    if brace.max.0 < seg1.max.0 {
                        self.set.insert(Segment {
                            min: Min(brace.max.0),
                            ..seg1
                        });
                    }
                    self.set.insert(brace);
                }
            }
        }
        let min = Min(self
            .set
            .range(..p)
            .next_back()
            .map_or(MIN, |seg1| seg1.max.0));
        let max = Max(self.set.range(p..).next().map_or(MAX, |seg1| seg1.min.0));
        if min.0 < max.0 {
            self.set.insert(Segment { line, min, max });
        }
    }
}

/// 変数
pub const X: Quadratic = Quadratic([0, 1, 0]);
#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
/// 二次式
pub struct Quadratic([i64; 3]);
impl Quadratic {
    pub fn eval(self, x: i64) -> i64 {
        self.0[0] + (self.0[1] + self.0[2] * x) * x
    }
    pub fn square(self) -> Self {
        self * self
    }
}
impl From<i64> for Quadratic {
    fn from(x: i64) -> Self {
        Self([x, 0, 0])
    }
}
impl Neg for Quadratic {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self([-self.0[0], -self.0[1], -self.0[2]])
    }
}
impl<T: Into<Self>> Add<T> for Quadratic {
    type Output = Self;
    fn add(self, rhs: T) -> Self::Output {
        let rhs = rhs.into();
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
        ])
    }
}
impl Add<Quadratic> for i64 {
    type Output = Quadratic;
    fn add(self, rhs: Quadratic) -> Self::Output {
        rhs.add(self)
    }
}
impl<T: Into<Self>> Sub<T> for Quadratic {
    type Output = Self;
    fn sub(self, rhs: T) -> Self::Output {
        let rhs = rhs.into();
        Self([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
        ])
    }
}
impl Sub<Quadratic> for i64 {
    type Output = Quadratic;
    fn sub(self, rhs: Quadratic) -> Self::Output {
        let lhs: Quadratic = self.into();
        Quadratic([
            lhs.0[0] - rhs.0[0],
            lhs.0[1] - rhs.0[1],
            lhs.0[2] - rhs.0[2],
        ])
    }
}
impl<T: Into<Self>> Mul<T> for Quadratic {
    type Output = Self;
    fn mul(self, rhs: T) -> Self::Output {
        let rhs = rhs.into();
        assert_eq!(self.0[1] * rhs.0[2] + self.0[2] * rhs.0[1], 0);
        assert_eq!(self.0[2] * rhs.0[2], 0);
        Self([
            self.0[0] * rhs.0[0],
            self.0[0] * rhs.0[1] + self.0[1] * rhs.0[0],
            self.0[0] * rhs.0[2] + self.0[1] * rhs.0[1] + self.0[2] * rhs.0[0],
        ])
    }
}
impl Mul<Quadratic> for i64 {
    type Output = Quadratic;
    fn mul(self, rhs: Quadratic) -> Self::Output {
        rhs.mul(self)
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
struct Min(i64);
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
struct Max(i64);
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
struct Line {
    p: i64,
    q: i64,
}
impl Line {
    fn eval(&self, x: i64) -> i64 {
        self.p * x - self.q
    }
    fn brace(self, other: Self) -> Result<Segment, i64> {
        let Self { p: p0, q: q0 } = self;
        let Self { p: p1, q: q1 } = other;
        debug_assert!(p0 < p1);
        let x0 = (q1 - q0).div_euclid(p1 - p0);
        if x0 * (p1 - p0) == (q1 - q0) {
            return Err(x0);
        }
        let x1 = x0 + 1;
        let p = (p1 * x1 - p0 * x0) - (q1 - q0);
        let q = (p1 - p0) * x0 * x1 - q1 * x0 + q0 * x1;
        debug_assert_eq!(p * x0 - q, p0 * x0 - q0);
        debug_assert_eq!(p * x1 - q, p1 * x1 - q1);
        Ok(Segment {
            line: Self { p, q },
            min: Min(x0),
            max: Max(x1),
        })
    }
}
#[derive(Clone, Default, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
struct Segment {
    line: Line,
    min: Min,
    max: Max,
}
impl Borrow<i64> for Segment {
    fn borrow(&self) -> &i64 {
        &self.line.p
    }
}
impl Borrow<Min> for Segment {
    fn borrow(&self) -> &Min {
        &self.min
    }
}
impl Borrow<Max> for Segment {
    fn borrow(&self) -> &Max {
        &self.max
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{prelude::StdRng, Rng, SeedableRng};

    #[test]
    fn test_brace_ok() {
        let l0 = Line { p: -2, q: -4 };
        let l1 = Line { p: 3, q: 3 };
        let expected = Ok(Segment {
            line: Line { p: 1, q: -1 },
            min: Min(1),
            max: Max(2),
        });
        assert_eq!(l0.brace(l1), expected);
    }

    #[test]
    fn test_brace_err() {
        let l0 = Line { p: -2, q: -4 };
        let l1 = Line { p: 3, q: 1 };
        let expected = Err(1);
        assert_eq!(l0.brace(l1), expected);
    }

    #[test]
    fn test_convex() {
        fn multieval(brute: &[Quadratic], xs: impl Iterator<Item = i64>) -> Vec<i64> {
            xs.map(|x| brute.iter().map(|&line| line.eval(x)).max().unwrap())
                .collect()
        }

        let mut input_max;
        let mut cht;
        let mut brute;
        macro_rules! insert {
            ($q:expr) => {
                let q: Quadratic = $q;

                // parameters
                let test_max = input_max * 3;
                let x_range = -test_max..=test_max;

                // mutate
                eprintln!("insert: {:?}", q);
                cht.add(q);
                brute.push(q);

                // lines
                eprintln!("lines: {:?}", &cht.collect_lines());

                // eval
                let result = cht.multieval(x_range.clone());
                let expected = multieval(&brute, x_range.clone());
                assert_eq!(result, expected, "eval");
            };
        }

        let mut rng = StdRng::seed_from_u64(42);
        for im in vec![0, 1, 3, 3, 5, 5, 10, 10, 100, 100] {
            input_max = im;
            eprintln!("Initialize");
            cht = Cht::<Convex>::new();
            brute = Vec::new();
            let second = rng.gen_range(-input_max..=input_max);
            for _ in 0..20 {
                let q = Quadratic([
                    rng.gen_range(-input_max..=input_max),
                    rng.gen_range(-input_max..=input_max),
                    second,
                ]);
                insert!(q);
            }
            eprintln!();
        }
    }

    #[test]
    fn test_concave() {
        fn multieval(brute: &[Quadratic], xs: impl Iterator<Item = i64>) -> Vec<i64> {
            xs.map(|x| brute.iter().map(|&line| line.eval(x)).min().unwrap())
                .collect()
        }

        let mut input_max;
        let mut cht;
        let mut brute;
        macro_rules! insert {
            ($q:expr) => {
                let q: Quadratic = $q;

                // parameters
                let test_max = input_max * 3;
                let x_range = -test_max..=test_max;

                // mutate
                eprintln!("insert: {:?}", q);
                cht.add(q);
                brute.push(q);

                // lines
                eprintln!("lines: {:?}", &cht.collect_lines());

                // eval
                let result = cht.multieval(x_range.clone());
                let expected = multieval(&brute, x_range.clone());
                assert_eq!(result, expected, "eval");
            };
        }

        let mut rng = StdRng::seed_from_u64(42);
        for im in vec![0, 1, 3, 3, 5, 5, 10, 10, 100, 100] {
            input_max = im;
            eprintln!("Initialize");
            cht = Cht::<Concave>::new();
            brute = Vec::new();
            let second = rng.gen_range(-input_max..=input_max);
            for _ in 0..20 {
                let q = Quadratic([
                    rng.gen_range(-input_max..=input_max),
                    rng.gen_range(-input_max..=input_max),
                    second,
                ]);
                insert!(q);
            }
            eprintln!();
        }
    }
}
