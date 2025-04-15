//! CHT です。
//!
//! # TODO
//!
//! - 浮動小数点数
//!   - ないと困ります
//! - 各アイテムのドキュメントを書く
//! - [`VecCht`] のカーソル管理もう少し上手にできないですかね
//!
//!
//! # WON'T DO
//!
//! - 凸探索付き平衡二分木を自作して、直線の式だけ管理すれば良いようにする
//!   - 理由: 大変そう
//!
//!
//! # できること
//!
//! ２次の係数のすべて等しいような、区分的に２次関数であるような、凸/凹関数を管理します。
//!
//! - 本体
//!   - ログ付き: [`BTreeCht`]
//!   - ログなし: [`VecCht`]
//!     - 前挿入は、いらないですか…
//!     - カーソルを１つだけ持っています。２つ以上はいらないですかね……どうしてもならオブジェクトごと２つ作ればできなくはないです。
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
//! use cht::BTreeCht;
//! use cht::Concave;
//! use cht::X;
//!
//! // 初期化
//! // この時点で `eval`, `multieval` を呼ぶとパニックします。
//! let mut cht = BTreeCht::<Concave>::new();
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

use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::i64::MAX;
use std::i64::MIN;
use std::marker::PhantomData;
use std::ops::Add;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Sub;

/// [`BTreeCht`], [`VecCht`] が凸関数を管理するか、凹関数を管理するかを表すマーカーのトレイト
pub trait ConvexOrConcave: Copy {
    fn negate_if_concave(x: i64) -> i64;
}
/// 凸関数を管理する方であるというマーカー
#[derive(Clone, Debug, Hash, Copy)]
pub enum Convex {}
#[derive(Clone, Debug, Hash, Copy)]
/// 凹関数を管理する方であるというマーカー
pub enum Concave {}
impl ConvexOrConcave for Convex {
    fn negate_if_concave(x: i64) -> i64 {
        x
    }
}
impl ConvexOrConcave for Concave {
    fn negate_if_concave(x: i64) -> i64 {
        -x
    }
}

/// ログがつかない方
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct VecCht<C> {
    vec: Vec<Segment>,
    coeff_at_two: i64,
    current: usize,
    __marker: PhantomData<fn() -> C>,
}
impl<C: ConvexOrConcave> VecCht<C> {
    pub fn new() -> Self {
        Self {
            vec: Vec::new(),
            coeff_at_two: 0,
            current: 0,
            __marker: PhantomData,
        }
    }

    pub fn multieval(&mut self, xs: impl Iterator<Item = i64>) -> Vec<i64> {
        let orig_current = self.current;
        self.current = 0;
        let res = xs.map(|x| self.eval(x)).collect();
        self.current = orig_current;
        res
    }

    pub fn eval(&mut self, x: i64) -> i64 {
        assert!(!self.vec.is_empty(), "cannot eval an empty cht");
        while self
            .vec
            .get(self.current)
            .map_or(false, |last| Min(x) <= last.min)
        {
            self.current -= 1;
        }
        while self.vec[self.current].max <= Max(x) {
            self.current += 1;
        }
        C::negate_if_concave(self.vec[self.current].line.eval(x)) + self.coeff_at_two * x * x
    }

    pub fn add(&mut self, quadratic: Quadratic) {
        let Quadratic([zeroth, first, second]) = quadratic;
        if self.vec.is_empty() {
            self.coeff_at_two = second;
        } else {
            assert_eq!(
                self.coeff_at_two, second,
                "added a expression with different `second` from the before.",
            );
        }

        let p = C::negate_if_concave(first);
        let q = C::negate_if_concave(-zeroth);
        let line = Line { p, q };
        if let Some(&seg) = self.vec.last() {
            if seg.line.p == p {
                if seg.line.q <= q {
                    return;
                }
                self.vec.pop().unwrap();
            }
        }

        while let Some(seg) = self.vec.pop() {
            let Min(x) = seg.min;
            if x == MIN || line.eval(x) < seg.line.eval(x) {
                self.vec.push(seg);
                break;
            }
        }
        if let Some(seg) = self.vec.pop() {
            match brace(seg.line, line) {
                Err(x) => self.vec.push(Segment { max: Max(x), ..seg }),
                Ok(brace) => {
                    if seg.min.0 < brace.min.0 {
                        self.vec.push(Segment {
                            max: Max(brace.min.0),
                            ..seg
                        });
                    }
                    self.vec.push(brace);
                }
            }
        }
        let min = Min(self.vec.last().map_or(MIN, |seg| seg.max.0));
        self.vec.push(Segment {
            line,
            min,
            max: Max(MAX),
        });
    }
}

/// ログがつく方
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct BTreeCht<C> {
    set: BTreeSet<Segment>,
    coeff_at_two: i64,
    __marker: PhantomData<fn() -> C>,
}
impl<C: ConvexOrConcave> BTreeCht<C> {
    pub fn new() -> Self {
        Self {
            set: BTreeSet::new(),
            coeff_at_two: 0,
            __marker: PhantomData,
        }
    }

    pub fn multieval(&self, xs: impl Iterator<Item = i64>) -> Vec<i64> {
        xs.map(|x| self.eval(x)).collect()
    }

    pub fn eval(&self, x: i64) -> i64 {
        assert!(!self.set.is_empty(), "cannot eval an empty cht");
        C::negate_if_concave(self.set.range(Max(x)..).next().unwrap().line.eval(x))
            + self.coeff_at_two * x * x
    }

    pub fn add(&mut self, quadratic: Quadratic) {
        let Quadratic([zeroth, first, second]) = quadratic;
        if self.set.is_empty() {
            self.coeff_at_two = second;
        } else {
            assert_eq!(
                self.coeff_at_two, second,
                "added a expression with different `second` from the before.",
            );
        }

        let p = C::negate_if_concave(first);
        let q = C::negate_if_concave(-zeroth);
        let line = Line { p, q };
        if let Some(seg) = self.set.range(p..).next() {
            let Min(x) = seg.min;
            if x == MIN && seg.line.p == p && seg.line.q <= q
                || x != MIN && line.eval(x) <= seg.line.eval(x)
            {
                return;
            }
        }

        self.set.take(&p);

        while let Some(&seg) = self.set.range(..p).next_back() {
            let Min(x) = seg.min;
            if x == MIN || line.eval(x) < seg.line.eval(x) {
                break;
            }
            self.set.remove(&seg);
        }
        while let Some(&seg) = self.set.range(p..).next() {
            let Max(x) = seg.max;
            if x == MAX || line.eval(x) < seg.line.eval(x) {
                break;
            }
            self.set.remove(&seg);
        }
        if let Some(&seg) = self.set.range(..p).next_back() {
            self.set.remove(&seg);
            match brace(seg.line, line) {
                Err(x) => self.set.insert(Segment { max: Max(x), ..seg }),
                Ok(brace) => {
                    if seg.min.0 < brace.min.0 {
                        self.set.insert(Segment {
                            max: Max(brace.min.0),
                            ..seg
                        });
                    }
                    self.set.insert(brace)
                }
            };
        }
        if let Some(&seg) = self.set.range(p..).next() {
            self.set.remove(&seg);
            match brace(line, seg.line) {
                Err(x) => self.set.insert(Segment { min: Min(x), ..seg }),
                Ok(brace) => {
                    if brace.max.0 < seg.max.0 {
                        self.set.insert(Segment {
                            min: Min(brace.max.0),
                            ..seg
                        });
                    }
                    self.set.insert(brace)
                }
            };
        }
        let min = Min(self.set.range(..p).next_back().map_or(MIN, |seg| seg.max.0));
        let max = Max(self.set.range(p..).next().map_or(MAX, |seg| seg.min.0));
        if min.0 < max.0 {
            self.set.insert(Segment { line, min, max });
        }
    }
}

/// 変数
pub const X: Quadratic = Quadratic([0, 1, 0]);
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, Copy)]
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
}
fn brace(l0: Line, l1: Line) -> Result<Segment, i64> {
    let Line { p: p0, q: q0 } = l0;
    let Line { p: p1, q: q1 } = l1;
    let x = (q1 - q0).div_euclid(p1 - p0);
    if l0.eval(x) == l1.eval(x) {
        Err(x)
    } else {
        let (x0, x1) = (x, x + 1);
        let p = l1.eval(x1) - l0.eval(x0);
        let q = p * x0 - l0.eval(x0);
        Ok(Segment {
            line: Line { p, q },
            min: Min(x0),
            max: Max(x1),
        })
    }
}
#[derive(Clone, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
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
impl Borrow<Max> for Segment {
    fn borrow(&self) -> &Max {
        &self.max
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter::from_fn;

    #[test]
    fn test_brace_ok_convex() {
        let l0 = Line { p: -2, q: -4 };
        let l1 = Line { p: 3, q: 3 };
        let expected = Ok(Segment {
            line: Line { p: 1, q: -1 },
            min: Min(1),
            max: Max(2),
        });
        assert_eq!(brace(l0, l1), expected);
    }

    #[test]
    fn test_brace_err_convex() {
        let l0 = Line { p: -2, q: -4 };
        let l1 = Line { p: 3, q: 1 };
        let expected = Err(1);
        assert_eq!(brace(l0, l1), expected);
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

                // eval
                let result = cht.multieval(x_range.clone());
                let expected = multieval(&brute, x_range.clone());
                assert_eq!(result, expected, "eval");
            };
        }

        let mut rng = StdRng::seed_from_u64(42);
        for &im in &[0, 1, 3, 3, 5, 5, 10, 10, 100, 100] {
            input_max = im;
            eprintln!("Initialize");
            cht = BTreeCht::<Convex>::new();
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

                // eval
                let result = cht.multieval(x_range.clone());
                let expected = multieval(&brute, x_range.clone());
                assert_eq!(result, expected, "eval");
            };
        }

        let mut rng = StdRng::seed_from_u64(42);
        for &im in &[0, 1, 3, 3, 5, 5, 10, 10, 100, 100] {
            input_max = im;
            eprintln!("Initialize");
            cht = BTreeCht::<Concave>::new();
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
    fn test_vec_convex() {
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
                cht.add(q);
                brute.push(q);

                // eval
                let result = cht.multieval(x_range.clone());
                let expected = multieval(&brute, x_range.clone());
                assert_eq!(result, expected, "eval");
            };
        }

        let mut rng = StdRng::seed_from_u64(42);
        for &im in &[0, 1, 3, 3, 5, 5, 10, 10, 100, 100] {
            input_max = im;
            eprintln!("Initialize");
            cht = VecCht::<Convex>::new();
            brute = Vec::new();
            let second = rng.gen_range(-input_max..=input_max);

            let queries = from_fn(|| {
                Some(Quadratic([
                    rng.gen_range(-input_max..=input_max),
                    rng.gen_range(-input_max..=input_max),
                    second,
                ]))
            })
            .take(20)
            .sorted_by_key(|q| q.0[1])
            .collect_vec();
            for q in queries {
                insert!(q);
            }
            eprintln!();
        }
    }
}
