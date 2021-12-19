use std::{
    borrow::Borrow,
    collections::BTreeSet,
    fmt::Debug,
    i64::{MAX, MIN},
    marker::PhantomData,
};

pub trait ConvexOrConcave {}
pub enum Convex {}
pub enum Concave {}
impl ConvexOrConcave for Convex {}
impl ConvexOrConcave for Concave {}

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct ConvexHullTrick<C: ConvexOrConcave> {
    base: ConvexHullTrickBase,
    __marker: PhantomData<fn(C) -> C>,
}
impl ConvexHullTrick<Convex> {
    pub fn new() -> Self {
        Self {
            base: Default::default(),
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
        self.base.eval(x)
    }
    pub fn lave(&self, p: i64) -> Option<i64> {
        self.base.lave(p)
    }
    pub fn insert(&mut self, tilt: i64, intercept: i64) -> bool {
        self.base.insert(tilt, intercept)
    }
}
impl ConvexHullTrick<Concave> {
    pub fn new() -> Self {
        Self {
            base: Default::default(),
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
        -self.base.eval(x)
    }
    pub fn lave(&self, p: i64) -> Option<i64> {
        assert_ne!(p, MIN);
        self.base.lave(-p).map(|q| -q)
    }
    pub fn insert(&mut self, tilt: i64, intercept: i64) -> bool {
        assert_ne!(tilt, MIN);
        assert_ne!(intercept, MIN);
        self.base.insert(-tilt, -intercept)
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct ConvexHullTrickBase {
    set: BTreeSet<Segment>,
}
impl ConvexHullTrickBase {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn eval(&self, x: i64) -> i64 {
        assert!(
            !self.set.is_empty(),
            "empty maximum is the negative infinity"
        );
        self.set.range(Max(x)..).next().unwrap().line.eval(x)
    }
    pub fn lave(&self, p: i64) -> Option<i64> {
        assert!(
            !self.set.is_empty(),
            "empty maximum is the negative infinity"
        );
        let &Segment {
            line: Line { p: p1, q: q1 },
            min: Min(min),
            max: _,
        } = self.set.range(p..).next()?;
        if min == MIN {
            if p1 == p {
                Some(q1)
            } else {
                None
            }
        } else {
            Some(q1 - (p1 - p) * min)
        }
    }
    pub fn insert(&mut self, tilt: i64, intercept: i64) -> bool {
        let q = -intercept;
        let p = tilt;
        if !self.set.is_empty() && self.lave(p).map_or(false, |c| c <= q) {
            return false;
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
        true
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
    use itertools::Itertools;
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
        fn multieval(brute: &[Line], xs: impl Iterator<Item = i64>) -> Vec<i64> {
            xs.map(|x| brute.iter().map(|&line| line.eval(x)).max().unwrap())
                .collect()
        }
        fn multilave(
            brute: &[Line],
            xy: &[(i64, i64)],
            ps: impl Iterator<Item = i64>,
        ) -> Vec<Option<i64>> {
            ps.map(|p| {
                if p < brute.iter().map(|&line| line.p).min().unwrap()
                    || brute.iter().map(|&line| line.p).max().unwrap() < p
                {
                    None
                } else {
                    Some(xy.iter().map(|&(x, y)| x * p - y).max().unwrap())
                }
            })
            .collect()
        }

        let mut input_max;
        let mut cht;
        let mut brute;
        macro_rules! insert {
            ($tilt:expr, $intercept:expr) => {
                let tilt: i64 = $tilt;
                let intercept: i64 = $intercept;

                // parameters
                let test_max = input_max * 3;
                let x_range = -test_max..=test_max;
                let p_range = -test_max..=test_max;

                // mutate
                eprintln!("insert: {}, {}", tilt, intercept);
                cht.insert(tilt, intercept);
                brute.push(Line {
                    p: tilt,
                    q: -intercept,
                });

                // lines
                eprintln!("lines: {:?}", &cht.collect_lines());

                // eval
                let result = cht.multieval(x_range.clone());
                let expected = multieval(&brute, x_range.clone());
                assert_eq!(result, expected, "eval");

                // lave
                let xy = x_range
                    .clone()
                    .zip(&expected)
                    .map(|(x, &y)| (x, y))
                    .collect_vec();
                let result = p_range.clone().map(|p| cht.lave(p)).collect_vec();
                let expected = multilave(&brute, &xy, p_range.clone());
                assert_eq!(result, expected, "lave");
            };
        }

        let mut rng = StdRng::seed_from_u64(42);
        for im in vec![0, 1, 3, 3, 5, 5, 10, 10, 100, 100] {
            input_max = im;
            eprintln!("Initialize");
            cht = ConvexHullTrick::<Convex>::new();
            brute = Vec::new();
            for _ in 0..20 {
                let tilt = rng.gen_range(-input_max..=input_max);
                let intercept = rng.gen_range(-input_max..=input_max);
                insert!(tilt, intercept);
            }
            eprintln!();
        }
    }

    #[test]
    fn test_concave() {
        fn multieval(brute: &[Line], xs: impl Iterator<Item = i64>) -> Vec<i64> {
            xs.map(|x| brute.iter().map(|&line| line.eval(x)).min().unwrap())
                .collect()
        }
        fn multilave(
            brute: &[Line],
            xy: &[(i64, i64)],
            ps: impl Iterator<Item = i64>,
        ) -> Vec<Option<i64>> {
            ps.map(|p| {
                if p < brute.iter().map(|&line| line.p).min().unwrap()
                    || brute.iter().map(|&line| line.p).max().unwrap() < p
                {
                    None
                } else {
                    Some(xy.iter().map(|&(x, y)| x * p - y).min().unwrap())
                }
            })
            .collect()
        }

        let mut input_max;
        let mut cht;
        let mut brute;
        macro_rules! insert {
            ($tilt:expr, $intercept:expr) => {
                let tilt: i64 = $tilt;
                let intercept: i64 = $intercept;

                // parameters
                let test_max = input_max * 3;
                let x_range = -test_max..=test_max;
                let p_range = -test_max..=test_max;

                // mutate
                eprintln!("insert: {}, {}", tilt, intercept);
                cht.insert(tilt, intercept);
                brute.push(Line {
                    p: tilt,
                    q: -intercept,
                });

                // lines
                eprintln!("lines: {:?}", &cht.collect_lines());

                assert_eq!(cht.base.set.iter().next().unwrap().min.0, MIN, "min");
                assert_eq!(cht.base.set.iter().next_back().unwrap().max.0, MAX, "max");

                // eval
                let result = cht.multieval(x_range.clone());
                let expected = multieval(&brute, x_range.clone());
                assert_eq!(result, expected, "eval");

                // lave
                let xy = x_range
                    .clone()
                    .zip(&expected)
                    .map(|(x, &y)| (x, y))
                    .collect_vec();
                let result = p_range.clone().map(|p| cht.lave(p)).collect_vec();
                let expected = multilave(&brute, &xy, p_range.clone());
                assert_eq!(result, expected, "lave");
            };
        }

        let mut rng = StdRng::seed_from_u64(42);
        for im in vec![0, 1, 3, 3, 5, 5, 10, 10, 100, 100] {
            input_max = im;
            eprintln!("Initialize");
            cht = ConvexHullTrick::<Concave>::new();
            brute = Vec::new();
            for _ in 0..20 {
                let tilt = rng.gen_range(-input_max..=input_max);
                let intercept = rng.gen_range(-input_max..=input_max);
                insert!(tilt, intercept);
            }
            eprintln!();
        }
    }
}
