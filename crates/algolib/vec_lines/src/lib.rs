//! 傾き単調な直線の列を `Vec` で管理します。
use std::{convert::TryFrom, fmt::Debug, hash::Hash, marker::PhantomData};

pub type VecLinesDecreasing = VecLines<DecreasingTilt>;
pub type VecLinesIncreasing = VecLines<IncreasingTilt>;

/// 傾き単調な直線の列を `Vec` で管理します。
///
/// # 使い方
///
/// ```
/// # use vec_lines::VecLinesIncreasing;
/// // 傾きが単調増加な直線の列を管理します。
/// let mut lines = VecLinesIncreasing::new();
/// ```
///
/// # `VecLinesDecreasing` と `VecLinesIncreasing` の違いについて
///
/// * 不要直線除去のロジックは完全に同じ。
/// * 今の所、違うのは直線をは挿入するときの assertion のみ。
#[derive(Clone, Debug, Hash, PartialEq)]
pub struct VecLines<C: Constraint> {
    lines: Vec<Line>,
    _marker: PhantomData<fn(C) -> C>,
}
impl<C: Constraint> VecLines<C> {
    pub fn new() -> Self {
        Self {
            lines: Vec::new(),
            _marker: PhantomData,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }
    pub fn len(&self) -> usize {
        self.lines.len()
    }
    pub fn get(&self, index: usize) -> Option<Line> {
        self.lines.get(index).copied()
    }
    pub fn push(&mut self, line: [i64; 2]) {
        assert!(
            self.lines
                .last()
                .map_or(true, |prv| C::ok(*prv, Line(line))),
            "傾きの単調性に違反しています。"
        );
        self.lines.push(Line(line));
        while 3 <= self.lines.len()
            && weakly_convex(*<&[Line; 3]>::try_from(&self.lines[self.lines.len() - 3..]).unwrap())
        {
            let p = self.lines.pop().unwrap();
            self.lines.pop().unwrap();
            self.lines.push(p);
        }
    }
    pub fn iter<'a>(&'a self) -> impl 'a + Iterator<Item = Line> {
        self.lines.iter().copied()
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
pub struct Line([i64; 2]);
impl Line {
    pub fn eval(self, x: i64) -> i64 {
        self.0[0] * x + self.0[1]
    }
    pub fn into_coeff(self) -> [i64; 2] {
        self.0
    }
}

fn weakly_convex([Line([a0, b0]), Line([a1, b1]), Line([a2, b2])]: [Line; 3]) -> bool {
    (a2 - a1) * (b1 - b0) <= (a1 - a0) * (b2 - b1)
}

pub trait Constraint: Clone + Debug + Hash + PartialEq {
    fn ok(prv: Line, crr: Line) -> bool;
}
#[derive(Clone, Debug, Hash, PartialEq)]
pub enum DecreasingTilt {}
#[derive(Clone, Debug, Hash, PartialEq)]
pub enum IncreasingTilt {}
impl Constraint for DecreasingTilt {
    fn ok(Line([a0, _]): Line, Line([a1, _]): Line) -> bool {
        a0 >= a1
    }
}
impl Constraint for IncreasingTilt {
    fn ok(Line([a0, _]): Line, Line([a1, _]): Line) -> bool {
        a0 <= a1
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{VecLinesDecreasing, VecLinesIncreasing},
        rand::{prelude::StdRng, Rng, SeedableRng},
    };

    /*
    こちらの問題の本質部分です。

    COLOCON -Colopl programming contest 2018- Final（オープンコンテスト）
    C - スペースエクスプローラー高橋君
    https://atcoder.jp/contests/colopl2018-final-open/tasks/colopl2018_final_c
     */
    #[test]
    fn test_decreasing_tilt() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let mut lines = VecLinesDecreasing::new();
            let mut raw_lines = Vec::new();
            let n = rng.gen_range(1..20);
            for x in 0..n as i64 {
                let y = rng.gen_range(0..(n * n) as i64);
                let a = -2 * x;
                let b = x * x + y;
                raw_lines.push([a, b]);
                lines.push([a, b]);
            }
            let mut i = 0;
            for x in 0..n {
                let expected = lines.iter().map(|line| line.eval(x)).min().unwrap();
                let mut result = lines.get(i).unwrap().eval(x);
                while let Some(swp) = lines.get(i + 1).map(|line| line.eval(x)) {
                    if result <= swp {
                        break;
                    }
                    result = swp;
                    i += 1;
                }
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_increasing_tilt() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let mut lines = VecLinesIncreasing::new();
            let mut raw_lines = Vec::new();
            let n = rng.gen_range(1..20);
            for x in 0..n as i64 {
                let y = rng.gen_range(0..(n * n) as i64);
                let a = 2 * x;
                let b = x * x + y;
                raw_lines.push([a, b]);
                lines.push([a, b]);
            }
            crate::lg!(&lines);
            let mut i = 0;
            for x in 0..n {
                let expected = lines.iter().map(|line| line.eval(x)).max().unwrap();
                let mut result = lines.get(i).unwrap().eval(x);
                while let Some(swp) = lines.get(i + 1).map(|line| line.eval(x)) {
                    if swp <= result {
                        break;
                    }
                    result = swp;
                    i += 1;
                }
                crate::lg!(i, x, result);
                assert_eq!(result, expected);
            }
        }
    }
}

// dbg {{{
#[allow(dead_code)]
mod dbg {

    mod bitslice {
        use std::fmt::{self, Debug, Display, Formatter};

        pub struct BitSlice<'a>(pub &'a [bool]);

        impl<'a> Display for BitSlice<'a> {
            fn fmt(&self, w: &mut Formatter) -> fmt::Result {
                write!(
                    w,
                    "{}",
                    self.0
                        .iter()
                        .map(|&b| if b { '1' } else { '0' })
                        .collect::<String>()
                )
            }
        }
        impl<'a> Debug for BitSlice<'a> {
            fn fmt(&self, w: &mut Formatter) -> fmt::Result {
                write!(w, "{}", self)
            }
        }
    }
    mod table {
        use std::{
            fmt::{self, Debug, Formatter},
            marker::PhantomData,
        };

        pub fn table<T, U>(table: &[U]) -> Table<'_, T, U> {
            Table {
                _marker: PhantomData,
                table,
            }
        }

        pub struct Table<'a, T, U> {
            table: &'a [U],
            _marker: PhantomData<T>,
        }
        impl<'a, T, U> Clone for Table<'a, T, U> {
            fn clone(&self) -> Self {
                Self {
                    table: self.table,
                    _marker: PhantomData,
                }
            }
        }
        impl<'a, T, U> Copy for Table<'a, T, U> {}
        impl<'a, T, U> Debug for Table<'a, T, U>
        where
            T: Debug,
            U: AsRef<[T]>,
        {
            fn fmt(&self, w: &mut Formatter) -> fmt::Result {
                write!(w, "{:?}", self.by(|cell| format!("{:?}", cell)))
            }
        }
        impl<'a, T, U> Table<'a, T, U> {
            pub fn by<F>(self, f: F) -> TableF<'a, T, U, F>
            where
                T: Debug,
                U: AsRef<[T]>,
                F: Fn(&T) -> String,
            {
                TableF {
                    _marker: PhantomData,
                    table: self.table,
                    f,
                }
            }
        }

        pub struct TableF<'a, T, U, F> {
            pub _marker: PhantomData<T>,
            pub table: &'a [U],
            pub f: F,
        }
        impl<'a, T, U, F: Clone> Clone for TableF<'a, T, U, F> {
            fn clone(&self) -> Self {
                Self {
                    table: self.table,
                    _marker: PhantomData,
                    f: self.f.clone(),
                }
            }
        }
        impl<'a, T, U, F: Copy> Copy for TableF<'a, T, U, F> {}
        impl<'a, T, U, F> Debug for TableF<'a, T, U, F>
        where
            T: Debug,
            U: AsRef<[T]>,
            F: Fn(&T) -> String,
        {
            fn fmt(&self, w: &mut Formatter) -> fmt::Result {
                self.table
                    .iter()
                    .enumerate()
                    .try_for_each(|(row_index, row)| {
                        writeln!(
                            w,
                            "{:02}|{}",
                            row_index,
                            row.as_ref()
                                .iter()
                                .map(|cell| format!(" {}", (&self.f)(cell)))
                                .collect::<String>()
                        )
                    })
            }
        }
    }

    pub use {
        bitslice::BitSlice,
        table::{table, Table},
    };

    #[macro_export]
    macro_rules! lg {
        (@nl $value:expr) => {
            eprintln!("[{}:{}]", file!(), line!());
            match $value {
                value => {
                    eprint!("{:?}", &value);
                }
            }
        };
        (@contents $head:expr $(,)?) => {
            match $head {
                head => {
                    eprintln!(" {} = {:?}", stringify!($head), &head);
                }
            }
        };
        (@contents $head:expr $(,$tail:expr)+ $(,)?) => {
            match $head {
                head => {
                    eprint!(" {} = {:?},", stringify!($head), &head);
                }
            }
            $crate::lg!(@contents $($tail),*);
        };
        ($($expr:expr),* $(,)?) => {
            eprint!("[{}:{}]", file!(), line!());
            $crate::lg!(@contents $($expr),*)
        };
    }
}
// }}}
