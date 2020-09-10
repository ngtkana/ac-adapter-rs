#![allow(dead_code)]
// dbg {{{
#[allow(dead_code)]
mod dbg {
    #[macro_export]
    macro_rules! lg {
        () => {
            $crate::eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
        };
        ($val:expr) => {
            match $val {
                tmp => {
                    eprintln!("[{}:{}] {} = {:?}",
                        file!(), line!(), stringify!($val), &tmp);
                    tmp
                }
            }
        };
        ($val:expr,) => { lg!($val) };
        ($($val:expr),+ $(,)?) => {
            ($(lg!($val)),+,)
        };
    }

    #[macro_export]
    macro_rules! lg_nl {
        () => {
            $crate::eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
        };
        ($val:expr) => {
            match $val {
                tmp => {
                    eprintln!("[{}:{}] {}:\n{:?}", file!(), line!(), stringify!($val), tmp);
                    tmp
                }
            };
        };
    }

    #[macro_export]
    macro_rules! msg {
        () => {
            compile_error!();
        };
        ($msg:expr) => {
            $crate::eprintln!("[{}:{}][{}]", $crate::file!(), $crate::line!(), $msg);
        };
        ($msg:expr, $val:expr) => {
            match $val {
                tmp => {
                    eprintln!("[{}:{}][{}] {} = {:?}",
                        file!(), line!(), $msg, stringify!($val), &tmp);
                    tmp
                }
            }
        };
        ($msg:expr, $val:expr,) => { msg!($msg, $val) };
        ($msg:expr, $($val:expr),+ $(,)?) => {
            ($(msg!($msg, $val)),+,)
        };
    }

    #[macro_export]
    macro_rules! tabular {
        ($val:expr) => {
            lg_nl!(crate::dbg::Tabular($val))
        };
    }

    #[macro_export]
    macro_rules! boolean_table {
        ($val:expr) => {
            lg_nl!(crate::dbg::BooleanTable($val));
        };
    }

    #[macro_export]
    macro_rules! boolean_slice {
        ($val:expr) => {
            lg!(crate::dbg::BooleanSlice($val));
        };
    }

    use std::fmt::{Debug, Formatter};

    #[derive(Clone)]
    pub struct Tabular<'a, T: Debug>(pub &'a [T]);
    impl<'a, T: Debug> Debug for Tabular<'a, T> {
        fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
            for i in 0..self.0.len() {
                writeln!(f, "{:2} | {:?}", i, &self.0[i])?;
            }
            Ok(())
        }
    }

    #[derive(Clone)]
    pub struct BooleanTable<'a>(pub &'a [Vec<bool>]);
    impl<'a> Debug for BooleanTable<'a> {
        fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
            for i in 0..self.0.len() {
                writeln!(f, "{:2} | {:?}", i, BooleanSlice(&self.0[i]))?;
            }
            Ok(())
        }
    }

    #[derive(Clone)]
    pub struct BooleanSlice<'a>(pub &'a [bool]);
    impl<'a> Debug for BooleanSlice<'a> {
        fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
            write!(
                f,
                "{}",
                self.0
                    .iter()
                    .map(|&b| if b { "1 " } else { "0 " })
                    .collect::<String>()
            )?;
            Ok(())
        }
    }
}
// }}}
// span {{{
#[allow(dead_code)]
mod span {
    use std::{cmp, ops};

    impl<T> Span<T> for [T] {
        #[inline]
        fn span_len(&self) -> usize {
            self.len()
        }

        #[inline]
        fn span_is_empty(&self) -> bool {
            self.is_empty()
        }

        #[inline]
        fn span_sort(&mut self)
        where
            T: cmp::Ord,
        {
            self.sort()
        }

        #[inline]
        fn span_sort_by<F>(&mut self, compare: F)
        where
            F: FnMut(&T, &T) -> cmp::Ordering,
        {
            self.sort_by(compare)
        }

        #[inline]
        fn span_sort_by_key<K, F>(&mut self, f: F)
        where
            F: FnMut(&T) -> K,
            K: cmp::Ord,
        {
            self.sort_by_key(f)
        }
    }

    pub trait Span<T>: ops::Index<usize, Output = T> {
        fn span_len(&self) -> usize;

        fn span_is_empty(&self) -> bool {
            self.span_len() == 0
        }

        fn span_sort(&mut self)
        where
            T: cmp::Ord;

        fn span_sort_by<F>(&mut self, compare: F)
        where
            F: FnMut(&T, &T) -> cmp::Ordering;

        fn span_sort_by_key<K, F>(&mut self, f: F)
        where
            F: FnMut(&T) -> K,
            K: cmp::Ord;

        fn sort_reverse(&mut self)
        where
            T: cmp::Ord,
        {
            self.span_sort_by(|a, b| a.cmp(b).reverse())
        }

        fn sort_reverse_by<F>(&mut self, mut compare: F)
        where
            F: FnMut(&T, &T) -> cmp::Ordering,
        {
            self.span_sort_by(|a, b| compare(a, b).reverse())
        }

        fn sort_reverse_by_key<K, F>(&mut self, mut f: F)
        where
            F: FnMut(&T) -> K,
            K: cmp::Ord,
        {
            self.span_sort_by_key(|x| cmp::Reverse(f(x)))
        }

        #[inline]
        fn lower_bound<'a>(&'a self, x: &Self::Output) -> usize
        where
            T: Ord,
        {
            self.lower_bound_by(|p| p.cmp(x))
        }

        #[inline]
        fn lower_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
        where
            F: FnMut(&T) -> B,
            B: Ord,
        {
            self.lower_bound_by(|x| f(x).cmp(b))
        }

        #[inline]
        fn lower_bound_by<F>(&self, mut f: F) -> usize
        where
            F: FnMut(&T) -> cmp::Ordering,
        {
            self.span_partition_point(|x| f(x) == cmp::Ordering::Less)
        }

        #[inline]
        fn upper_bound<'a>(&'a self, x: &Self::Output) -> usize
        where
            Self::Output: Ord,
        {
            self.upper_bound_by(|p| p.cmp(x))
        }

        #[inline]
        fn upper_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
        where
            F: FnMut(&T) -> B,
            B: Ord,
        {
            self.upper_bound_by(|x| f(x).cmp(b))
        }

        #[inline]
        fn upper_bound_by<F>(&self, mut f: F) -> usize
        where
            F: FnMut(&T) -> cmp::Ordering,
        {
            self.span_partition_point(|x| f(x) != cmp::Ordering::Greater)
        }

        fn span_partition_point<F>(&self, mut pred: F) -> usize
        where
            F: FnMut(&T) -> bool,
        {
            let mut left = 0;
            let mut right = self.span_len();
            while left != right {
                let mid = left + (right - left) / 2;
                let value = &self[mid];
                if pred(value) {
                    left = mid + 1;
                } else {
                    right = mid;
                }
            }

            left
        }
    }
}
// }}}

use span::Span;
use std::ops;

#[derive(Debug, Clone)]
struct Fenwick {
    pub table: Vec<u32>,
}
impl Fenwick {
    pub fn new(zero: u32) -> Self {
        Self { table: vec![zero] }
    }
    pub fn push(&mut self, mut x: u32) {
        let n = self.table.len();
        let mut d = 1;
        let k = lsb(n);
        while d != k {
            x += self.table[n - d];
            d *= 2;
        }
        self.table.push(x);
    }
    pub fn build(src: &[u32]) -> Self {
        let mut table = vec![0; src.len() + 1];
        for i in 1..table.len() {
            let x = src[i - 1];
            table[i] += x;
            let j = i + lsb(i);
            if j < table.len() {
                table[j] += table[i];
            }
        }
        Self { table }
    }
    pub fn prefix_sum(&self, mut i: usize) -> u32 {
        let mut res = 0;
        while i != 0 {
            res += self.table[i];
            i -= lsb(i);
        }
        res
    }
    pub fn add(&mut self, mut i: usize, x: u32) {
        i += 1;
        while i < self.table.len() {
            self.table[i] += x;
            i += lsb(i);
        }
    }
    pub fn upper_bound(&self, x: &u32) -> usize {
        let mut l = self.table.len().next_power_of_two() / 2;
        let mut d = l;
        let mut now = self.table[l];
        while d != 1 {
            d /= 2;
            if &now <= x {
                while d != 1 && self.table.len() <= l + d {
                    d /= 2;
                }
                if self.table.len() <= l + d {
                    break;
                }
                l += d;
                now += self.table[l];
            } else {
                now -= self.table[l];
                l -= d;
                now += self.table[l];
            }
        }
        if &now <= x {
            l
        } else {
            l - 1
        }
    }
}

#[inline]
fn lsb(i: usize) -> usize {
    let i = i as isize;
    (i & -i) as usize
}

fn main() {
    let mut a = Vec::new();
    let n = 10;
    for _ in 0..n {
        let x = rand::random::<u32>() % 4;
        a.push(x);
    }
    let mut fenwick = Fenwick::build(&a);
    for i in 0..n {
        let x = rand::random::<u32>() % 4;
        fenwick.add(i, x);
        a[i] += x;
    }
    lg!(&fenwick);
    lg!(&a);
    for i in 0..=n {
        let expected = a[..i].iter().sum::<u32>();
        let result = fenwick.prefix_sum(i);
    }
    let mut b = vec![0; n + 1];
    for i in 0..n {
        b[i + 1] = b[i] + a[i];
    }
    lg!(&b);
    for x in 0..=320 {
        let expected = b.upper_bound(&x) - 1;
        let result = fenwick.upper_bound(&x);
        lg!((x, result, expected));
        assert_eq!(result, expected);
    }
}
