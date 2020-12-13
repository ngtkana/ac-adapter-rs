mod algo;

use rand::prelude::*;
use std::{collections::HashSet, iter, mem, ops::Range};

#[derive(Debug)]
pub struct LogUniform(pub Range<usize>);
impl Distribution<usize> for LogUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        let Range { start, end } = self.0;
        assert!(start <= end);
        let ln = rng.gen_range((start as f64).ln(), (end as f64).ln());
        (ln.exp().floor() as usize).max(start).min(end - 1)
    }
}

#[derive(Debug)]
pub struct DistinctTwo(pub Range<usize>);
impl Distribution<(usize, usize)> for DistinctTwo {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (usize, usize) {
        let Range { start, end } = self.0;
        assert!(start + 2 <= end);
        let mut i = rng.gen_range(start, end - 1);
        let j = rng.gen_range(start, end);
        if i > j {
            i += 1;
        }
        (i, j)
    }
}

#[derive(Debug)]
pub struct SubRange(pub Range<usize>);
impl Distribution<Range<usize>> for SubRange {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Range<usize> {
        let Range { start, end } = self.0;
        assert!(start <= end);
        let mut l = rng.gen_range(start, end + 2);
        let mut r = rng.gen_range(start, end + 1);
        if l > r {
            mem::swap(&mut l, &mut r);
            r -= 1;
        }
        l..r
    }
}

#[derive(Debug)]
pub struct NonEmptySubRange(pub Range<usize>);
impl Distribution<Range<usize>> for NonEmptySubRange {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Range<usize> {
        let Range { start, end } = self.0;
        assert!(start < end);
        let mut l = rng.gen_range(start, end);
        let mut r = rng.gen_range(start, end + 1);
        if l >= r {
            mem::swap(&mut l, &mut r);
            r += 1;
        }
        l..r
    }
}

#[derive(Debug)]
pub struct Tree(pub usize);
impl Distribution<Vec<Vec<usize>>> for Tree {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let n = self.0;
        assert!(1 <= n);
        if n == 1 {
            vec![Vec::new()]
        } else {
            let prufer = iter::repeat_with(|| rng.gen_range(0, n))
                .take(n - 2)
                .collect::<Vec<_>>();
            algo::prufer2tree(&prufer)
        }
    }
}

#[derive(Debug)]
pub struct SimpleGraph(pub usize, pub usize);
impl Distribution<Vec<Vec<usize>>> for SimpleGraph {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let &Self(n, m) = self;
        let mut g = vec![Vec::new(); n];
        for (u, v) in rng.sample(SimpleGraphEdges(n, m)) {
            g[u].push(v);
            g[v].push(u);
        }
        g
    }
}

#[derive(Debug)]
pub struct SimpleDigraph(pub usize, pub usize);
impl Distribution<Vec<Vec<usize>>> for SimpleDigraph {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<Vec<usize>> {
        let &Self(n, m) = self;
        let mut g = vec![Vec::new(); n];
        for (u, v) in rng.sample(SimpleGraphEdges(n, m)) {
            g[u].push(v);
        }
        g
    }
}

#[derive(Debug)]
pub struct SimpleGraphEdges(pub usize, pub usize);
impl Distribution<Vec<(usize, usize)>> for SimpleGraphEdges {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<(usize, usize)> {
        let &Self(n, m) = self;
        assert!(m <= n * (n - 1) / 2);
        let mut set = HashSet::new();
        DistinctTwo(0..n)
            .sample_iter(rng)
            .filter(|&(u, v)| {
                let found = set.contains(&(u, v));
                set.insert((u, v));
                set.insert((v, u));
                !found
            })
            .take(m)
            .collect()
    }
}

#[derive(Debug)]
pub struct SimpleDigraphEdges(pub usize, pub usize);
impl Distribution<Vec<(usize, usize)>> for SimpleDigraphEdges {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<(usize, usize)> {
        let &Self(n, m) = self;
        assert!(m <= n * (n - 1) / 2);
        let mut set = HashSet::new();
        DistinctTwo(0..n)
            .sample_iter(rng)
            .filter(|&(u, v)| {
                let found = set.contains(&(u, v));
                set.insert((u, v));
                !found
            })
            .take(m)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{LogUniform, NonEmptySubRange, SubRange, Tree},
        rand::prelude::*,
        std::ops::Range,
    };
    mod algo;

    #[test]
    fn test_log_uniform() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let range = rng.sample(NonEmptySubRange(1..20));
            let x = rng.sample(LogUniform(range.clone()));
            assert!(range.contains(&x));
        }
    }

    #[test]
    fn test_open() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let d = rng.gen_range(2, 8);
            let l = rng.gen_range(0, 40);
            let r = l + d;
            let Range { start, end } = rng.sample(SubRange(l..r));

            assert!(l <= start && start <= end && end <= r);
        }
    }
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
        ($val:expr,) => { $crate::lg!($val) };
        ($($val:expr),+ $(,)?) => {
            ($($crate::lg!($val)),+,)
        };
    }

        #[macro_export]
        macro_rules! lg_nl {
            () => {
                eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
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
                $crate::lg_nl!($crate::Tabular($val))
            };
        }

        #[macro_export]
        macro_rules! boolean_table {
            ($val:expr) => {
                $crate::lg_nl!($crate::BooleanTable($val));
            };
        }

        #[macro_export]
        macro_rules! boolean_slice {
            ($val:expr) => {
                $crate::lg!($crate::BooleanSlice($val));
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

    #[test]
    fn test_tree() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1, 1_000);
            let g = rng.sample(Tree(n));
            println!("g = {:?}", &g);
            assert!(algo::is_tree(&g));
        }
    }
}
