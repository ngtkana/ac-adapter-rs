use {
    super::Convolution,
    fp::{Fp, Mod},
    std::iter::repeat,
};

/// FPS の、積に関する逆元を mod x ^ `precision` で返します。
///
/// # 制約
///
/// * `a[0]` が 0 でない。
pub fn fps_inverse<M: Mod>(mut a: Vec<Fp<M>>, precision: usize) -> Vec<Fp<M>>
where
    Fp<M>: Convolution,
{
    let scalar = a[0];
    let scalar_recip = scalar.recip();
    assert_ne!(scalar, Fp::new(0), "定数項が 0 はだめです。");
    a.iter_mut().for_each(|x| *x *= scalar_recip);
    let mut b = vec![Fp::<M>::new(1)];
    while b.len() < precision {
        let next_precision = 2 * b.len();
        let a = a[..a.len().min(next_precision)].to_vec();
        let mut tmp = Fp::convolution(a, b.clone());
        tmp.iter_mut().for_each(|x| *x = -*x);
        tmp[0] += Fp::new(2);
        b = Fp::convolution(b, tmp);
        b.resize(next_precision, Fp::new(0));
    }
    b.resize(precision, Fp::new(0));
    b.iter_mut().for_each(|x| *x *= scalar_recip);
    b
}

/// FPS の log を mod x ^ `precision` で返します。
///
/// # 制約
///
/// * `a[0]` が 1 。
///
///
pub fn fps_log<M: Mod>(a: Vec<Fp<M>>, precision: usize) -> Vec<Fp<M>>
where
    Fp<M>: Convolution,
{
    assert_eq!(a[0], Fp::new(1), "定数項は 1 でないとだめです。");
    let den = fps_inverse(a.clone(), precision);
    let mut num = a;
    num.remove(0);
    num.iter_mut()
        .enumerate()
        .for_each(|(i, x)| *x *= Fp::new(i as u32 + 1));
    num.resize(precision, Fp::new(0));
    let mut ans = Fp::convolution(num, den);
    ans.iter_mut()
        .enumerate()
        .for_each(|(i, x)| *x /= Fp::new(i as u32 + 1));
    ans.insert(0, Fp::new(0));
    ans.resize(precision, Fp::new(0));
    ans
}

/// FPS の exp を mod x ^ `precision` で返します。
///
/// # 制約
///
/// * `a[0]` が 1 。
pub fn fps_exp<M: Mod>(a: Vec<Fp<M>>, precision: usize) -> Vec<Fp<M>>
where
    Fp<M>: Convolution,
{
    assert_eq!(a[0], Fp::new(0), "定数項が 0 でないとだめです。");
    let mut b = vec![Fp::<M>::new(1)];
    while b.len() < precision {
        let next_precision = 2 * b.len();
        let mut tmp = a
            .iter()
            .copied()
            .chain(repeat(Fp::new(0)))
            .zip(fps_log(
                b[..next_precision.min(b.len())].to_vec(),
                next_precision,
            ))
            .map(|(x, y)| x - y)
            .collect::<Vec<_>>();
        tmp[0] += Fp::new(1);
        b = Fp::convolution(b, tmp);
        b.resize(next_precision, Fp::new(0));
    }
    b.resize(precision, Fp::new(0));
    b
}

/// FPS の sqrt のひとつを mod x ^ `precision` で返します。
///
/// 存在しない場合は `None` を返します。
///
pub fn fps_sqrt<M: Mod>(mut a: Vec<Fp<M>>, precision: usize) -> Option<Vec<Fp<M>>>
where
    Fp<M>: Convolution,
{
    if a.as_slice() == &[Fp::new(0)] {
        return Some(a);
    }
    let zeros = a
        .iter()
        .position(|&x| x != Fp::new(0))
        .unwrap_or_else(|| panic!("0 がたくさん並んでいるのはだめです。"));
    if zeros % 2 == 1 {
        return None;
    }
    a = a[zeros..].to_vec();
    let mut b = vec![Fp::<M>::new(1)];
    let half = Fp::new(2).recip();
    while b.len() < precision {
        let next_precision = 2 * b.len();
        b = b
            .clone()
            .into_iter()
            .chain(repeat(Fp::new(0)))
            .zip(Fp::convolution(
                a.iter()
                    .copied()
                    .chain(repeat(Fp::new(0)))
                    .take(next_precision)
                    .collect::<Vec<_>>(),
                fps_inverse(b[..next_precision.min(b.len())].to_vec(), next_precision),
            ))
            .map(|(x, y)| (x + y) * half)
            .collect::<Vec<_>>();
        b.resize(next_precision, Fp::new(0));
    }
    b = repeat(Fp::new(0))
        .take(zeros / 2)
        .chain(b.into_iter())
        .collect::<Vec<_>>();
    b.resize(precision, Fp::new(0));
    Some(b)
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
#[cfg(test)]
mod tests {
    use {
        super::{super::Convolution, fps_exp, fps_inverse, fps_log, fps_sqrt},
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::iter::{once, repeat, repeat_with},
    };

    #[test]
    fn test_fps_inverse() {
        use fp::F998244353 as Fp;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..100);
            let precision = rng.gen_range(1..100);
            let a = once(Fp::new(rng.gen_range(1..Fp::P)))
                .chain(repeat_with(|| Fp::new(rng.gen_range(0..20))))
                .take(n)
                .collect_vec();
            let result = fps_inverse(a.clone(), precision);
            let mut expected_to_be_one = Fp::convolution(a, result.clone());
            expected_to_be_one.truncate(precision);
            assert_eq!(
                expected_to_be_one,
                once(Fp::new(1))
                    .chain(repeat(Fp::new(0)))
                    .take(precision)
                    .collect_vec()
            );
        }
    }

    #[test]
    fn test_fps_log() {
        use fp::F998244353 as Fp;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..20);
            let precision = rng.gen_range(1..20);
            let a = once(Fp::new(1))
                .chain(repeat_with(|| Fp::new(rng.gen_range(0..20))))
                .take(n)
                .collect_vec();
            let result = fps_log(a.clone(), precision);
            let mut expected = vec![Fp::new(0); precision];
            let mut acc = vec![Fp::new(1)];
            for i in 1..=precision {
                acc = Fp::convolution(
                    once(Fp::new(0)).chain(a[1..].iter().copied()).collect_vec(),
                    acc,
                );
                acc.truncate(precision);
                expected.iter_mut().zip(acc.iter()).for_each(|(x, y)| {
                    *x += *y / Fp::new(i as u32)
                        * Fp::from(match i % 2 {
                            0 => -1,
                            1 => 1,
                            _ => unreachable!(),
                        })
                });
            }
            assert_eq!(result, expected,);
        }
    }

    #[test]
    fn test_fps_exp() {
        use fp::F998244353 as Fp;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..20);
            let precision = rng.gen_range(1..20);
            let a = once(Fp::new(0))
                .chain(repeat_with(|| Fp::new(rng.gen_range(0..20))))
                .take(n)
                .collect_vec();
            let result = fps_exp(a.clone(), precision);
            let mut expected = vec![Fp::new(0); precision];
            expected[0] = Fp::new(1);
            let mut acc = vec![Fp::new(1)];
            for i in 1..=precision {
                acc = Fp::convolution(a.clone(), acc);
                acc.iter_mut().for_each(|x| *x /= Fp::from(i as u32));
                acc.resize(precision, Fp::new(0));
                expected
                    .iter_mut()
                    .zip(acc.iter())
                    .for_each(|(x, y)| *x += *y);
            }
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_fps_sqrt() {
        use fp::F998244353 as Fp;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..20);
            let precision = rng.gen_range(1..20);
            let a = once(Fp::new(1))
                .chain(repeat_with(|| Fp::new(rng.gen_range(0..20))))
                .take(n)
                .collect_vec();
            crate::lg!(&a);
            let result = fps_sqrt(a.clone(), precision).unwrap();
            crate::lg!(&result);
            let expected_to_be_a = Fp::convolution(result.clone(), result.clone());
            assert_eq!(
                &expected_to_be_a[..precision],
                &a.iter()
                    .copied()
                    .chain(repeat(Fp::new(0)))
                    .take(precision)
                    .collect::<Vec<_>>()
            );
        }
    }
}
