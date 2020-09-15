use std::{fmt, iter, ops};

#[derive(Debug, Clone)]
pub struct Fenwick<T> {
    table: Vec<T>,
}

impl<'a, T> Fenwick<T>
where
    T: Clone + fmt::Debug + ops::Add<Output = T> + ops::AddAssign + iter::Sum<T>,
{
    pub fn new(zero: T) -> Self {
        Fenwick { table: vec![zero] }
    }

    pub fn from_zero_slice(zero: T, src: &[T]) -> Self {
        let mut table = iter::once(zero)
            .chain(src.iter().cloned())
            .collect::<Vec<_>>();
        let n = table.len();
        (1..n)
            .map(|i| (i, i + lsb(i)))
            .filter(|&(_, j)| j < n)
            .for_each(|(i, j)| {
                let x = table[i].clone();
                table[j] += x
            });
        Self { table }
    }

    pub fn push(&mut self, mut x: T) {
        let i = self.table.len();
        let lsb_i = lsb(i);
        x += iter::successors(Some(1), |&d| Some(2 * d))
            .take_while(|&d| d != lsb_i)
            .map(|d| self.table[i - d].clone())
            .sum::<T>();
        self.table.push(x);
    }

    pub fn prefix_sum(&self, i: usize) -> T {
        iter::successors(Some(i), |&i| Some(i - lsb(i)))
            .take_while(|&i| i != 0)
            .map(|i| self.table[i].clone())
            .sum::<T>()
    }

    pub fn add(&mut self, i: usize, x: T) {
        let n = self.table.len();
        iter::successors(Some(i + 1), |&i| Some(i + lsb(i)))
            .take_while(|&i| i < n)
            .for_each(|i| self.table[i] += x.clone());
    }

    pub fn partition_point(&self, pred: impl Fn(usize, &T) -> bool) -> (usize, T) {
        let mut j = 0;
        let mut current = self.table[0].clone();
        for d in iter::successors(Some(self.table.len().next_power_of_two() / 2), |&d| {
            Some(d / 2)
        })
        .take_while(|&d| d != 0)
        {
            assert!(
                pred(0, &self.table[0]),
                "pred(0, zero) のほうよろしくお願いいたします！"
            );
            if j + d < self.table.len() {
                let next = current.clone() + self.table[j + d].clone();
                if pred(j + d, &next) {
                    current = next;
                    j += d;
                }
            }
        }
        (j, current)
    }

    #[inline]
    pub fn lower_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        self.partition_point(|_, y| y < x).0
    }

    #[inline]
    pub fn upper_bound(&self, x: &T) -> usize
    where
        T: Ord,
    {
        self.partition_point(|_, y| y <= x).0
    }

    #[inline]
    pub fn lower_bound_from(&self, i: usize, x: &T) -> usize
    where
        T: Ord,
    {
        let bi = self.prefix_sum(i);
        let res = self.partition_point(|_, y| y < &(bi.clone() + x.clone())).0;
        assert!(i <= res, "逆戻りしていませんか？");
        res
    }

    #[inline]
    pub fn upper_bound_from(&self, i: usize, x: &T) -> usize
    where
        T: Ord,
    {
        let bi = self.prefix_sum(i);
        let res = self
            .partition_point(|_, y| y <= &(bi.clone() + x.clone()))
            .0;
        assert!(i <= res, "逆戻りしていませんか？");
        res
    }
}

impl<'a, T> Fenwick<T>
where
    T: Clone
        + fmt::Debug
        + ops::Add<Output = T>
        + ops::AddAssign
        + ops::Sub<Output = T>
        + ops::SubAssign
        + iter::Sum<T>,
{
    pub fn sum(&self, range: impl ops::RangeBounds<usize>) -> T {
        let start = match range.start_bound() {
            ops::Bound::Unbounded => 0,
            ops::Bound::Included(&x) => x,
            ops::Bound::Excluded(&x) => x + 1,
        };
        let end = match range.end_bound() {
            ops::Bound::Excluded(&x) => x,
            ops::Bound::Included(&x) => x + 1,
            ops::Bound::Unbounded => self.table.len() - 1,
        };
        assert!(start <= end, "変な区間を渡すのをやめませんか？");
        assert!(end < self.table.len(), "残念範囲外です！");
        self.prefix_sum(end) - self.prefix_sum(start)
    }

    pub fn access(&self, i: usize) -> T {
        assert!(i < self.table.len() - 1, "残念範囲外です！");
        self.prefix_sum(i + 1) - self.prefix_sum(i)
    }

    pub fn set(&mut self, i: usize, x: T) {
        assert!(i < self.table.len() - 1, "残念範囲外です！");
        self.add(i, x - self.access(i));
    }
}

fn lsb(x: usize) -> usize {
    x & x.wrapping_neg()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use std::{marker, mem};

    #[test]
    fn test_hand() {
        let mut fenwick = Fenwick::from_zero_slice(0, &[1, 1, 1]);
        assert_eq!(fenwick.prefix_sum(0), 0);
        assert_eq!(fenwick.prefix_sum(1), 1);
        assert_eq!(fenwick.prefix_sum(2), 2);

        (fenwick.add(0, 1));
        (fenwick.add(1, 1));
        (fenwick.add(2, 1));

        fenwick.push(2);
        fenwick.push(2);
        fenwick.push(2);

        assert_eq!(fenwick.prefix_sum(0), 0);
        assert_eq!(fenwick.prefix_sum(1), 2);
        assert_eq!(fenwick.prefix_sum(2), 4);
        assert_eq!(fenwick.prefix_sum(3), 6);
        assert_eq!(fenwick.prefix_sum(4), 8);
        assert_eq!(fenwick.prefix_sum(5), 10);
    }

    macro_rules! make_test {
        ($zero:expr, $gen_value:expr) => {
            test_utils::Test {
                test_count: 10,
                query_count: 30,
                gen_instance: |rng: &mut StdRng| {
                    let n = rng.gen_range(6, 20);
                    iter::repeat_with(|| $gen_value(rng))
                        .take(n)
                        .collect::<Vec<_>>()
                },
                construct: |a| Fenwick::from_zero_slice($zero, a),
                queries: test_utils::Omikuji::new(),
            };
        };
    }

    macro_rules! push {
        ($test:ident, $gen_value:expr) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "push",
                    gen_query: |_: &Vec<_>, rng: &mut StdRng| $gen_value(rng),
                    brute: |a: &mut Vec<_>, &x| a.push(x),
                    fast: |fenwick: &mut Fenwick<_>, &x| fenwick.push(x),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! prefix_sum {
        ($test:ident) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "prefix_sum",
                    gen_query: |a: &Vec<_>, rng: &mut StdRng| rng.gen::<usize>() % a.len(),
                    brute: |a: &mut Vec<_>, &i| a[..i].iter().sum::<_>(),
                    fast: |fenwick: &mut Fenwick<_>, &i| fenwick.prefix_sum(i),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! add {
        ($test:ident, $gen_value:expr) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "add",
                    gen_query: |a: &Vec<_>, rng: &mut StdRng| {
                        (rng.gen::<usize>() % a.len(), $gen_value(rng))
                    },
                    brute: |a: &mut Vec<_>, &(i, x)| a[i] += x,
                    fast: |fenwick: &mut Fenwick<_>, &(i, x)| fenwick.add(i, x),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! sum {
        ($test:ident, $T:ty) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "sum",
                    gen_query: |a: &Vec<_>, rng: &mut StdRng| {
                        let mut l = rng.gen_range(0, a.len());
                        let mut r = rng.gen_range(0, a.len() + 1);
                        if l > r {
                            mem::swap(&mut l, &mut r);
                        }
                        (l, r)
                    },
                    brute: |a: &mut Vec<_>, &(l, r)| a[l..r].iter().sum::<$T>(),
                    fast: |fenwick: &mut Fenwick<_>, &(l, r)| fenwick.sum(l..r),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! access {
        ($test:ident) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "access",
                    gen_query: |a: &Vec<_>, rng: &mut StdRng| rng.gen_range(0, a.len()),
                    brute: |a: &mut Vec<_>, &i| a[i],
                    fast: |fenwick: &mut Fenwick<_>, &i| fenwick.access(i),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! set {
        ($test:ident, $gen_value:ident) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "set",
                    gen_query: |a: &Vec<_>, rng: &mut StdRng| {
                        (rng.gen_range(0, a.len()), $gen_value(rng))
                    },
                    brute: |a: &mut Vec<_>, (i, x)| a[*i] = x.clone(),
                    fast: |fenwick: &mut Fenwick<_>, (i, x)| fenwick.set(*i, x.clone()),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! lower_bound {
        ($test:ident, $gen_value:ident) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "lower_bound",
                    gen_query: |_: &Vec<_>, rng: &mut StdRng| $gen_value(rng),
                    brute: |a: &mut Vec<_>, x| {
                        let mut i = 0;
                        let mut current = 0;
                        while i < a.len() && &(current + a[i]) < x {
                            current += a[i];
                            i += 1;
                        }
                        i
                    },
                    fast: |fenwick: &mut Fenwick<_>, x| fenwick.lower_bound(x),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! upper_bound {
        ($test:ident, $gen_value:ident) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "upper_bound",
                    gen_query: |_: &Vec<_>, rng: &mut StdRng| $gen_value(rng),
                    brute: |a: &mut Vec<_>, x| {
                        let mut i = 0;
                        let mut current = 0;
                        while i < a.len() && &(current + a[i]) <= x {
                            current += a[i];
                            i += 1;
                        }
                        i
                    },
                    fast: |fenwick: &mut Fenwick<_>, x| fenwick.upper_bound(x),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! lower_bound_from {
        ($test:ident, $gen_value:ident) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "lower_bound_from",
                    gen_query: |a: &Vec<_>, rng: &mut StdRng| {
                        (rng.gen_range(0, a.len()), $gen_value(rng))
                    },
                    brute: |a: &mut Vec<_>, (i, x)| {
                        let mut i = *i;
                        let mut current = 0;
                        while i < a.len() && &(current + a[i]) < x {
                            current += a[i];
                            i += 1;
                        }
                        i
                    },
                    fast: |fenwick: &mut Fenwick<_>, (i, x)| fenwick.lower_bound_from(*i, x),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    macro_rules! upper_bound_from {
        ($test:ident, $gen_value:ident) => {
            $test.queries.push(
                10,
                Box::new(test_utils::QueryImpl {
                    name: "lower_bound_from",
                    gen_query: |a: &Vec<_>, rng: &mut StdRng| {
                        (rng.gen_range(0, a.len()), $gen_value(rng))
                    },
                    brute: |a: &mut Vec<_>, (i, x)| {
                        let mut i = *i;
                        let mut current = 0;
                        while i < a.len() && &(current + a[i]) <= x {
                            current += a[i];
                            i += 1;
                        }
                        i
                    },
                    fast: |fenwick: &mut Fenwick<_>, (i, x)| fenwick.upper_bound_from(*i, x),
                    marker: marker::PhantomData::<_>,
                }),
            );
        };
    }

    #[test]
    fn test_i32() {
        use rand::prelude::*;

        fn gen_value(rng: &mut StdRng) -> i32 {
            rng.gen_range(-9, 10)
        }

        let mut test = make_test!(0, gen_value);
        push!(test, gen_value);
        prefix_sum!(test);
        add!(test, gen_value);
        sum!(test, i32);
        access!(test);
        set!(test, gen_value);

        let mut rng = StdRng::seed_from_u64(42);
        test.run(&mut rng);
    }

    // u32 にすると set の内部実装でオーバーフローをします。
    #[test]
    fn test_non_negative_i32() {
        use rand::prelude::*;

        fn gen_value(rng: &mut StdRng) -> i32 {
            rng.gen_range(0, 10)
        }

        fn gen_summed_positive_value(rng: &mut StdRng) -> i32 {
            rng.gen_range(1, 100)
        }

        fn gen_summed_nonnegative_value(rng: &mut StdRng) -> i32 {
            rng.gen_range(0, 100)
        }

        let mut test = make_test!(0, gen_value);
        push!(test, gen_value);
        prefix_sum!(test);
        add!(test, gen_value);
        sum!(test, i32);
        access!(test);
        set!(test, gen_value);
        lower_bound!(test, gen_summed_positive_value);
        upper_bound!(test, gen_summed_nonnegative_value);
        lower_bound_from!(test, gen_summed_positive_value);
        upper_bound_from!(test, gen_summed_nonnegative_value);

        let mut rng = StdRng::seed_from_u64(42);
        test.run(&mut rng);
    }

    #[test]
    fn test_fp() {
        use type_traits::Constant;
        type_traits::define_constant! { type Mod97: i16 = 97; }
        type Fp = fp::Fp<Mod97>;

        fn gen_value(rng: &mut StdRng) -> Fp {
            Fp::new(rng.gen_range(0, 97))
        }

        let mut test = make_test!(Fp::zero(), gen_value);
        push!(test, gen_value);
        prefix_sum!(test);
        add!(test, gen_value);
        sum!(test, Fp);
        access!(test);
        set!(test, gen_value);

        let mut rng = StdRng::seed_from_u64(42);
        test.run(&mut rng);
    }
}
