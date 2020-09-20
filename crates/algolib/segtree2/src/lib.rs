use std::{iter, ops};
use type_traits::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Segtree<T> {
    len: usize,
    table: Vec<T>,
}

impl<T: Assoc> Segtree<T> {
    pub fn from_slice(src: &[T]) -> Self {
        if src.is_empty() {
            Self {
                len: 0,
                table: Vec::new(),
            }
        } else {
            let mut me = Self {
                len: src.len(),
                table: src.iter().chain(src).cloned().collect::<Vec<_>>(),
            };
            for i in (0..src.len()).rev() {
                me.update(i);
            }
            me
        }
    }

    pub fn set(&mut self, i: usize, x: T) {
        assert!(i < self.len);
        self.modify(i, |y| y.clone_from(&x));
    }

    pub fn get(&mut self, i: usize) -> &T {
        assert!(i < self.len);
        &self.table[self.len + i]
    }

    pub fn modify(&mut self, mut i: usize, f: impl Fn(&mut T)) {
        assert!(i < self.len);
        i += self.len;
        f(&mut self.table[i]);
        for i in iter::successors(Some(i / 2), |&x| if x == 0 { None } else { Some(x / 2) }) {
            self.update(i);
        }
    }

    pub fn fold(&self, range: impl ops::RangeBounds<usize>) -> Option<T> {
        let (mut start, mut end) = open(self.len, range);
        assert!(start <= end, "変な区間を渡すのをやめませんか？");
        assert!(end <= self.len, "範囲外です！");
        start += self.len;
        end += self.len;

        if start == end {
            None
        } else if start + 1 == end {
            Some(self.table[start].clone())
        } else {
            let mut left = self.table[start].clone();
            start += 1;
            end -= 1;
            let mut right = self.table[end].clone();
            while start != end {
                if start % 2 == 1 {
                    left.op_from_right(&self.table[start]);
                    start += 1;
                }
                if end % 2 == 1 {
                    end -= 1;
                    right.op_from_left(&self.table[end]);
                }
                start /= 2;
                end /= 2;
            }
            Some(T::op(left, right))
        }
    }

    fn update(&mut self, i: usize) {
        let x = T::op(self.table[2 * i].clone(), self.table[2 * i + 1].clone());
        self.table[i] = x;
    }
}

fn open(len: usize, range: impl ops::RangeBounds<usize>) -> (usize, usize) {
    use ops::Bound::*;
    (
        match range.start_bound() {
            Unbounded => 0,
            Included(&x) => x,
            Excluded(&x) => x + 1,
        },
        match range.end_bound() {
            Excluded(&x) => x,
            Included(&x) => x + 1,
            Unbounded => len,
        },
    )
}

#[cfg(test)]
mod tests {
    mod tester;

    use super::*;
    use query_test::query;
    use rand::prelude::*;
    use std::marker::PhantomData;
    use tester::{gen_instance, SegQuery};
    use type_traits::wrappers::{Add, Affine, Cat};

    fn gen_fp<Mod>(rng: &mut impl Rng) -> fp::Fp<Mod>
    where
        Mod: fp::Modable<Output = i64>,
    {
        fp::Fp::new(rng.gen_range(0, Mod::VALUE))
    }

    macro_rules! query_struct {
        (struct $name:ident;) => {
            struct $name<'a> {
                pub len: usize,
                pub rng: &'a mut StdRng,
            }
        };
    }
    macro_rules! triv_mtds {
        ($self:ident: $Self:ident) => {
            type Rng = StdRng;
            fn new(len: usize, rng: &'a mut Self::Rng) -> $Self {
                $Self { len, rng }
            }
            fn rng(&mut $self) -> &mut Self::Rng {
                &mut $self.rng
            }
            fn len(&$self) -> usize {
                $self.len
            }
        };
    }

    #[test]
    fn test_add_fp_add() {
        use rand::prelude::*;
        type Fp = fp::F998244353;

        query_struct! { struct Query; }
        impl<'a> SegQuery<'a> for Query<'a> {
            type Value = Add<Fp>;
            triv_mtds! {self: Self}
            fn gen_value(&mut self) -> Self::Value {
                Add(gen_fp(&mut self.rng))
            }
        }

        let mut rng = StdRng::seed_from_u64(42);
        let mut instance = gen_instance(1..30, &mut rng, PhantomData::<Query>);
        for _ in 0..20 {
            match instance.query.rng().gen_range(0, 100) {
                0..=29 => instance.apply(query!(set, i, x)),
                20..=39 => instance.apply(query!(get, i)),
                40..=99 => instance.apply(query!(fold, range)),
                _ => panic!(),
            }
        }
    }

    #[test]
    fn test_add_fp_affine() {
        use rand::prelude::*;
        type Fp = fp::F998244353;

        query_struct! { struct Query; }
        impl<'a> SegQuery<'a> for Query<'a> {
            type Value = Affine<Fp>;
            triv_mtds! {self: Self}
            fn gen_value(&mut self) -> Self::Value {
                Affine {
                    a: gen_fp(&mut self.rng()),
                    b: gen_fp(&mut self.rng()),
                }
            }
        }

        let mut rng = StdRng::seed_from_u64(42);
        let mut instance = gen_instance(1..30, &mut rng, PhantomData::<Query>);
        for _ in 0..20 {
            match instance.query.rng().gen_range(0, 100) {
                0..=29 => instance.apply(query!(set, i, x)),
                20..=39 => instance.apply(query!(get, i)),
                40..=99 => instance.apply(query!(fold, range)),
                _ => panic!(),
            }
        }
    }

    #[test]
    fn test_cat() {
        use rand::prelude::*;

        query_struct! { struct Query; }
        impl<'a> SegQuery<'a> for Query<'a> {
            type Value = Cat;
            triv_mtds! {self: Self}
            fn gen_value(&mut self) -> Self::Value {
                Cat(
                    iter::repeat_with(|| self.rng().sample(rand::distributions::Alphanumeric))
                        .take(3)
                        .collect::<String>(),
                )
            }
        }

        let mut rng = StdRng::seed_from_u64(42);
        let mut instance = gen_instance(1..30, &mut rng, PhantomData::<Query>);
        for _ in 0..20 {
            match instance.query.rng().gen_range(0, 100) {
                0..=29 => instance.apply(query!(set, i, x)),
                20..=39 => instance.apply(query!(get, i)),
                40..=99 => instance.apply(query!(fold, range)),
                _ => panic!(),
            }
        }
    }
}
