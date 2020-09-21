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
        assert!(end <= self.len, "範囲外は禁止です！");
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

    pub fn as_slice(&self) -> &[T] {
        &self.table[self.len..]
    }

    pub fn forward_partition_point(&self, start: usize, mut f: impl FnMut(&T) -> bool) -> usize {
        assert!(start <= self.len, "範囲外は禁止です！");
        let mut i = self.len + start;
        if self.fold(start..).map(|x| f(&x)).unwrap_or(true) {
            self.len
        } else if !f(&self.table[i]) {
            start
        } else {
            let mut current = self.table[i].clone();
            i += 1;
            let mut next = current.clone().op(self.table[i].clone());

            while f(&next) {
                if i % 2 == 0 {
                    i /= 2;
                } else {
                    current = next.clone();
                    i += 1;
                }
                next = current.clone().op(self.table[i].clone());
            }
            loop {
                if f(&next) {
                    current = next.clone();
                    i += 1;
                } else {
                    if self.len < i {
                        return i - self.len;
                    }
                    i *= 2;
                }
                next = current.clone().op(self.table[i].clone());
            }
        }
    }

    pub fn backward_partition_point(&self, end: usize, mut f: impl FnMut(&T) -> bool) -> usize {
        assert!(end <= self.len, "範囲外は禁止です！");
        let mut i = self.len + end;
        if self.fold(..end).map(|x| f(&x)).unwrap_or(true) {
            0
        } else if !f(&self.table[i - 1]) {
            end
        } else {
            i -= 1;
            let mut current = self.table[i].clone();
            let mut next = self.table[i - 1].clone().op(current.clone());

            while f(&next) {
                if i % 2 == 0 {
                    i /= 2;
                } else {
                    i -= 1;
                    current = next.clone();
                }
                next = self.table[i - 1].clone().op(current.clone());
            }
            loop {
                if f(&next) {
                    i -= 1;
                    current = next.clone();
                } else {
                    if self.len < i {
                        return i - self.len;
                    }
                    i *= 2;
                }
                next = self.table[i - 1].clone().op(current.clone());
            }
        }
    }
    pub fn forward_lower_bound_by_key<U: Ord>(
        &self,
        start: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.forward_partition_point(start, |x| &project(x) < value)
    }
    pub fn forward_upper_bound_by_key<U: Ord>(
        &self,
        start: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.forward_partition_point(start, |x| &project(x) <= value)
    }
    pub fn backward_lower_bound_by_key<U: Ord>(
        &self,
        end: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.backward_partition_point(end, |x| &project(x) < value)
    }
    pub fn backward_upper_bound_by_key<U: Ord>(
        &self,
        end: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.backward_partition_point(end, |x| &project(x) <= value)
    }

    fn update(&mut self, i: usize) {
        let x = T::op(self.table[2 * i].clone(), self.table[2 * i + 1].clone());
        self.table[i] = x;
    }
}

impl<T: Assoc + Ord> Segtree<T> {
    pub fn forward_lower_bound(&self, start: usize, value: &T) -> usize {
        self.forward_partition_point(start, |x| x < value)
    }
    pub fn forward_upper_bound(&self, start: usize, value: &T) -> usize {
        self.forward_partition_point(start, |x| x <= value)
    }
    pub fn backward_lower_bound(&self, end: usize, value: &T) -> usize {
        self.backward_partition_point(end, |x| x < value)
    }
    pub fn backward_upper_bound(&self, end: usize, value: &T) -> usize {
        self.backward_partition_point(end, |x| x <= value)
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
    use tester::{gen_instance, SegBinSearchQuery, SegQuery};
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
    fn test_u32_add_bin_search() {
        use rand::prelude::*;

        query_struct! { struct Query; }
        impl<'a> SegQuery<'a> for Query<'a> {
            type Value = Add<u32>;
            triv_mtds! {self: Self}
            fn gen_value(&mut self) -> Self::Value {
                Add(self.rng().gen_range(0, 10))
            }
        }
        impl<'a> SegBinSearchQuery<'a> for Query<'a> {
            fn gen_ge_nonempty_folded_value(&mut self) -> Self::Value {
                let lim = self.len() as u32 * 10 / 2;
                Add(self.rng().gen_range(0, lim))
            }
            fn gen_gt_nonempty_folded_value(&mut self) -> Self::Value {
                let lim = self.len() as u32 * 10 / 2;
                Add(self.rng().gen_range(1, lim))
            }
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut instance = gen_instance(1..30, &mut rng, PhantomData::<Query>);
            for _ in 0..50 {
                match instance.query.rng().gen_range(0, 100) {
                    0..=19 => instance.apply(query!(set, i, x)),
                    20..=39 => instance.apply(query!(forward_upper_bound, start, ref value)),
                    40..=59 => instance.apply(query!(forward_lower_bound, start, ref value)),
                    60..=79 => instance.apply(query!(backward_upper_bound, start, ref value)),
                    80..=99 => instance.apply(query!(backward_lower_bound, start, ref value)),
                    _ => panic!(),
                }
            }
        }
    }

    #[test]
    fn test_fp_add() {
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
        for _ in 0..20 {
            let mut instance = gen_instance(1..30, &mut rng, PhantomData::<Query>);
            for _ in 0..50 {
                match instance.query.rng().gen_range(0, 100) {
                    0..=29 => instance.apply(query!(set, i, x)),
                    20..=39 => instance.apply(query!(get, i)),
                    40..=99 => instance.apply(query!(fold, range)),
                    _ => panic!(),
                }
            }
        }
    }

    #[test]
    fn test_fp_affine() {
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
        for _ in 0..20 {
            let mut instance = gen_instance(1..30, &mut rng, PhantomData::<Query>);
            for _ in 0..50 {
                match instance.query.rng().gen_range(0, 100) {
                    0..=29 => instance.apply(query!(set, i, x)),
                    20..=39 => instance.apply(query!(get, i)),
                    40..=99 => instance.apply(query!(fold, range)),
                    _ => panic!(),
                }
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
        for _ in 0..20 {
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
}
