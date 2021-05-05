use std::{
    fmt::{Debug, DebugList, DebugMap, Formatter, Result},
    iter::repeat_with,
    marker::PhantomData,
    ops::{Bound, Range, RangeBounds},
};

#[derive(Clone, Default, Hash, PartialEq)]
pub struct Segtree<T, S> {
    seg: Option<Box<Nonempty<T, S>>>,
    len: usize,
}
impl<T: Clone, S: SparseSegtreeTrait<Value = T>> Segtree<T, S> {
    pub fn new(len: usize) -> Self {
        Self {
            seg: if len == 0 {
                None
            } else {
                Some(Box::new(__internal_new(len.next_power_of_two())))
            },
            len,
        }
    }
    pub fn set(&mut self, i: usize, x: T) {
        self.modify(i, move |y| *y = x);
    }
    pub fn modify(&mut self, i: usize, f: impl FnOnce(&mut T)) {
        assert!(i < self.len, "範囲外です。 i = {}, len = {}", i, self.len);
        __internal_modify(self.seg.as_mut().unwrap(), i, f);
    }
    pub fn fold(&self, range: impl RangeBounds<usize>) -> T {
        let Range { start, end } = __internal_open(range, self.len);
        assert!(
            start <= end && end <= self.len,
            "範囲外です。 range = {:?}, len = {}",
            &(start..end),
            self.len
        );
        __internal_fold(&self.seg, start, end)
    }
    pub fn debug_list(&self) -> SparseSegtreeDebugList<'_, T, S> {
        SparseSegtreeDebugList(self)
    }
}

#[derive(Clone, Default, Hash, PartialEq)]
pub struct Nonempty<T, S> {
    len: usize,
    value: T,
    child: [Option<Box<Self>>; 2],
    __marker: PhantomData<fn(S) -> S>,
}
fn __internal_new<T: Clone, S: SparseSegtreeTrait<Value = T>>(len: usize) -> Nonempty<T, S> {
    assert!(len.is_power_of_two());
    Nonempty {
        len,
        value: S::id(),
        child: [None, None],
        __marker: PhantomData,
    }
}
fn __internal_fold<T: Clone, S: SparseSegtreeTrait<Value = T>>(
    seg: &Option<Box<Nonempty<T, S>>>,
    l: usize,
    r: usize,
) -> T {
    match seg {
        None => S::id(),
        Some(seg) => {
            let len = seg.len;
            let half = len / 2;
            if [l, r] == [0, len] {
                seg.value.clone()
            } else if l == r {
                S::id()
            } else if r <= half {
                __internal_fold(&seg.child[0], l, r)
            } else if half <= l {
                __internal_fold(&seg.child[1], l - half, r - half)
            } else {
                S::op(
                    &__internal_fold(&seg.child[0], l, half),
                    &__internal_fold(&seg.child[1], 0, r - half),
                )
            }
        }
    }
}
fn __internal_modify<T: Clone, S: SparseSegtreeTrait<Value = T>>(
    seg: &mut Nonempty<T, S>,
    i: usize,
    f: impl FnOnce(&mut S::Value),
) {
    let len = seg.len;
    debug_assert!(i < len);
    if len == 1 {
        f(&mut seg.value);
    } else {
        let (e, i) = if len / 2 <= i {
            (1, i - len / 2)
        } else {
            (0, i)
        };
        __internal_modify(
            seg.child[e].get_or_insert_with(|| Box::new(__internal_new(len / 2))),
            i,
            f,
        );
        __internal_update(seg);
    }
}
fn __internal_update<T: Clone, S: SparseSegtreeTrait<Value = T>>(seg: &mut Nonempty<T, S>) {
    seg.value = S::op(
        &seg.child[0]
            .as_ref()
            .map_or_else(S::id, |c| c.value.clone()),
        &seg.child[1]
            .as_ref()
            .map_or_else(S::id, |c| c.value.clone()),
    );
}

impl<T: Clone + Debug, S: SparseSegtreeTrait<Value = T>> Debug for Segtree<T, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut map = f.debug_map();
        if let Some(seg) = self.seg.as_ref() {
            __internal_debug_map(seg, &mut map, 0);
        }
        map.finish()
    }
}
fn __internal_debug_map<T: Clone + Debug, S: SparseSegtreeTrait<Value = T>>(
    seg: &Nonempty<T, S>,
    map: &mut DebugMap<'_, '_>,
    offset: usize,
) {
    if seg.len == 1 {
        map.entry(&offset, &seg.value);
    } else {
        for e in 0..2 {
            if let Some(c) = seg.child[e].as_ref() {
                __internal_debug_map(c, map, offset + seg.len / 2 * e);
            }
        }
    }
}

#[derive(Clone, Hash, PartialEq, Copy)]
pub struct SparseSegtreeDebugList<'a, T, S>(&'a Segtree<T, S>);
impl<'a, T: Clone + Debug, S: SparseSegtreeTrait<Value = T>> Debug
    for SparseSegtreeDebugList<'a, T, S>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut list = f.debug_list();
        if let Some(seg) = self.0.seg.as_ref() {
            let mut rest = seg.len;
            __internal_debug_list(seg, &mut list, &mut rest);
        }
        list.finish()
    }
}

fn __internal_debug_list<T: Clone + Debug, S: SparseSegtreeTrait<Value = T>>(
    seg: &Nonempty<T, S>,
    list: &mut DebugList<'_, '_>,
    rest: &mut usize,
) {
    if seg.len == 1 {
        list.entry(&seg.value);
        *rest -= 1;
    } else {
        for e in 0..2 {
            if let Some(c) = seg.child[e].as_ref() {
                __internal_debug_list(c, list, rest);
            } else {
                let take = (seg.len / 2).min(*rest);
                list.entries(repeat_with(S::id).take(seg.len).take(take));
                *rest -= take;
            }
        }
    }
}

fn __internal_open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
    (match range.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    })..match range.end_bound() {
        Bound::Excluded(&x) => x,
        Bound::Included(&x) => x + 1,
        Bound::Unbounded => len,
    }
}

pub trait SparseSegtreeTrait {
    type Value: Clone;
    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
    fn id() -> Self::Value;
}

#[cfg(test)]
mod tests {
    use {
        super::{Segtree, SparseSegtreeTrait},
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::SubRange,
    };

    enum Cat {}
    impl SparseSegtreeTrait for Cat {
        type Value = String;
        fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            lhs.chars().chain(rhs.chars()).collect::<String>()
        }
        fn id() -> Self::Value {
            String::new()
        }
    }

    #[test]
    fn test_seg() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..20);
            println!("n = {}", n);
            let mut a = vec![String::new(); n];
            let mut seg = Segtree::<_, Cat>::new(n.next_power_of_two());
            for iter in 0..2 * n {
                match rng.gen_range(0..2) {
                    0 => {
                        let i = rng.gen_range(0..n);
                        let s = ((b'a' + (iter % 26) as u8) as char).to_string();
                        println!("Modify {}, {}", i, &s);
                        a[i] = s.clone();
                        seg.set(i, s);
                    }
                    1 => {
                        let range = rng.sample(SubRange(0..n));
                        println!("Fold {:?}", &range);
                        let expected = a[range.clone()]
                            .iter()
                            .fold(Cat::id(), |x, y| Cat::op(&x, y));
                        let result = seg.fold(range);
                        assert_eq!(expected, result);
                    }
                    _ => unreachable!(),
                }
                println!("seg = {:?}", &seg);
                println!("seg = {:?}", seg.debug_list());
            }
            println!();
        }
    }
}
