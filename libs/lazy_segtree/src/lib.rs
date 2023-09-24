use std::cell::RefCell;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::{self};
use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;

#[derive(Clone)]
pub struct LazySegtree<T, U, Op, Apply, Compose, Identity, IdAction> {
    lg: u32,
    len: usize,
    table: RefCell<Box<[T]>>,
    lazy: RefCell<Box<[U]>>,
    op: Op,
    apply: Apply,
    compose: Compose,
    identity: Identity,
    id_action: IdAction,
}
pub struct LazySegtreeBuilder<'a, T, Op, Apply, Compose, Identity, IdAction> {
    pub slice: &'a [T],
    pub op: Op,
    pub apply: Apply,
    pub compose: Compose,
    pub identity: Identity,
    pub id_action: IdAction,
}
impl<'a, T, U, Op, Apply, Compose, Identity, IdAction>
    LazySegtreeBuilder<'a, T, Op, Apply, Compose, Identity, IdAction>
where
    T: Clone + Debug,
    U: Clone + Debug,
    Op: Fn(T, T) -> T,
    Apply: Fn(U, T) -> T,
    Compose: Fn(U, U) -> U,
    Identity: Fn() -> T,
    IdAction: Fn() -> U,
{
    pub fn finish(self) -> LazySegtree<T, U, Op, Apply, Compose, Identity, IdAction> {
        LazySegtree::new(
            self.slice,
            self.op,
            self.apply,
            self.compose,
            self.identity,
            self.id_action,
        )
    }
}

impl<T, U, Op, Apply, Compose, Identity, IdAction>
    LazySegtree<T, U, Op, Apply, Compose, Identity, IdAction>
where
    T: Clone + Debug,
    U: Clone + Debug,
    Op: Fn(T, T) -> T,
    Apply: Fn(U, T) -> T,
    Compose: Fn(U, U) -> U,
    Identity: Fn() -> T,
    IdAction: Fn() -> U,
{
    pub fn new(
        slice: &[T],
        op: Op,
        apply: Apply,
        compose: Compose,
        identity: Identity,
        id_action: IdAction,
    ) -> Self {
        let len = slice.len();
        let lg = len.next_power_of_two().trailing_zeros();
        let mut table = slice.to_vec();
        table.extend(slice.iter().cloned());
        let table = RefCell::new(table.into_boxed_slice());
        (1..len).rev().for_each(|i| {
            let x = op(
                table.borrow()[2 * i].clone(),
                table.borrow()[2 * i + 1].clone(),
            );
            table.borrow_mut()[i] = x;
        });
        #[allow(clippy::redundant_closure)]
        let lazy = RefCell::new(
            std::iter::repeat_with(|| id_action())
                .take(len)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        );
        Self {
            lg,
            len,
            table,
            lazy,
            op,
            apply,
            compose,
            identity,
            id_action,
        }
    }

    pub fn get(&self, i: usize) -> T { self.table.borrow()[self.len + i].clone() }

    pub fn modify(&mut self, i: usize, mut f: impl FnMut(&mut T)) {
        let i = self.len + i;
        (1..=self.lg).rev().for_each(|p| self.push(i >> p));
        f(&mut self.table.borrow_mut()[i]);
        (1..=self.lg).for_each(|p| self.update(i >> p));
    }

    pub fn fold(&self, range: impl RangeBounds<usize>) -> T {
        let Range { mut start, mut end } = open(range, self.len);
        start += self.len;
        end += self.len;
        self.thrust(start);
        self.thrust(end);
        let mut fl = (self.identity)();
        let mut fr = (self.identity)();
        while start != end {
            if start % 2 == 1 {
                fl = (self.op)(fl, self.table.borrow()[start].clone());
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                fr = (self.op)(self.table.borrow()[end].clone(), fr);
            }
            start /= 2;
            end /= 2;
        }
        (self.op)(fl, fr)
    }

    pub fn apply(&mut self, range: impl RangeBounds<usize>, actor: U) {
        let Range { mut start, mut end } = open(range, self.len);
        start += self.len;
        end += self.len;
        self.thrust(start);
        self.thrust(end);
        {
            let mut start = start;
            let mut end = end;
            while start != end {
                if start % 2 == 1 {
                    self.all_apply(start, actor.clone());
                    start += 1;
                }
                if end % 2 == 1 {
                    end -= 1;
                    self.all_apply(end, actor.clone());
                }
                start /= 2;
                end /= 2;
            }
        }
        for p in 1..=self.lg {
            if (start >> p) << p != start {
                self.update(start >> p);
            }
            if (end >> p) << p != end {
                self.update((end - 1) >> p);
            }
        }
    }

    pub fn to_vec(&self) -> Vec<T>
    where
        Self: Clone,
    {
        self.clone().into_vec()
    }

    pub fn into_vec(self) -> Vec<T> {
        (1..self.len).for_each(|i| self.push(i));
        (1..self.len).rev().for_each(|i| self.update(i));
        let len = self.len;
        let table = self.table;
        table.into_inner()[len..].to_vec()
    }

    fn update(&self, i: usize) {
        let x = (self.op)(
            self.table.borrow()[i * 2].clone(),
            self.table.borrow()[i * 2 + 1].clone(),
        );
        self.table.borrow_mut()[i] = x;
    }

    fn all_apply(&self, i: usize, f: U) {
        let x = (self.apply)(f.clone(), self.table.borrow()[i].clone());
        self.table.borrow_mut()[i] = x;
        if i < self.len {
            let x = (self.compose)(f, self.lazy.borrow()[i].clone());
            self.lazy.borrow_mut()[i] = x;
        }
    }

    fn push(&self, i: usize) {
        let lazy = std::mem::replace(&mut self.lazy.borrow_mut()[i], (self.id_action)());
        self.all_apply(2 * i, lazy.clone());
        self.all_apply(2 * i + 1, lazy);
    }

    fn thrust(&self, i: usize) {
        (1..=self.lg)
            .rev()
            .filter(|&p| (i >> p) << p != i)
            .for_each(|p| {
                self.push(i >> p);
            });
    }
}

fn open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
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

impl<T, U, Op, Apply, Compose, Identity, IdAction> Debug
    for LazySegtree<T, U, Op, Apply, Compose, Identity, IdAction>
where
    T: Clone + Debug,
    U: Clone + Debug,
    Op: Fn(T, T) -> T,
    Apply: Fn(U, T) -> T,
    Compose: Fn(U, U) -> U,
    Identity: Fn() -> T,
    IdAction: Fn() -> U,
{
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        w.debug_struct("LazySegtree")
            .field("table", &self.table.borrow())
            .field("lazy", &self.lazy.borrow())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::LazySegtree;
    use super::LazySegtreeBuilder;
    use rand::prelude::*;
    use randtools::SubRange;
    use std::fmt::Debug;
    use std::iter;

    #[test]
    fn test_index() {
        let seg = LazySegtreeBuilder {
            slice: &[0, 1],
            op: std::cmp::min,
            apply: std::ops::Add::add,
            compose: std::ops::Add::add,
            identity: || std::u32::MAX,
            id_action: || 0_u32,
        }
        .finish();
        assert_eq!(seg.get(0), 0);
        assert_eq!(seg.get(1), 1);
    }

    #[test]
    fn test_modify() {
        let mut seg = LazySegtreeBuilder {
            slice: &[0, 1],
            op: std::cmp::min,
            apply: std::ops::Add::add,
            compose: std::ops::Add::add,
            identity: || std::u32::MAX,
            id_action: || 0_u32,
        }
        .finish();
        seg.modify(0, |x| *x = 10);
        seg.modify(1, |x| *x = 11);
        assert_eq!(seg.to_vec().as_slice(), &[10, 11]);
        seg.modify(0, |x| *x = 20);
        seg.modify(1, |x| *x = 21);
        assert_eq!(seg.to_vec().as_slice(), &[20, 21]);
    }

    #[test]
    fn test_min_add() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..40);
            let mut a = iter::repeat_with(|| rng.gen_range(0_u32..30))
                .take(n)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            let mut seg = LazySegtreeBuilder {
                slice: &a,
                op: std::cmp::min,
                apply: std::ops::Add::add,
                compose: std::ops::Add::add,
                identity: || std::u32::MAX,
                id_action: || 0_u32,
            }
            .finish();
            println!("a = {:?}", &a);
            println!("seg = {:?}", debug_collect(&seg));
            for _ in 0..20 {
                match rng.gen_range(0..3) {
                    0 => {
                        let i = rng.gen_range(0..n);
                        let x = rng.gen_range(0..30);
                        println!("Set via modify {} {}", &i, x);
                        seg.modify(i, |y| *y = x);
                        a[i] = x;

                        let collected = debug_collect(&seg);
                        println!("seg = {:?}", &collected);
                        assert_eq!(&a, &collected);
                    }
                    1 => {
                        let range = rng.sample(SubRange(0..n));
                        println!("Fold {:?}", &range);
                        let result = seg.fold(range.clone());
                        let expected = a[range].iter().copied().min().unwrap_or(std::u32::MAX);
                        assert_eq!(result, expected);
                    }
                    2 => {
                        let range = rng.sample(SubRange(0..n));
                        let f = rng.gen_range(0..30);
                        println!("Apply {:?} {}", &range, f);
                        seg.apply(range.clone(), f);
                        a[range].iter_mut().for_each(|x| *x += f);

                        let collected = debug_collect(&seg);
                        println!("seg = {:?}", &collected);
                        assert_eq!(&a, &collected);
                    }
                    _ => panic!(),
                }
                validate(&seg);
            }
        }
    }

    #[test]
    fn test_to_vec() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..40);
            let mut a = iter::repeat_with(|| rng.gen_range(0_u32..30))
                .take(n)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            let mut seg = LazySegtreeBuilder {
                slice: &a,
                op: std::cmp::min,
                apply: std::ops::Add::add,
                compose: std::ops::Add::add,
                identity: || std::u32::MAX,
                id_action: || 0_u32,
            }
            .finish();
            println!("a = {:?}", &a);
            println!("seg = {:?}", debug_collect(&seg));
            for _ in 0..20 {
                let range = rng.sample(SubRange(0..n));
                let f = rng.gen_range(0..30);
                println!("Apply {:?} {}", &range, f);
                seg.apply(range.clone(), f);
                a[range].iter_mut().for_each(|x| *x += f);

                let collected = debug_collect(&seg);
                println!("seg = {:?}", &collected);
                assert_eq!(&a, &collected);
                validate(&seg);
            }
            assert_eq!(seg.to_vec().into_boxed_slice(), a);
        }
    }

    fn validate<T, U, Op, Apply, Compose, Identity, IdAction>(
        seg: &LazySegtree<T, U, Op, Apply, Compose, Identity, IdAction>,
    ) where
        T: Clone + Debug + PartialEq,
        U: Clone + Debug,
        Op: Fn(T, T) -> T,
        Apply: Fn(U, T) -> T,
        Compose: Fn(U, U) -> U,
        Identity: Fn() -> T,
        IdAction: Fn() -> U,
    {
        for i in (1..seg.len).rev() {
            let expeted = (seg.apply)(
                seg.lazy.borrow()[i].clone(),
                (seg.op)(
                    seg.table.borrow()[2 * i].clone(),
                    seg.table.borrow()[2 * i + 1].clone(),
                ),
            );
            let result = seg.table.borrow()[i].clone();
            assert_eq!(
                &result, &expeted,
                "Validation failed: i = {}, seg = {:?}",
                i, &seg
            );
        }
    }

    fn debug_collect<T, U, Op, Apply, Compose, Identity, IdAction>(
        seg: &LazySegtree<T, U, Op, Apply, Compose, Identity, IdAction>,
    ) -> Box<[T]>
    where
        T: Clone + Debug + Default,
        U: Clone + Debug,
        Op: Fn(T, T) -> T,
        Apply: Fn(U, T) -> T,
        Compose: Fn(U, U) -> U,
        Identity: Fn() -> T,
        IdAction: Fn() -> U,
    {
        (0..seg.len)
            .map(|i| seg.len + i)
            .map(|i| {
                let mut x = seg.table.borrow()[i].clone();
                (1..=seg.lg)
                    .rev()
                    .for_each(|p| x = (seg.apply)(seg.lazy.borrow()[i >> p].clone(), x.clone()));
                x
            })
            .collect::<Vec<_>>()
            .into_boxed_slice()
    }
}
