use crate::{
    gen::{GenLen, GenValue},
    query::{Get, Set},
    solve::{SolveGet, SolveMut},
    Gen, RandNew, Test,
};
use rand::prelude::*;
use std::{
    cell::{RefCell, RefMut},
    fmt::Debug,
    marker::PhantomData,
    ops::DerefMut,
};

/// 配列データ構造です。
pub trait Array<T>: SolveGet<Get<T>> + SolveMut<Set<T>> {}

/// 配列データ構造の愚直です。
pub type Brute<T> = Vec<T>;
impl<T> SolveGet<Get<T>> for Brute<T> {
    fn solve_get(&self, i: usize) -> &T {
        &self[i]
    }
}
impl<T> SolveMut<Set<T>> for Brute<T> {
    fn solve_mut(&mut self, (i, x): (usize, T)) {
        self[i] = x;
    }
}
impl<T, G: GenLen + GenValue<T>> RandNew<G> for Brute<T> {
    fn rand_new<R: Rng>(rng: &mut R, _marker: PhantomData<G>) -> Self {
        let len = G::gen_len(rng);
        std::iter::repeat_with(|| G::gen_value(rng))
            .take(len)
            .collect()
    }
}

/// 配列データ構造のテスターです。
///
/// TODO: 他のデータ構造と共通化します。
pub struct Tester<R, T, G> {
    rng: RefCell<R>,
    brute: Brute<T>,
    marker: PhantomData<G>,
}
impl<R: Rng, T, G> Test for Tester<R, T, G> {
    type Rng = R;
    type Brute = Brute<T>;
    fn rng_mut(&self) -> RefMut<Self::Rng> {
        self.rng.borrow_mut()
    }
    fn brute(&self) -> &Self::Brute {
        &self.brute
    }
    fn brute_mut(&mut self) -> &mut Self::Brute {
        &mut self.brute
    }
}
impl<R, T, G> Tester<R, T, G>
where
    R: Rng,
    T: Debug,
    G: GenLen + GenValue<T>,
{
    /// テスターを構築します。
    pub fn new(mut rng: R, marker: PhantomData<G>) -> Self {
        Self {
            brute: Brute::rand_new(&mut rng, PhantomData::<G>),
            rng: RefCell::new(rng),
            marker,
        }
    }
}
impl<R: Rng, T, G> Tester<R, T, G> {
    fn gen_index(&self) -> usize {
        self.rng.borrow_mut().gen_range(0, self.brute.len())
    }
}
impl<R: Rng, T, G> Gen<Get<T>> for Tester<R, T, G> {
    fn gen(&self) -> usize {
        self.gen_index()
    }
}
impl<R: Rng, T, G: GenValue<T>> Gen<Set<T>> for Tester<R, T, G> {
    fn gen(&self) -> (usize, T) {
        (
            self.gen_index(),
            G::gen_value(self.rng.borrow_mut().deref_mut()),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone, PartialEq)]
    struct Reverse<T>(Vec<T>);
    impl<T: Clone> Reverse<T> {
        pub fn from_brute(brute: &Brute<T>) -> Self {
            let mut res = brute.to_vec();
            res.reverse();
            Reverse(res)
        }
    }
    impl<T> SolveGet<Get<T>> for Reverse<T> {
        fn solve_get(&self, i: usize) -> &T {
            &self.0[self.0.len() - i - 1]
        }
    }
    impl<T> SolveMut<Set<T>> for Reverse<T> {
        fn solve_mut(&mut self, (i, x): (usize, T)) {
            let len = self.0.len();
            self.0[len - i - 1] = x;
        }
    }

    #[test]
    fn test_u32() {
        struct G {}
        impl GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(0, 8)
            }
        }
        impl GenValue<u32> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> u32 {
                rng.gen_range(0, 256)
            }
        }

        let mut tester = Tester::new(StdRng::seed_from_u64(42), PhantomData::<G>);
        let mut fast = Reverse::from_brute(&tester.brute());
        for _ in 0..20 {
            let command = tester.rng.borrow_mut().gen_range(0, 3);
            match command {
                0 => tester.test_get(&fast, PhantomData::<Get<u32>>),
                1 => tester.test_mutate(&mut fast, PhantomData::<Set<u32>>),
                2 => tester.damp(),
                _ => unreachable!(),
            }
        }
    }
}
