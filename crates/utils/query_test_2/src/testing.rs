use crate::{solve, FromBrute, Gen, Query, RandNew};
use rand::Rng;
use std::{
    cell::{RefCell, RefMut},
    cmp::PartialEq,
    fmt::Debug,
    marker::PhantomData,
    ops::DerefMut,
};

mod checkers;
pub mod config;
use checkers::{Checker, InitPrinter, Preprinter, UnChecker};

#[derive(Debug, Clone, PartialEq)]
pub struct Tester<R, B, F, G> {
    rng: RefCell<R>,
    brute: B,
    fast: F,
    config: config::Config,
    marker: std::marker::PhantomData<G>,
}
impl<R, B, F, G> Tester<R, B, F, G>
where
    R: Rng,
    B: RandNew<G> + Debug,
    F: FromBrute<Brute = B> + Debug,
{
    pub fn rng_mut(&self) -> RefMut<R> {
        self.rng.borrow_mut()
    }
    pub fn new(mut rng: R, config: config::Config) -> Self {
        let brute = B::rand_new(&mut rng, PhantomData::<G>);
        let fast = F::from_brute(&brute);
        InitPrinter {
            brute: &brute,
            fast: &fast,
        }
        .print(config.initialize);
        Self {
            rng: RefCell::new(rng),
            brute,
            fast,
            config,
            marker: PhantomData::<G>,
        }
    }
    pub fn initialize(&mut self) {
        let brute = B::rand_new(self.rng_mut().deref_mut(), PhantomData::<G>);
        let fast = F::from_brute(&brute);
        InitPrinter {
            brute: &brute,
            fast: &fast,
        }
        .print(self.config.initialize);
        self.brute = brute;
        self.fast = fast;
    }
    pub fn compare<Q: Query>(&self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + solve::Solve<Q>,
        F: solve::Solve<Q>,
    {
        let param = self.brute.gen::<R>(self.rng_mut().deref_mut());
        self.preprint::<Q>(&param);
        let expected = self.brute.solve(param.clone());
        let result = self.fast.solve(param.clone());
        Checker {
            brute: &self.brute,
            fast: &self.fast,
            query_name: Q::NAME,
            expected,
            result,
            param,
        }
        .check(self.config)
    }
    pub fn judge<Q: Query>(&self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + solve::Solve<Q>,
        F: solve::Judge<Q>,
    {
        todo!();
    }
    pub fn mutate<Q: Query>(&mut self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + solve::Mutate<Q>,
        F: solve::Mutate<Q>,
    {
        let param = self.brute.gen::<R>(self.rng_mut().deref_mut());
        self.preprint::<Q>(&param);
        self.brute.mutate(param.clone());
        self.fast.mutate(param.clone());
        UnChecker {
            brute: &self.brute,
            fast: &self.fast,
            query_name: Q::NAME,
            param,
        }
        .uncheck(self.config.unchecked);
    }
    fn preprint<Q: Query>(&self, param: &Q::Param)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
    {
        if let Some(pre) = self.config.pre {
            Preprinter {
                brute: &self.brute,
                fast: &self.fast,
                query_name: Q::NAME,
                param: param.clone(),
            }
            .preprint(pre);
        }
    }
}
