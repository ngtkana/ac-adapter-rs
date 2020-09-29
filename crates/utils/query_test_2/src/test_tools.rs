use crate::*;
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
    pub fn rng_mut(&self) -> RefMut<R> {
        self.rng.borrow_mut()
    }
}

macro_rules! method_block_check {
    ($self:ident, $solve_method:ident) => {{
        let param = $self.brute.gen::<R>($self.rng_mut().deref_mut());
        $self.preprint::<Q>(&param);
        let expected = $self.brute.$solve_method(param.clone()).clone();
        let result = $self.fast.$solve_method(param.clone()).clone();
        Checker {
            brute: &$self.brute,
            fast: &$self.fast,
            query_name: Q::NAME,
            expected,
            result,
            param,
        }
        .check($self.config)
    }};
}

macro_rules! method_block_uncheck {
    ($self:ident, $solve_method:ident) => {{
        let param = $self.brute.gen::<R>($self.rng_mut().deref_mut());
        $self.preprint::<Q>(&param);
        let _: () = $self.brute.$solve_method(param.clone()).clone();
        let _: () = $self.fast.$solve_method(param.clone()).clone();
        UnChecker {
            brute: &$self.brute,
            fast: &$self.fast,
            query_name: Q::NAME,
            param,
        }
        .uncheck($self.config.unchecked);
    }};
}

impl<R, B, F, G> Tester<R, B, F, G>
where
    R: Rng,
    B: RandNew<G> + Debug,
    F: FromBrute<Brute = B> + Debug,
{
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
    pub fn test<Q: Query>(&self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + Solve<Q>,
        F: Solve<Q>,
    {
        method_block_check!(self, solve)
    }
    pub fn test_get<Q: Query>(&self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + SolveGet<Q>,
        F: SolveGet<Q>,
    {
        method_block_check!(self, solve_get)
    }
    pub fn test_mut<Q: Query>(&mut self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + SolveMut<Q>,
        F: SolveMut<Q>,
    {
        method_block_uncheck!(self, solve_mut)
    }
}
