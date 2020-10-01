use crate::{solve, FromBrute, Gen, Query, RandNew};
use rand::Rng;
use std::{
    cell::{RefCell, RefMut},
    cmp::PartialEq,
    fmt::Debug,
    marker::PhantomData,
    ops::DerefMut,
};

pub mod config;
mod logger;

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
    B: RandNew<G> + Debug + Clone,
    F: FromBrute<Brute = B> + Debug + Clone,
{
    pub fn rng_mut(&self) -> RefMut<R> {
        self.rng.borrow_mut()
    }
    pub fn new(mut rng: R, config: config::Config) -> Self {
        let brute = B::rand_new(&mut rng, PhantomData::<G>);
        let fast = F::from_brute(&brute);
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
        self.brute = brute;
        self.fast = fast;
    }
    pub fn compare<Q: Query>(&self)
    where
        Q::Param: Clone + Debug + Clone,
        Q::Output: Clone + Debug + Clone + PartialEq,
        B: Gen<Q, G> + solve::Solve<Q>,
        F: solve::Solve<Q>,
    {
        let param = self.brute.gen::<R>(self.rng_mut().deref_mut());
        let expected = self.brute.solve(param.clone());
        let output = self.fast.solve(param.clone());

        let verdict = &expected == &output;
        let logger = logger::Logger {
            tester: self,
            param,
            output: Some(output),
            expected: Some(expected),
            marker: PhantomData::<Q>,
        };
        match verdict {
            true => logger.passing(),
            false => {
                logger.failing();
                panic!("Failed in a test.");
            }
        }
    }
    pub fn judge<Q: Query>(&self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + solve::Judge<Q>,
        F: solve::Solve<Q>,
    {
        let param = self.brute.gen::<R>(self.rng_mut().deref_mut());
        let output = self.fast.solve(param.clone());
        let verdict = self.brute.judge(param.clone(), output.clone());
        let logger = logger::Logger {
            tester: self,
            param,
            output: Some(output),
            expected: None,
            marker: PhantomData::<Q>,
        };
        match verdict {
            true => logger.passing(),
            false => {
                logger.failing();
                panic!("Failed in a test.");
            }
        }
    }
    pub fn mutate<Q: Query>(&mut self)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        B: Gen<Q, G> + solve::Mutate<Q>,
        F: solve::Mutate<Q>,
    {
        let param = self.brute.gen::<R>(self.rng_mut().deref_mut());
        self.brute.mutate(param.clone());
        self.fast.mutate(param.clone());
        logger::Logger {
            tester: self,
            param,
            output: None,
            expected: None,
            marker: PhantomData::<Q>,
        }
        .mutate();
    }
}

trait Test {
    type Brute;
    type Fast;
    fn brute(&self) -> &Self::Brute;
    fn fast(&self) -> &Self::Fast;
    fn config(&self) -> config::Config;
}
impl<R, B, F, G> Test for Tester<R, B, F, G> {
    type Brute = B;
    type Fast = F;
    fn brute(&self) -> &B {
        &self.brute
    }
    fn fast(&self) -> &F {
        &self.fast
    }
    fn config(&self) -> config::Config {
        self.config
    }
}
