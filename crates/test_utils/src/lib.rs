use rand::Rng;
use std::{fmt, marker};

pub struct Test<A, B, R, GenInstance, Construct>
where
    GenInstance: Fn(&mut R) -> A,
    Construct: Fn(&A) -> B,
{
    pub test_count: usize,
    pub query_count: usize,
    pub gen_instance: GenInstance,
    pub construct: Construct,
    pub queries: Omikuji<Box<dyn Query<A, B, R>>>,
}

impl<A, B, R, GenInstance, Construct> Test<A, B, R, GenInstance, Construct>
where
    GenInstance: Fn(&mut R) -> A,
    Construct: Fn(&A) -> B,
{
    pub fn run(&self, rng: &mut R)
    where
        R: Rng,
        A: fmt::Debug,
        B: fmt::Debug,
    {
        for test_number in 0..self.test_count {
            eprintln!("Test number {}", test_number);

            let mut instance = (self.gen_instance)(rng);
            eprintln!("Created an instance. {:?}", &instance);

            let mut data_structure = (self.construct)(&instance);
            eprintln!("Built a data structure. {:?}", &data_structure);

            eprintln!();
            for query_number in 0..self.query_count {
                eprintln!("Query number {}", query_number);
                let query = self.queries.draw(rng);
                query.run(&mut instance, &mut data_structure, rng);
            }
            eprintln!();
        }
    }
}

#[derive(Debug, Clone)]
pub struct Omikuji<T>(Vec<(u32, T)>);

impl<T> Omikuji<T> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    fn draw(&self, rng: &mut impl Rng) -> &T {
        let lim = self.0.last().map(|&(x, _)| x).unwrap_or(0);
        let dice = rng.gen_range(0, lim);
        &self.0.iter().find(|&&(x, _)| dice <= x).unwrap().1
    }

    pub fn push(&mut self, mut probability: u32, content: T) {
        probability += self.0.last().map(|&(x, _)| x).unwrap_or(0);
        self.0.push((probability, content));
    }
}

impl<T> Default for Omikuji<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub trait Query<A, B, R> {
    fn run(&self, instance: &mut A, data_structure: &mut B, rng: &mut R);
}

pub struct QueryImpl<'a, A, B, C, Q, R, GenQuery, Brute, Fast>
where
    GenQuery: Fn(&A, &mut R) -> Q,
    Brute: Fn(&mut A, &Q) -> C,
    Fast: Fn(&mut B, &Q) -> C,
{
    pub name: &'a str,
    pub gen_query: GenQuery,
    pub brute: Brute,
    pub fast: Fast,
    pub marker: marker::PhantomData<(A, B, C, Q, R)>,
}

impl<'a, A, B, C, Q, R, GenQuery, Brute, Fast> Query<A, B, R>
    for QueryImpl<'a, A, B, C, Q, R, GenQuery, Brute, Fast>
where
    C: fmt::Debug + Eq,
    Q: fmt::Debug,
    GenQuery: Fn(&A, &mut R) -> Q,
    Brute: Fn(&mut A, &Q) -> C,
    Fast: Fn(&mut B, &Q) -> C,
{
    fn run(&self, instance: &mut A, data_structure: &mut B, rng: &mut R) {
        eprintln!("\tName: {}", self.name);

        let query = (self.gen_query)(instance, rng);
        eprintln!("\tQuery: {:?}", &query);

        let expected = (self.brute)(instance, &query);
        eprintln!("\tExpected: {:?}", &expected);

        let result = (self.fast)(data_structure, &query);
        eprintln!("\tResult: {:?}", &result);
        eprintln!();

        assert_eq!(expected, result);
    }
}
