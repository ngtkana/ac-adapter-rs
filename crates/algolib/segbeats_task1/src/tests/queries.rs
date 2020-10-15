use query_test::{query, Query};
use std::{
    marker::PhantomData,
    ops::{Add, AddAssign, Range},
};

#[query(fn(Range<usize>, T))]
pub struct ChangeMin<T: Ord>(PhantomData<T>);

#[query(fn(Range<usize>) -> T)]
pub struct QueryMax<T: Ord>(PhantomData<T>);

#[query(fn(Range<usize>) -> T)]
pub struct QuerySum<T: Add<Output = T> + AddAssign>(PhantomData<T>);
