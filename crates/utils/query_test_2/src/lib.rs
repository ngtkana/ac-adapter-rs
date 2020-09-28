#![warn(missing_docs)]
/*!
クエリ形式のテストを支援するライブラリです。
*/

use rand::prelude::*;
use solve::*;
use std::{cell::RefMut, cmp::PartialEq, fmt::Debug, marker::PhantomData, ops::DerefMut};

/// パラメータを受け取ってデータ構造を構築したりクエリを受け取って回答したりするものがたくさんあります。
pub mod ds;

/// 具体的なクエリ型定義の倉庫です。
pub mod query;

/// クエリの回答形式です。
pub mod solve;

/// 生成するものです。
pub mod gen;

/// クエリです。
pub trait Query {
    /// クエリのパラメータ型です。
    type Param;
    /// クエリの出力型です。
    type Output;
    /// クエリのお名前です。
    const NAME: &'static str;
}

/// クエリを生成します。
pub trait Gen<Q: Query> {
    #[allow(missing_docs)]
    fn gen(&self) -> Q::Param;
}

/// ランダム生成です。
pub trait RandNew<G> {
    #[allow(missing_docs)]
    fn rand_new<R: Rng>(rng: &mut R, marker: PhantomData<G>) -> Self;
}

/// テストをします。
pub trait Test {
    /// 乱数生成器型です。
    type Rng: Rng;

    /// 愚直型です。
    type Brute;

    /// 乱数生成器への可変参照を返します。
    fn rng_mut(&self) -> RefMut<Self::Rng>;

    /// 愚直への参照を返します。
    fn brute(&self) -> &Self::Brute;

    /// 愚直への可変参照を返しいます。
    fn brute_mut(&mut self) -> &mut Self::Brute;

    /// 現在のインスタンスの状態をチェックです。
    fn damp(&self)
    where
        Self::Brute: Debug,
    {
        println!("Brute: {:?}", self.brute());
    }

    /// 愚直を生成し直します。
    fn regenerate<G>(&mut self)
    where
        Self::Brute: RandNew<G>,
    {
        let brute =
            Self::Brute::rand_new::<Self::Rng>(self.rng_mut().deref_mut(), PhantomData::<G>);
        *self.brute_mut() = brute;
    }

    /// クエリのテストをします。
    #[allow(clippy::unit_cmp)]
    fn test_get<Q: Query, A>(&self, fast: &A, _marker: PhantomData<Q>)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        Self: Gen<Q>,
        A: SolveGet<Q>,
        Self::Brute: SolveGet<Q>,
    {
        let query = self.gen();
        let expected = self.brute().solve_get(query.clone());
        let result = fast.solve_get(query.clone());
        println!(
            "Query = ({} {:?}), expected = {:?}, result = {:?}",
            Q::NAME,
            &query,
            &expected,
            &result
        );
        assert_eq!(expected, result);
    }

    /// クエリのテストをします。
    #[allow(clippy::unit_cmp)]
    fn test_mutate<Q: Query, A>(&mut self, fast: &mut A, _marker: PhantomData<Q>)
    where
        Q::Param: Clone + Debug,
        Q::Output: Clone + Debug + PartialEq,
        Self: Gen<Q>,
        A: SolveMut<Q>,
        Self::Brute: SolveMut<Q>,
    {
        let query = self.gen();
        let expected = self.brute_mut().solve_mut(query.clone());
        let result = fast.solve_mut(query.clone());
        println!(
            "Query = ({} {:?}), expected = {:?}, result = {:?}",
            Q::NAME,
            &query,
            &expected,
            &result
        );
        assert_eq!(expected, result);
    }
}
