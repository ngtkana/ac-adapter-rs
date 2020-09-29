// #![warn(missing_docs)]
/*!
クエリ形式のテストを支援するライブラリです。
*/

use rand::prelude::*;
use std::marker::PhantomData;

mod ds;
/// 具体的なクエリ型定義の倉庫です。
pub mod query;
mod solve;
mod test_tools;
pub use solve::*;
mod gen;

use config::{Checked, Config, Unchecked};
pub use ds::vector::Vector;
/// 愚直と比較をしてテストをするためのツールです。
pub use test_tools::{config, Tester};

pub const CONFIG: Config = Config {
    pre: None,
    failing: Checked::Verbose,
    passing: Checked::Short,
    unchecked: Unchecked::Short,
};

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
pub trait Gen<Q: Query, G> {
    fn gen<R: Rng>(&self, rng: &mut R) -> Q::Param;
}

/// ランダム生成です。
pub trait RandNew<G> {
    fn rand_new<R: Rng>(rng: &mut R, marker: PhantomData<G>) -> Self;
}

/// `Brute` 構造体から変換します。
pub trait FromBrute {
    type Brute;
    fn from_brute(brute: &Self::Brute) -> Self;
}
