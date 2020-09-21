//! データ構造のテストのためのフレームワークです。
//!
//! # 使い方
//!
//! ## 用意するもの
//!
//! これら 3 つを定義し、各種クエリを同名のメソッドとして定義すると、
//! [`query`] マクロによるダックタイイングでテストをすることができます。
//!
//! - テストしたい構造体
//! - 比較対象の構造体
//! - クエリを作る構造体
//!
//! # テストがひとつしかない（典型的にはノンジェネリックな場合）
//!
//! `UnionFind` を例にご説明します。
//!
//! テストしたい構造体はあるとして、比較対象の構造体を作っていきます。
//!
//! ```
//! #[derive(Debug, Clone, PartialEq)]
//! struct Brute(Vec<Vec<usize>>);
//! impl Brute {
//!     fn new(len: usize) -> Self {
//!         Self((0..len).map(|i| vec![i]).collect())
//!     }
//!     fn find(&self, i: usize) -> usize {
//!         self.0
//!             .iter()
//!             .position(|v| v.iter().any(|&x| x == i))
//!             .unwrap()
//!     }
//!     fn unite(&mut self, x: usize, y: usize) -> bool {
//!         let i = self.find(x);
//!         let j = self.find(y);
//!         if i == j {
//!             false
//!         } else {
//!             let v = self.0.remove(i.max(j));
//!             self.0[i.min(j)].extend(v);
//!             true
//!         }
//!     }
//! }
//! ```
//!
//! 次に、比較対象の構造体を定義します。
//! クエリの内容を返すような構造体を定義します。
//! 乱数生成器をフィールドに持っていることが多いでしょう。
//! また、今回は長さがわかる必要がありますから、それも持っていただきます。
//!
//! ```
//! use rand::prelude::*;
//! struct Query<'a> {
//!     pub len: usize,
//!     pub rng: &'a mut StdRng,
//! }
//! impl<'a> Query<'a> {
//!     fn unite(&mut self) -> (usize, usize) {
//!         (
//!             self.rng.gen_range(0, self.len),
//!             self.rng.gen_range(0, self.len),
//!         )
//!     }
//! }
//! ```
//!
//! これらが揃うと次のように、[`query`] マクロでテストをすることができます。
//!
//! ```
//! # use rand::prelude::*;
//! #
//! # #[derive(Debug, Clone, PartialEq)]
//! # struct UnionFind {
//! #     table: Vec<isize>,
//! # }
//! # impl UnionFind {
//! #     fn new(len: usize) -> Self {
//! #         Self {
//! #             table: vec![-1; len],
//! #         }
//! #     }
//! #     fn size(&mut self, mut i: usize) -> usize {
//! #         i = self.root(i);
//! #         (-self.table[i]) as usize
//! #     }
//! #     fn root(&mut self, i: usize) -> usize {
//! #         if self.table[i] < 0 {
//! #             i
//! #         } else {
//! #             let p = self.table[i] as usize;
//! #             let root = self.root(p);
//! #             self.table[i] = root as isize;
//! #             root
//! #         }
//! #     }
//! #     fn unite(&mut self, mut i: usize, mut j: usize) -> bool {
//! #         i = self.root(i);
//! #         j = self.root(j);
//! #         if i == j {
//! #             false
//! #         } else {
//! #             if self.size(i) < self.size(j) {
//! #                 std::mem::swap(&mut i, &mut j);
//! #             }
//! #             self.table[i] += self.table[j];
//! #             self.table[j] = i as isize;
//! #             true
//! #         }
//! #     }
//! # }
//! #
//! # #[derive(Debug, Clone, PartialEq)]
//! # struct Brute(Vec<Vec<usize>>);
//! # impl Brute {
//! #     fn new(len: usize) -> Self {
//! #         Self((0..len).map(|i| vec![i]).collect())
//! #     }
//! #     fn find(&self, i: usize) -> usize {
//! #         self.0
//! #             .iter()
//! #             .position(|v| v.iter().any(|&x| x == i))
//! #             .unwrap()
//! #     }
//! #     fn unite(&mut self, x: usize, y: usize) -> bool {
//! #         let i = self.find(x);
//! #         let j = self.find(y);
//! #         if i == j {
//! #             false
//! #         } else {
//! #             let v = self.0.remove(i.max(j));
//! #             self.0[i.min(j)].extend(v);
//! #             true
//! #         }
//! #     }
//! # }
//! #
//! # struct Query<'a> {
//! #     pub len: usize,
//! #     pub rng: &'a mut StdRng,
//! # }
//! # impl<'a> Query<'a> {
//! #     fn unite(&mut self) -> (usize, usize) {
//! #         (
//! #             self.rng.gen_range(0, self.len),
//! #             self.rng.gen_range(0, self.len),
//! #         )
//! #     }
//! # }
//! #
//! use query_test::query;
//! #[test]
//! fn test_uf_rand() {
//!     let mut rng = StdRng::seed_from_u64(42);
//!     for _ in 0..20 {
//!         let len = rng.gen_range(1, 20);
//!         let mut instance = query_test::Instance {
//!             query: Query {
//!                 len: len,
//!                 rng: &mut rng,
//!             },
//!             brute: Brute::new(len),
//!             fast: UnionFind::new(len),
//!         };
//!         for _ in 0..20 {
//!             match instance.query.rng.gen_range(0, 100) {
//!                 0..=99 => instance.apply(query!(unite, u, v)),
//!                 _ => unreachable!(),
//!             }
//!         }
//!     }
//! }
//! ```
//!
//! すると、`--nocapture` つきでテストをすると、このようにログが出てくることでしょう。
//!
//! ```ignore
//! Query = (unite (3, 3)), expected = false, result = false
//! Query = (unite (2, 3)), expected = true, result = true
//! Query = (unite (0, 2)), expected = true, result = true
//! ...
//! ```
//!
//! # テストが複数ある場合（典型的には、ジェネリックな場合）
//!
//! 先程 `Fast` と書いたもの、`Brute` と書いたものは、テストがいくつあっても使い回せるはずです。
//! 一方、`Query` はテストをたくさん作るとその数だけ定義する必要があり、それがとても大変かもしれません。
//!
//! それを楽にするにはこのように、`Query` 構造体の満たすべきトレイトを作っておくとよいです。
//! メソッド定義がかなり省略できるはずです。
//!
//! ```
//! use std::{iter, ops};
//! use rand::prelude::*;
//! trait SegQuery<'a> {
//!     type Value;
//!     type Rng: Rng;
//!
//!     // Required methods
//!     fn new(len: usize, rng: &'a mut Self::Rng) -> Self;
//!     fn rng(&mut self) -> &mut Self::Rng;
//!     fn len(&self) -> usize;
//!     fn gen_value(&mut self) -> Self::Value;
//!
//!     // Helper methods
//!     fn gen_index(&mut self) -> usize {
//!         let len = self.len();
//!         self.rng().gen_range(0, len)
//!     }
//!     fn gen_range(&mut self) -> ops::Range<usize> {
//!         let u = self.gen_index();
//!         let v = self.gen_index();
//!         u.min(v)..u.max(v)
//!     }
//!
//!     // Useful methods
//!     fn construct(&mut self) -> Vec<Self::Value> {
//!         let len = self.len();
//!         iter::repeat_with(|| self.gen_value()).take(len).collect()
//!     }
//!     fn set(&mut self) -> (usize, Self::Value) {
//!         let i = self.gen_index();
//!         let x = self.gen_value();
//!         (i, x)
//!     }
//!     fn get(&mut self) -> usize {
//!         self.gen_index()
//!     }
//!     fn fold(&mut self) -> ops::Range<usize> {
//!         self.gen_range()
//!     }
//! }
//! ```
//!
//! インスタンスを作るところを関数化したり、クエリ用トレイトの必須メソッドの実装を
//! マクロにしたりなどすると、更に短くなるでしょう。
//!
//! [`query`]: macro.query.html

/// For only internal use
#[macro_export]
macro_rules! print_query_without_nl {
    ($instance:ident, $name:ident, ($($query:ident),*)) => {
        print!(
            "Query = ({} {:?}),\t",
            stringify!($name),
            ($(&$query),*),
        );
    };
}

/// For only internal use
#[macro_export]
macro_rules! print_results {
    ($result:expr, $expected:expr) => {
        println!("Result = {:?}, Expected = {:?}", $result, $expected);
    };
}

/// For only internal use
#[macro_export]
macro_rules! query_assert {
    ($instance:ident, $name:ident, $expected:ident, $result:ident, ($($query:ident),*)) => {
        if &$expected != &$result {
            panic!(
                "Failed in a test!\n\tbrute = {:?},\n\tfast = {:?},\n\tquery = ({} {:?})\n\texpected = {:?}\n\tresult = {:?}",
                $instance.brute,
                $instance.fast,
                stringify!($name),
                ($(&$query),*),
                &$expected,
                &$result,
            );
        }
    }
}

/// クエリを表す、クロージャを返します。
///
/// # 使い方
///
/// `(クエリのお名前, args..)` を渡すとクロージャができますから、それを [`Instance`] のメソッド
/// [`apply`] にお渡しすると良いです。
///
/// # Examples
///
/// 例えばこれらのコードは等価です。
///
/// ```ignore
/// query!(set, i, x);
/// ```
///
/// ```ignore
/// |instance| {
///     let (i, x) = query.set();
///     let expected = instance.brute.set().clone();
///     let result = instance.fast.set().clone();
///     println!(
///         "Query = ({} {:?}), expected = {:?}, result = {:?}",
///         stringify!(set),
///         (&i, &x),
///         &expected,
///         &result,
///     );
///     if &expected != &result {
///         panic!(
///             "Failed in a test!\n\tbrute = {:?},\n\tfast = {:?},\n\tquery = ({} {:?})\n\texpected = {:?}\n\tresult = {:?}",
///             instance.brute,
///             instance.fast,
///             stringify!(set),
///             (&i, &x),
///             &expected,
///             &result,
///         );
///     }
/// }
/// ```
///
/// [`Instance`]: struct.Instance.html
/// [`apply`]: struct.Instance.html#method.apply
#[macro_export]
macro_rules! query {
    // 引数の数が 0 つの場合
    ($name:ident) => {
        |instance| {
            let () = instance.query.$name();
            $crate::print_query_without_nl!(instance, $name, ());
            let expected = instance.brute.$name().clone();
            let result = instance.fast.$name().clone();
            $crate::print_results!(result, expected);
            $crate::query_assert!(instance, $name, expected, result, ());
        };
    };
    // 引数の数が 1 つの場合
    ($name:ident, $arg:ident) => {
        |instance| {
            let $arg = instance.query.$name();
            $crate::print_query_without_nl!(instance, $name, ($arg));
            let expected = instance.brute.$name($arg.clone()).clone();
            let result = instance.fast.$name($arg.clone()).clone();
            $crate::print_results!(result, expected);
            $crate::query_assert!(instance, $name, expected, result, ($arg));
        };
    };
    // 引数の数が 2 つ以上の場合
    ($name:ident, $head:ident, $($tails:ident),*) => {
        |instance| {
            let ($head, $($tails),*) = instance.query.$name();
            $crate::print_query_without_nl!(instance, $name, ($head, $($tails),*));
            let expected = instance.brute.$name($head.clone(), $($tails.clone()),*).clone();
            let result = instance.fast.$name($head.clone(), $($tails.clone()),*).clone();
            $crate::print_results!(result, expected);
            $crate::query_assert!(instance, $name, expected, result, ($head, $($tails),*));
        };
    };
    // 引数の数が 2 つで、(value, ref) な場合です。（アドホックをやめませんか？）
    ($name:ident, $head:ident, ref $tail:ident) => {
        |instance| {
            let ($head, $tail) = instance.query.$name();
            $crate::print_query_without_nl!(instance, $name, ($head, $tail));
            let expected = instance.brute.$name($head.clone(), &$tail.clone()).clone();
            let result = instance.fast.$name($head.clone(), &$tail).clone();
            $crate::print_results!(result, expected);
            $crate::query_assert!(instance, $name, expected, result, ($head, $tail));
        };
    };
    // 引数の数が 2 つ + 3 つめが定数な場合です。（アドホックをやめませんか？）
    ($name:ident, $head:ident, $tail:ident, @bind $bind:expr) => {
        |instance| {
            let ($head, $tail) = instance.query.$name();
            $crate::print_query_without_nl!(instance, $name, ($head, $tail));
            let expected = instance.brute.$name($head.clone(), &$tail.clone(), $bind).clone();
            let result = instance.fast.$name($head.clone(), &$tail, $bind).clone();
            $crate::print_results!(result, expected);
            $crate::query_assert!(instance, $name, expected, result, ($head, $tail));
        };
    };
}

/// テストに必要な 3 つの構造体を束ねる型です。
#[derive(Debug, Clone)]
pub struct Instance<Q, Brute, Fast> {
    pub query: Q,
    pub brute: Brute,
    pub fast: Fast,
}

impl<Q, Brute, Fast> Instance<Q, Brute, Fast> {
    /// 自分自身に適用します。[`query`](macro.query.html) マクロと併用することが意図されています。
    pub fn apply(&mut self, f: impl Fn(&mut Self)) {
        f(self)
    }
}
