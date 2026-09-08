//! 素集合データ構造（Union-Find）。頂点を非交差な集合に分け、併合・同一判定を高速に行う
//!
//! 各集合を根付き木で表現し、経路圧縮と union by size を組み合わせることで、
//! 木の高さを低く抑える。これにより find・union は償却 $O(\alpha(n))$
//! （$\alpha$ はアッカーマン関数の逆関数）で完了し、$m$ 回の操作全体では
//! $O(m \alpha(n))$ に収まる。
//!
//! # 仕様
//! - [`UnionFind::new`]: 頂点数 $n$ の、すべて孤立した状態を構築する
//! - [`UnionFind::union`]: 頂点 $x, y$ を含む集合を併合する。既に同じ集合なら `false`
//! - [`UnionFind::same`]: 頂点 $x, y$ が同じ集合に属するか判定する
//! - [`UnionFind::find`] / [`find_mut`](UnionFind::find_mut): 頂点 $x$ が属する集合の代表元を返す
//! - 頂点重み: [`Op`] を実装した型 `O` を指定すると、`UnionFind<O>` は
//!   各集合に重み（[`Op::Value`]）を持てる。既製品として
//!   [`EdgeCount`], [`VertexCount`], [`HasCycle`] を用意している。
//!   複数の重みを同時に持たせたいときはタプル `(T, U, ..)` を使う
//!
//! # 例
//! 頂点重みなし（デフォルトは `()`）
//! ```
//! # use union_find::UnionFind;
//! // 型引数 `()` の defaulting のため `<_>` が必要
//! let mut uf = <UnionFind>::new(3);
//! assert_eq!(uf.same(0, 1), false);
//! assert_eq!(uf.union(0, 1), true);
//! assert_eq!(uf.same(0, 1), true);
//! assert_eq!(uf.same(0, 2), false);
//! assert_eq!(uf.union(0, 1), false); // 既に同じ集合
//! ```
//!
//! 頂点重みあり（辺数・サイクル判定）
//! ```
//! # use union_find::{EdgeCount, HasCycle, UnionFind};
//! let mut uf = UnionFind::<(EdgeCount, HasCycle)>::new(3);
//! assert_eq!(uf.value(0), (0, false));
//!
//! assert_eq!(uf.union(0, 1), true);
//! assert_eq!(uf.value(0), (1, false)); // 辺 1 本、サイクルなし
//!
//! assert_eq!(uf.union(0, 1), false); // 既に同じ集合 → 辺を 1 本追加
//! assert_eq!(uf.value(0), (2, true)); // 辺 2 本、サイクルあり
//! ```
//!
//! # 計算量
//! - [`new`](UnionFind::new) / [`from_values`](UnionFind::from_values): $O(n)$
//! - [`find`](UnionFind::find) / [`find_mut`](UnionFind::find_mut) / [`same`](UnionFind::same) / [`union`](UnionFind::union): 償却 $O(\alpha(n))$
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::Result;
use std::iter::repeat_with;
use std::marker::PhantomData;
use std::mem::replace;
use std::mem::swap;
use std::mem::take;

/// 頂点重みを自作したいときに使うトレイトです。
pub trait Op {
    /// 頂点重み型
    type Value: Default;
    /// [`UnionFind::new()`] で構築したときのデフォルト値
    fn singleton() -> Self::Value;
    /// 連結成分に辺を１本追加したとき
    fn add_edge(x: &mut Self::Value);
    /// 連結成分同士を新しい辺１本でつないだとき
    fn graft(parent: &mut Self::Value, child: Self::Value);
}
impl Op for () {
    type Value = ();

    fn singleton() -> Self::Value {}

    fn add_edge(_x: &mut Self::Value) {}

    fn graft(_parent: &mut Self::Value, _child: Self::Value) {}
}
impl<T: Op, U: Op> Op for (T, U) {
    type Value = (T::Value, U::Value);

    fn singleton() -> Self::Value {
        (T::singleton(), U::singleton())
    }

    fn add_edge(x: &mut Self::Value) {
        T::add_edge(&mut x.0);
        U::add_edge(&mut x.1);
    }

    fn graft(parent: &mut Self::Value, child: Self::Value) {
        T::graft(&mut parent.0, child.0);
        U::graft(&mut parent.1, child.1);
    }
}
impl<T: Op, U: Op, V: Op> Op for (T, U, V) {
    type Value = (T::Value, U::Value, V::Value);

    fn singleton() -> Self::Value {
        (T::singleton(), U::singleton(), V::singleton())
    }

    fn add_edge(x: &mut Self::Value) {
        T::add_edge(&mut x.0);
        U::add_edge(&mut x.1);
        V::add_edge(&mut x.2);
    }

    fn graft(parent: &mut Self::Value, child: Self::Value) {
        T::graft(&mut parent.0, child.0);
        U::graft(&mut parent.1, child.1);
        V::graft(&mut parent.2, child.2);
    }
}
/// 辺の本数
pub enum EdgeCount {}
impl Op for EdgeCount {
    type Value = usize;

    fn singleton() -> Self::Value {
        0
    }

    fn add_edge(x: &mut Self::Value) {
        *x += 1;
    }

    fn graft(parent: &mut Self::Value, child: Self::Value) {
        *parent += child + 1;
    }
}
/// 頂点の個数
pub enum VertexCount {}
impl Op for VertexCount {
    type Value = usize;

    fn singleton() -> Self::Value {
        1
    }

    fn add_edge(_x: &mut Self::Value) {}

    fn graft(parent: &mut Self::Value, child: Self::Value) {
        *parent += child;
    }
}
/// サイクルがあるとき、`true`
pub enum HasCycle {}
impl Op for HasCycle {
    type Value = bool;

    fn singleton() -> Self::Value {
        false
    }

    fn add_edge(x: &mut Self::Value) {
        *x = true;
    }

    fn graft(parent: &mut Self::Value, child: Self::Value) {
        *parent |= child;
    }
}

#[derive(Clone, Default, Hash, PartialEq)]
#[doc(alias = "DSU")]
pub struct UnionFind<O: Op = ()> {
    parent_or_size: Vec<isize>,
    values: Vec<O::Value>,
    __marker: PhantomData<fn(O) -> O>,
}
impl<O: Op> UnionFind<O> {
    pub fn new(n: usize) -> Self {
        Self::from_values(repeat_with(|| O::singleton()).take(n).collect())
    }

    pub fn from_values(values: Vec<O::Value>) -> Self {
        let n = values.len();
        assert!(n <= usize::MAX / 2);
        Self {
            parent_or_size: vec![-1; n],
            values,
            __marker: PhantomData,
        }
    }

    pub fn find_mut(&mut self, mut x: usize) -> usize {
        assert!(x < self.parent_or_size.len());
        let mut p = self.parent_or_size[x];
        while 0 <= p {
            if 0 <= self.parent_or_size[p as usize] {
                self.parent_or_size[x] = self.parent_or_size[p as usize];
            }
            x = p as usize;
            p = self.parent_or_size[x];
        }
        x
    }

    pub fn find(&self, mut x: usize) -> usize {
        assert!(x < self.parent_or_size.len());
        let mut p = self.parent_or_size[x];
        while 0 <= p {
            x = p as usize;
            p = self.parent_or_size[x];
        }
        x
    }

    pub fn same(&self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    pub fn is_root(&self, x: usize) -> bool {
        x == self.find(x)
    }

    pub fn get_value(&self, x: usize) -> &O::Value {
        assert!(x < self.parent_or_size.len());
        &self.values[self.find(x)]
    }

    pub fn value_mut(&mut self, x: usize) -> &mut O::Value {
        assert!(x < self.parent_or_size.len());
        let x = self.find_mut(x);
        &mut self.values[x]
    }

    pub fn value(&self, x: usize) -> O::Value
    where
        O::Value: Copy,
    {
        assert!(x < self.parent_or_size.len());
        self.values[self.find(x)]
    }

    pub fn union(&mut self, mut x: usize, mut y: usize) -> bool {
        assert!(x < self.parent_or_size.len());
        assert!(y < self.parent_or_size.len());
        x = self.find_mut(x);
        y = self.find_mut(y);
        if x == y {
            O::add_edge(&mut self.values[x]);
            false
        } else {
            if self.parent_or_size[x] < self.parent_or_size[y] {
                swap(&mut x, &mut y);
            }
            let aug = take(&mut self.values[x]);
            O::graft(&mut self.values[y], aug);
            self.parent_or_size[y] += replace(&mut self.parent_or_size[x], y as isize);
            true
        }
    }
}

impl<O: Op> Debug for UnionFind<O>
where
    O::Value: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let n = self.parent_or_size.len();
        let mut groups = vec![Vec::new(); n];
        for i in 0..n {
            groups[self.find(i)].push(i);
        }
        f.debug_list()
            .entries(
                groups
                    .into_iter()
                    .enumerate()
                    .filter(|(_, group)| !group.is_empty())
                    .map(|(root, list)| (&self.values[root], list)),
            )
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::EdgeCount;
    use super::HasCycle;
    use super::Op;
    use super::UnionFind;
    use super::VertexCount;
    use itertools::Itertools;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use randtools::DistinctTwo;
    use std::marker::PhantomData;
    use std::mem::take;

    #[test]
    fn test_union_find_smoke() {
        enum O {}
        impl Op for O {
            type Value = PhantomData<()>;

            fn singleton() -> Self::Value {
                PhantomData
            }

            fn add_edge(_x: &mut Self::Value) {}

            fn graft(_parent: &mut Self::Value, _child: Self::Value) {}
        }
        let _: UnionFind<()> = <UnionFind>::new(3); // requires `<_>`. cf: https://www.reddit.com/r/rust/comments/ek6w5g/default_generic_type_inference/
        let _: UnionFind<()> = UnionFind::<()>::new(3);
        <UnionFind>::new(3).value(0);
        let _: usize = UnionFind::<EdgeCount>::new(3).value(0);
        let _: (usize, usize) = UnionFind::<(EdgeCount, VertexCount)>::new(3).value(0);
        let _: (bool, bool, bool) = UnionFind::<(HasCycle, HasCycle, HasCycle)>::new(3).value(0);
        let _: PhantomData<()> = UnionFind::<O>::new(3).value(0);
    }

    #[test]
    fn test_union_find() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = 3;
            let mut parent = (0..n).collect_vec();
            let mut edge_count = vec![0; n];
            let mut vertex_count = vec![1; n];
            let mut has_cycle = vec![false; n];
            let mut uf = UnionFind::<(EdgeCount, VertexCount, HasCycle)>::new(n);
            for _ in 0..80 {
                match rng.gen_range(0..5) {
                    // union
                    0 => {
                        let (u, v) = rng.sample(DistinctTwo(0..n));
                        uf.union(u, v);
                        let u = parent[u];
                        let v = parent[v];
                        for p in &mut parent {
                            if *p == v {
                                *p = u;
                            }
                        }
                        if u == v {
                            edge_count[u] += 1;
                            has_cycle[u] = true;
                        } else {
                            edge_count[u] += take(&mut edge_count[v]) + 1;
                            vertex_count[u] += take(&mut vertex_count[v]);
                            has_cycle[u] |= has_cycle[v];
                        }
                    }
                    // same
                    1 => {
                        let (u, v) = rng.sample(DistinctTwo(0..n));
                        let result = uf.same(u, v);
                        let expected = parent[u] == parent[v];
                        assert_eq!(result, expected);
                    }
                    // edge_count
                    2 => {
                        let u = rng.gen_range(0..n);
                        let result = uf.value(u).0;
                        let expected = edge_count[parent[u]];
                        assert_eq!(result, expected);
                    }
                    // vertex_count
                    3 => {
                        let u = rng.gen_range(0..n);
                        let result = uf.value(u).1;
                        let expected = vertex_count[parent[u]];
                        assert_eq!(result, expected);
                    }
                    // has_cycle
                    4 => {
                        let u = rng.gen_range(0..n);
                        let result = uf.value(u).2;
                        let expected = has_cycle[parent[u]];
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
