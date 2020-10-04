//! 双対セグメントツリーです。
//!
//!
//! # 抽象データ構造としての双対セグメントツリー
//!
//! 半群の要素の列 `a` を管理します。できる操作はこちらです。
//!
//! - `build(a)`:
//!     - 列 `a` に対応する双対セグメントツリーを構築します。
//!     - 時間計算量 O ( N )
//!
//! - `apply_range(l, r, x)`
//!     - `l` 以上 `r` 未満のすべての項に、（左から）`x` をかけます。
//!     - 時間計算量 O ( lg ( r - l ) )
//!
//! - `get(i)`
//!     - `i` 番目の要素を取得します。
//!     - 時間計算量 O ( lg N )
//!
//!
//! # 双対セグメントツリーと作用
//!
//! 半群 A が集合 X に作用するとして、集合 X の要素の列 a を管理します。できる操作はこちらです。
//!
//! - `build(a)`:
//!     - （空間側が）列 `a` に対応するデータ構造を構築です。
//!     - 時間計算量 O ( N )
//!
//! - `apply_range(l, r, x)`
//!     - `l` 以上 `r` 未満のすべての項に、作用素半群 A の要素 `x` を作用します。
//!     - 時間計算量 O ( lg ( r - l ) )
//!
//! - `get(i)`
//!     - `a` の `i` 番目の要素を取得します。
//!     - 時間計算量 O ( lg N )
//!
//!
use std::{
    iter,
    ops::{self, Range, RangeBounds},
};
use type_traits::{Action, Identity};

/// 双対セグメントツリーを使って作用を管理します。
#[derive(Debug, Clone, PartialEq)]
pub struct DualSegtreeWith<T: Action> {
    dual: DualSegtree<T>,
    table: Vec<T::Space>,
}
impl<T: Action + Identity> DualSegtreeWith<T> {
    /// `build(a)` をします。
    pub fn from_slice(table: &[T::Space]) -> Self {
        DualSegtreeWith {
            // TODO: FromIterator を使います。
            dual: DualSegtree::from_slice(
                iter::repeat_with(T::identity)
                    .take(table.len())
                    .collect::<Vec<_>>()
                    .as_slice(),
            ),
            table: table.to_vec(),
        }
    }
    pub fn apply(&mut self, range: impl RangeBounds<usize>, x: T) {
        self.dual.apply(range, x);
    }
    pub fn get(&mut self, i: usize) -> &T::Space {
        let x = self.dual.take(i);
        if x != T::identity() {
            x.act_mut(&mut self.table[i]);
        }
        &self.table[i]
    }
}

/// 双対セグメントツリーを実現します。
#[derive(Debug, Clone, PartialEq)]
pub struct DualSegtree<T> {
    len: usize,
    lg: u32,
    table: Vec<T>,
}
impl<T: Identity> DualSegtree<T> {
    /// `build(a)` をします。
    pub fn from_slice(src: &[T]) -> Self {
        Self {
            len: src.len(),
            lg: src.len().next_power_of_two().trailing_zeros(),
            table: std::iter::repeat_with(T::identity)
                .take(src.len())
                .chain(src.to_vec())
                .collect::<Vec<_>>(),
        }
    }
    /// `apply_range(start, end, x)` をします。
    pub fn apply(&mut self, range: impl RangeBounds<usize>, x: T) {
        let Range { mut start, mut end } = open(self.len, range);
        if start < end {
            start += self.len;
            end += self.len;
            self.thrust(start);
            self.thrust(end - 1);
            while start != end {
                if start % 2 == 1 {
                    self.table[start].op_from_left(&x);
                    start += 1;
                }
                if end % 2 == 1 {
                    end -= 1;
                    self.table[end].op_from_left(&x);
                }
                start >>= 1;
                end >>= 1;
            }
        }
    }
    /// `get(i)` をします。
    pub fn get(&mut self, mut i: usize) -> &T {
        i += self.len;
        self.thrust(i);
        &self.table[i]
    }
    /// `i` 番目を `1` にして、もともとの値を返します。
    pub fn take(&mut self, mut i: usize) -> T {
        i += self.len;
        self.thrust(i);
        std::mem::replace(&mut self.table[i], T::identity())
    }
    fn thrust(&mut self, i: usize) {
        let lg = self.lg;
        (1..=lg)
            .rev()
            .map(|p| i >> p)
            .for_each(|j| self.propagate(j));
    }
    fn propagate(&mut self, i: usize) {
        if self.table[i] != T::identity() {
            let x = std::mem::replace(&mut self.table[i], T::identity());
            self.table[2 * i].op_from_left(&x);
            self.table[2 * i + 1].op_from_left(&x);
        }
    }
}
fn open(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    use ops::Bound::*;
    (match range.start_bound() {
        Unbounded => 0,
        Included(&x) => x,
        Excluded(&x) => x + 1,
    })..(match range.end_bound() {
        Excluded(&x) => x,
        Included(&x) => x + 1,
        Unbounded => len,
    })
}

#[cfg(test)]
mod tests {
    mod impl_query;
    use query_test_2::{gen, query, CONFIG};
    use rand::prelude::*;
    use test_vector::Vector;
    use type_traits::Action;

    type Fp = fp::F998244353;
    type TesterDualSegtree<T, G> =
        query_test_2::Tester<StdRng, Vector<T>, crate::DualSegtree<T>, G>;
    type TesterDualSegtreeWith<T, G> =
        query_test_2::Tester<StdRng, Vector<<T as Action>::Space>, crate::DualSegtreeWith<T>, G>;

    #[test]
    fn test_add_fp() {
        use type_traits::{actions::Adj, binary::Add, Constant};
        type Node = Add<Fp>;
        type Action = Adj<Node>;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 100)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(_rng: &mut R) -> Node {
                Add(Fp::new(0))
            }
        }
        impl gen::GenAction<Action> for G {
            fn gen_action<R: Rng>(rng: &mut R) -> Action {
                Adj(Add(Fp::new(rng.gen_range(0, fp::Mod998244353::VALUE))))
            }
        }

        let mut tester = TesterDualSegtree::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 2);
                match command {
                    0 => tester.compare_mut::<query::Get<_>>(),
                    1 => tester.mutate::<query::RangeApply<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_update_u32() {
        use type_traits::actions::Update;
        type Node = u32;
        type Action = Option<Update<u32>>;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 20)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(_rng: &mut R) -> Node {
                0
            }
        }
        impl gen::GenAction<Action> for G {
            fn gen_action<R: Rng>(rng: &mut R) -> Action {
                Some(Update(rng.gen_range(0, 100)))
            }
        }

        let mut tester = TesterDualSegtreeWith::<Action, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 2);
                match command {
                    0 => tester.compare_mut::<query::Get<_>>(),
                    1 => tester.mutate::<query::RangeApply<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_pow_fp() {
        use type_traits::{actions::Pow, binary::Mul};
        type Node = Mul<Fp>;
        type Action = Pow<Mul<Fp>>;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 20)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Node {
                Mul(Fp::new(rng.gen_range(2, 5)))
            }
        }
        impl gen::GenAction<Action> for G {
            fn gen_action<R: Rng>(rng: &mut R) -> Action {
                Pow::new(rng.gen_range(1, 3))
            }
        }

        let mut tester = TesterDualSegtreeWith::<Action, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 2);
                match command {
                    0 => tester.compare_mut::<query::Get<_>>(),
                    1 => tester.mutate::<query::RangeApply<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
