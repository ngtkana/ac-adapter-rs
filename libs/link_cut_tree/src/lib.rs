//! 森（複数の根付き木の集まり）を管理し、パスの集約値を対数時間で更新・取得する Link-Cut Tree
//!
//! 各根付き木を「優先パス」に分解し、パスごとに 1 本の splay 木（節点が根に近い順に並ぶ二分探索木）を構築する。
//! パス同士は「パス親」ポインタでつなぎ、根から任意の節点までを `expose` 操作で 1 本の優先パスへ再編する。
//! この再編は splay 木の償却解析により償却 $O(\log n)$ で行え、結果として `link`・`cut`・`evert`（根の付け替え）・
//! パスの集約取得などの操作がすべて償却 $O(\log n)$ で実現する。
//!
//! # 仕様
//!
//! - [`LinkCutTree`] は集約値を持たない森
//! - [`CommutLinkCutTree<T>`](CommutLinkCutTree) は可換なモノイド `T`（[`Op`] トレイトで定義）を載せた森
//! - [`NonCommutLinkCutTree<T>`](NonCommutLinkCutTree) は非可換なモノイド `T` を載せた森
//!
//! いずれも実体は [`LinkCutTreeBase`]。根を付け替えるには [`evert`](LinkCutTreeBase::evert) を呼ぶ。
//! 有向の根付き森として扱う操作（`link`, `cut`, `parent`, `lca` など）に加え、根を意識しない
//! 無向グラフとしての操作（`undirected_link`, `undirected_cut`, `undirected_is_connected`,
//! `undirected_fold` など）も提供する。
//!
//! # 例
//!
//! ```
//! use link_cut_tree::LinkCutTree;
//!
//! let mut lct = LinkCutTree::new(3);
//! lct.link(0, 1); // 0 -> 1
//! lct.link(1, 2); // 1 -> 2
//! assert_eq!(lct.parent(2), Some(1));
//! assert_eq!(lct.lca(0, 2), Some(0));
//!
//! lct.cut(2);
//! assert_eq!(lct.parent(2), None);
//! ```
//!
//! # 計算量
//!
//! すべての操作: 償却 $O(\log n)$（$n$ は節点数）

mod base;

pub use base::LinkCutTreeBase;
use base::OpBase;

/// 集約演算を定義するトレイト
///
/// モノイド $(Value, \cdot, e)$ を定める。`mul` は結合律を満たす必要がある。可換性は要求しないが、
/// 可換なら [`CommutLinkCutTree`]、非可換なら [`NonCommutLinkCutTree`] を使う。
pub trait Op {
    type Value: Clone;
    fn identity() -> Self::Value;
    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

impl OpBase for () {
    type InternalValue = ();
    type Value = ();

    fn identity() -> Self::InternalValue {}

    fn mul(_lhs: &Self::InternalValue, _rhs: &Self::InternalValue) -> Self::InternalValue {}

    fn rev(_value: &mut Self::InternalValue) {}

    fn into_front(_value: Self::InternalValue) {}

    fn from_front(_value: Self::Value) -> Self::InternalValue {}
}
/// 集約値を持たない Link-Cut Tree
///
/// 連結性・親子関係・LCA など、木構造そのものの操作のみを提供する。
pub type LinkCutTree = LinkCutTreeBase<()>;

/// 可換なモノイドを載せた Link-Cut Tree
///
/// パスの集約値が根からの向きに依存しない（$x \cdot y = y \cdot x$）ことを前提とする。
pub type CommutLinkCutTree<T> = LinkCutTreeBase<Commut<T>>;
#[doc(hidden)]
pub struct Commut<T: Op>(T);

impl<T: Op> OpBase for Commut<T> {
    type InternalValue = T::Value;
    type Value = T::Value;

    fn identity() -> Self::InternalValue {
        T::identity()
    }

    fn mul(lhs: &Self::InternalValue, rhs: &Self::InternalValue) -> Self::InternalValue {
        T::mul(lhs, rhs)
    }

    fn rev(_value: &mut Self::InternalValue) {}

    fn into_front(value: Self::InternalValue) -> Self::Value {
        value
    }

    fn from_front(value: Self::Value) -> Self::InternalValue {
        value
    }
}

#[doc(hidden)]
pub struct NonCommut<T: Op>(T);
/// 非可換なモノイドを載せた Link-Cut Tree
///
/// 各節点で正順・逆順両方の積を保持し、根の付け替え（[`evert`](LinkCutTreeBase::evert)）に
/// よる向きの反転を $O(1)$ で追従させる。
pub type NonCommutLinkCutTree<T> = LinkCutTreeBase<NonCommut<T>>;

impl<T: Op> OpBase for NonCommut<T> {
    type InternalValue = (T::Value, T::Value);
    type Value = T::Value;

    fn identity() -> Self::InternalValue {
        (T::identity(), T::identity())
    }

    fn mul(lhs: &Self::InternalValue, rhs: &Self::InternalValue) -> Self::InternalValue {
        (T::mul(&lhs.0, &rhs.0), T::mul(&rhs.1, &lhs.1))
    }

    fn rev(value: &mut Self::InternalValue) {
        std::mem::swap(&mut value.0, &mut value.1);
    }

    fn into_front(value: Self::InternalValue) -> Self::Value {
        value.0
    }

    fn from_front(value: Self::Value) -> Self::InternalValue {
        (value.clone(), value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    struct NaiveLinkCutTree {
        parent: Vec<Option<usize>>,
        children: Vec<Vec<usize>>,
    }
    impl NaiveLinkCutTree {
        fn new(n: usize) -> Self {
            Self {
                parent: vec![None; n],
                children: vec![vec![]; n],
            }
        }

        fn root(&self, mut x: usize) -> usize {
            while let Some(p) = self.parent[x] {
                x = p;
            }
            x
        }

        fn ancestors(&self, mut x: usize) -> Vec<usize> {
            let mut res = vec![x];
            while let Some(p) = self.parent[x] {
                res.push(p);
                x = p;
            }
            res
        }

        fn is_linkable(&self, p: usize, c: usize) -> bool {
            self.parent[c].is_none() && self.root(p) != c
        }

        fn link(&mut self, p: usize, c: usize) {
            assert_eq!(self.parent[c], None);
            self.parent[c] = Some(p);
            self.children[p].push(c);
        }

        fn cut(&mut self, x: usize) -> Option<usize> {
            let p = self.parent[x]?;
            self.parent[x] = None;
            self.children[p].retain(|&c| c != x);
            Some(p)
        }

        fn evert(&mut self, mut x: usize) {
            let mut prev = None;
            while let Some(p) = std::mem::replace(&mut self.parent[x], prev) {
                self.children[p].retain(|&c| c != x);
                self.children[x].push(p);
                prev = Some(x);
                x = p;
            }
        }

        fn lca(&self, x: usize, y: usize) -> Option<usize> {
            self.ancestors(x)
                .iter()
                .rev()
                .zip(self.ancestors(y).iter().rev())
                .take_while(|&(a, b)| a == b)
                .last()
                .map(|(a, _)| *a)
        }

        fn parent(&self, x: usize) -> Option<usize> {
            self.parent[x]
        }
    }

    struct NaiveDynamicConnectivity {
        graph: Vec<Vec<usize>>,
    }
    impl NaiveDynamicConnectivity {
        fn new(n: usize) -> Self {
            Self {
                graph: vec![vec![]; n],
            }
        }

        fn link(&mut self, p: usize, c: usize) -> bool {
            if self.is_connected(p, c) {
                return false;
            }
            self.graph[p].push(c);
            self.graph[c].push(p);
            true
        }

        fn cut(&mut self, p: usize, c: usize) -> bool {
            if self.graph[p].iter().all(|&x| x != c) {
                return false;
            }
            self.graph[p].retain(|&x| x != c);
            self.graph[c].retain(|&x| x != p);
            true
        }

        fn is_connected(&self, x: usize, y: usize) -> bool {
            let mut visited = vec![false; self.graph.len()];
            let mut stack = vec![x];
            while let Some(v) = stack.pop() {
                if v == y {
                    return true;
                }
                if visited[v] {
                    continue;
                }
                visited[v] = true;
                stack.extend(self.graph[v].iter().copied());
            }
            false
        }

        fn path(&self, x: usize, y: usize) -> Option<Vec<usize>> {
            let mut parent = vec![None; self.graph.len()];
            parent[x] = Some(x);
            let mut stack = vec![x];
            while let Some(v) = stack.pop() {
                if v == y {
                    break;
                }
                for &u in &self.graph[v] {
                    if parent[u].is_none() {
                        parent[u] = Some(v);
                        stack.push(u);
                    }
                }
            }
            parent[y]?;
            let mut path = vec![];
            let mut v = y;
            loop {
                path.push(v);
                if v == x {
                    break;
                }
                v = parent[v].unwrap();
            }
            path.reverse();
            Some(path)
        }
    }

    #[test]
    fn test_link_cut_tree() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=60);
            let q = rng.gen_range(n..2 * n);
            let mut lct = LinkCutTree::new(n);
            let mut naive = NaiveLinkCutTree::new(n);
            for _ in 0..q {
                match rng.gen_range(0..5) {
                    // link
                    0 => {
                        if naive.parent.iter().filter(|&&p| p.is_some()).count() == n - 1 {
                            continue;
                        }
                        let (p, c) = loop {
                            let p = rng.gen_range(0..n);
                            let c = rng.gen_range(0..n);
                            if naive.is_linkable(p, c) {
                                break (p, c);
                            }
                        };
                        lct.link(p, c);
                        naive.link(p, c);
                    }
                    // cut
                    1 => {
                        let x = rng.gen_range(0..n);
                        let ans = lct.cut(x);
                        let expected = naive.cut(x);
                        assert_eq!(ans, expected);
                    }
                    // evert
                    2 => {
                        let x = rng.gen_range(0..n);
                        lct.evert(x);
                        naive.evert(x);
                    }
                    // lca
                    3 => {
                        let x = rng.gen_range(0..n);
                        let y = rng.gen_range(0..n);
                        let ans = lct.lca(x, y);
                        let expected = naive.lca(x, y);
                        assert_eq!(ans, expected);
                    }
                    // parent
                    4 => {
                        let x = rng.gen_range(0..n);
                        let ans = lct.parent(x);
                        let expected = naive.parent(x);
                        assert_eq!(ans, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_dynamic_connectivity() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=60);
            let q = rng.gen_range(n..2 * n);
            let mut lct = LinkCutTree::new(n);
            let mut naive = NaiveDynamicConnectivity::new(n);
            for _ in 0..q {
                match rng.gen_range(0..3) {
                    // link
                    0 => {
                        let i = rng.gen_range(0..n);
                        let j = rng.gen_range(0..n);
                        let result = lct.undirected_link(i, j);
                        let expected = naive.link(i, j);
                        assert_eq!(result, expected);
                    }
                    // cut
                    1 => {
                        let x = rng.gen_range(0..n);
                        let y = rng.gen_range(0..n);
                        let result = lct.undirected_cut(x, y);
                        let expected = naive.cut(x, y);
                        assert_eq!(result, expected);
                    }
                    // is_connected
                    2 => {
                        let x = rng.gen_range(0..n);
                        let y = rng.gen_range(0..n);
                        let ans = lct.undirected_is_connected(x, y);
                        let expected = naive.is_connected(x, y);
                        assert_eq!(ans, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_link_cut_tree_xor() {
        enum O {}
        impl Op for O {
            type Value = u32;

            fn identity() -> Self::Value {
                0
            }

            fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                lhs ^ rhs
            }
        }
        const LIM: u32 = 1 << 20;

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=60);
            let q = rng.gen_range(n..2 * n);
            let mut values = (0..n).map(|_| rng.gen_range(0..LIM)).collect::<Vec<_>>();
            let mut lct = CommutLinkCutTree::<O>::from_values(values.iter().copied());
            let mut naive = NaiveDynamicConnectivity::new(n);
            for _ in 0..q {
                match rng.gen_range(0..4) {
                    // link
                    0 => {
                        let i = rng.gen_range(0..n);
                        let j = rng.gen_range(0..n);
                        let result = lct.undirected_link(i, j);
                        let expected = naive.link(i, j);
                        assert_eq!(result, expected);
                    }
                    // cut
                    1 => {
                        let i = rng.gen_range(0..n);
                        let j = rng.gen_range(0..n);
                        let result = lct.undirected_cut(i, j);
                        let expected = naive.cut(i, j);
                        assert_eq!(result, expected);
                    }
                    // set
                    2 => {
                        let i = rng.gen_range(0..n);
                        let value = rng.gen_range(0..LIM);
                        lct.set(i, |old| old ^ value);
                        values[i] ^= value;
                    }
                    // fold
                    3 => {
                        let i = rng.gen_range(0..n);
                        let j = rng.gen_range(0..n);
                        let ans = lct.undirected_fold(i, j);
                        let path = naive.path(i, j);
                        let expected = path.map(|path| {
                            path.iter()
                                .map(|&i| values[i])
                                .fold(0, std::ops::BitXor::bitxor)
                        });
                        assert_eq!(ans, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_link_cut_tree_rolling_hash() {
        const P: u64 = 998_244_353;
        const BASE: u64 = 100;
        #[derive(Clone, Copy, Debug, PartialEq)]
        struct RollingHash {
            base: u64,
            value: u64,
        }
        enum O {}
        impl Op for O {
            type Value = RollingHash;

            fn identity() -> Self::Value {
                RollingHash { base: 1, value: 0 }
            }

            fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                RollingHash {
                    base: lhs.base * rhs.base % P,
                    value: (lhs.value * rhs.base + rhs.value) % P,
                }
            }
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=60);
            let q = rng.gen_range(n..2 * n);
            let mut values = (0..n)
                .map(|_| RollingHash {
                    base: BASE,
                    value: rng.gen_range(0..P),
                })
                .collect::<Vec<_>>();
            let mut lct = NonCommutLinkCutTree::<O>::from_values(values.iter().copied());
            let mut naive = NaiveDynamicConnectivity::new(n);
            for _ in 0..q {
                match rng.gen_range(0..4) {
                    // link
                    0 => {
                        let i = rng.gen_range(0..n);
                        let j = rng.gen_range(0..n);
                        let result = lct.undirected_link(i, j);
                        let expected = naive.link(i, j);
                        assert_eq!(result, expected);
                    }
                    // cut
                    1 => {
                        let i = rng.gen_range(0..n);
                        let j = rng.gen_range(0..n);
                        let result = lct.undirected_cut(i, j);
                        let expected = naive.cut(i, j);
                        assert_eq!(result, expected);
                    }
                    // set
                    2 => {
                        let i = rng.gen_range(0..n);
                        let value = rng.gen_range(0..BASE);
                        lct.set(i, |_| RollingHash { base: BASE, value });
                        values[i].value = value;
                    }
                    // fold
                    3 => {
                        let i = rng.gen_range(0..n);
                        let j = rng.gen_range(0..n);
                        let ans = lct.undirected_fold(i, j);
                        let path = naive.path(i, j);
                        let expected = path.map(|path| {
                            path.iter()
                                .map(|&i| values[i])
                                .fold(O::identity(), |lhs, rhs| O::mul(&lhs, &rhs))
                        });
                        assert_eq!(ans, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
