//! Dinic 法で最大流を求めます。
//!
//! # Flow Type
//!
//! 符号なし整数型のみです。
//! 浮動小数点数は、[`Ord`] トレイトを実装していないので厳しそうです。
//!
//! [`Ord`]: https://doc.rust-lang.org/stable/std/cmp/trait.Ord.html

use std::fmt::Debug;
use std::fmt::Display;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Sub;
use std::ops::SubAssign;

////////////////////////////////////////////////////////////////////////////////
// FlowTrait
////////////////////////////////////////////////////////////////////////////////

/// 流量型になれるものです。
///
/// 具体的には、符号なし整数型です。
pub trait FlowTrait:
    Debug
    + Display
    + Clone
    + Copy
    + PartialOrd
    + Ord
    + Eq
    + PartialEq
    + Add
    + AddAssign
    + Sub
    + SubAssign
{
    /// `0` を返します。
    fn zero() -> Self;

    /// `std::$ty::MAX` を返します。
    fn infinity() -> Self;
}

macro_rules! flow_value_impl_integer {
    ($($ty: ident,)*) => {
        $(impl FlowTrait for $ty {
            #[inline]
            fn zero() -> Self {
                0
            }
            #[inline]
            fn infinity() -> Self {
                std::$ty::MAX
            }
        })*
    };
}

flow_value_impl_integer! {
    usize, u8, u16, u32, u64, u128,
}

////////////////////////////////////////////////////////////////////////////////
// FlowEdge, MaxFlow
////////////////////////////////////////////////////////////////////////////////
#[derive(Debug, Clone)]
struct FlowEdge<Value: FlowTrait> {
    to: usize,
    cap: Value,
    rev: usize,
}

#[derive(Debug, Clone)]
struct DoubleEdge {
    from: usize,
    from_idx: usize,
    to: usize,
    to_idx: usize,
}

/// Dinic 法で最大流を求めます。
pub struct MaxFlow<Value: FlowTrait> {
    /// 最大流のアルゴリズムを適用済みかどうかです。
    source: usize,
    sink: usize,
    network: Vec<Vec<FlowEdge<Value>>>,
}

impl<Value: FlowTrait> MaxFlow<Value> {
    fn len(&self) -> usize {
        self.network.len()
    }

    /// 構築です。
    ///
    /// # Examples
    ///
    /// ```
    /// use max_flow::MaxFlow;
    /// let network = MaxFlow::<u8>::with_size_source_sink(5, 0, 4);
    /// ```
    pub fn with_size_source_sink(n: usize, source: usize, sink: usize) -> Self {
        Self {
            source,
            sink,
            network: vec![vec![]; n],
        }
    }

    /// 辺を挿入です。
    ///
    /// 内部的には、アルゴリズム上必要なので容量 `0` の逆辺も挿入します。
    ///
    /// # Examples
    ///
    /// ```
    /// use max_flow::MaxFlow;
    /// let mut network = MaxFlow::<u8>::with_size_source_sink(5, 0, 4);
    /// network.insert(1, 3, 4);
    /// ```
    pub fn insert(&mut self, u: usize, v: usize, cap: Value) {
        let su = self.network[u].len();
        let sv = self.network[v].len();
        self.network[u].push(FlowEdge {
            to: v,
            cap,
            rev: sv,
        });
        self.network[v].push(FlowEdge {
            to: u,
            cap: Value::zero(),
            rev: su,
        });
    }

    /// [`insert`] をたくさん呼びます。
    ///
    /// # Examples
    ///
    /// ```
    /// use max_flow::MaxFlow;
    /// let n = 6;
    /// let s = 0;
    /// let t = 5;
    /// let mut network = MaxFlow::<u8>::with_size_source_sink(n, s, t);
    /// network.insert_from_slice(&[
    ///     (s, 1, 10),
    ///     (s, 2, 10),
    ///     (1, 2, 2),
    ///     (1, 3, 4),
    ///     (1, 4, 8),
    ///     (2, 4, 9),
    ///     (4, 3, 6),
    ///     (3, t, 10),
    ///     (4, t, 10),
    /// ]);
    /// assert_eq!(network.run(), 19);
    /// ```
    ///
    /// [`insert`]: struct.MaxFlow.html#insert
    pub fn insert_from_slice(&mut self, src: &[(usize, usize, Value)]) {
        src.iter().for_each(|&(u, v, cap)| self.insert(u, v, cap));
    }

    /// 実行します。
    ///
    /// 最大流量を返却します。
    ///
    /// # Examples
    ///
    /// ```
    /// use max_flow::MaxFlow;
    /// let mut network = MaxFlow::<u8>::with_size_source_sink(5, 0, 4);
    /// network.insert(0, 1, 4);
    /// network.insert(1, 2, 2);
    /// network.insert(2, 3, 3);
    /// network.insert(3, 4, 6);
    /// assert_eq!(network.run(), 2);
    /// ```
    pub fn run(&mut self) -> Value {
        let mut flow = Value::zero();
        loop {
            // 最短距離を計算です。
            let dist = self.construct_dist_array();
            if dist[self.sink] == std::usize::MAX {
                return flow;
            }

            // 増分路と流せる量を計算です。
            let mut path = Vec::new();
            let e = self.dfs(self.source, Value::infinity(), &dist, &mut path);
            assert_ne!(e, Value::zero());

            // 増分路をネットワークに反映させて、流せる量を答えに足します。
            for DoubleEdge {
                from,
                from_idx,
                to,
                to_idx,
            } in path
            {
                self.network[from][from_idx].cap -= e;
                self.network[to][to_idx].cap += e;
            }
            flow += e;
        }
    }

    fn dfs(&self, from: usize, d: Value, dist: &[usize], path: &mut Vec<DoubleEdge>) -> Value {
        if from == self.sink {
            return d;
        }
        for (from_idx, &FlowEdge { to, cap, rev }) in
            self.network[from]
                .iter()
                .enumerate()
                .filter(|&(_, &FlowEdge { to, cap, rev: _ })| {
                    cap != Value::zero() && dist[from] + 1 == dist[to]
                })
        {
            let e = self.dfs(to, d.min(cap), dist, path);
            if e == Value::zero() {
                continue;
            }
            path.push(DoubleEdge {
                from,
                from_idx,
                to,
                to_idx: rev,
            });
            return e;
        }
        Value::zero()
    }

    fn construct_dist_array(&self) -> Vec<usize> {
        let mut dist = vec![std::usize::MAX; self.len()];
        dist[self.source] = 0;
        let mut queue = std::collections::VecDeque::with_capacity(self.len());
        queue.push_back(self.source);
        while let Some(from) = queue.pop_front() {
            for &FlowEdge { to, cap: _, rev: _ } in
                self.network[from].iter().filter(|e| e.cap != Value::zero())
            {
                if dist[to] == std::usize::MAX {
                    dist[to] = dist[from] + 1;
                    queue.push_back(to);
                }
            }
        }
        dist
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_flow_dinic_wipikedia() {
        let n = 6;
        let s = 0;
        let t = 5;
        let mut network = MaxFlow::<u8>::with_size_source_sink(n, s, t);
        network.insert_from_slice(&[
            (s, 1, 10),
            (s, 2, 10),
            (1, 2, 2),
            (1, 3, 4),
            (1, 4, 8),
            (2, 4, 9),
            (4, 3, 6),
            (3, t, 10),
            (4, t, 10),
        ]);
        assert_eq!(network.run(), 19);
    }
}
