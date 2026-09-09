//! 動的確保によるモノイド載せ二分木（疎セグメント木）
//!
//! `segtree` クレートの完全二分木を、内部ノードの動的確保に置き換えた実装。
//! 定義域 $[0, n)$ をあらかじめ固定しておき、実際に触れた添字への経路上のノードだけを
//! `Box` で確保する。未確保の部分木は単位元 $e$ を持つとみなして畳み込みに参加させる。
//! 触れた添字の個数を $k$ とすると、空間計算量は $O(k \log n)$ に抑えられる。
//!
//! # 仕様
//!
//! [`Op`] トレイトでモノイド $(S, \cdot, e)$ を定義する。
//!
//! - [`Op::identity`][]: 単位元 $e$
//! - [`Op::op`][]: 積 $x \cdot y$（結合律を満たすこと）
//!
//! [`SparseSegtree::from_range`] で定義域 $[0, n)$ を指定して構築し、
//! [`SparseSegtree::apply`] で 1 点更新、[`SparseSegtree::fold`] で区間畳み込みを行う。
//!
//! # 例
//!
//! ```
//! use sparse_segtree::Op;
//! use sparse_segtree::SparseSegtree;
//!
//! enum Add {}
//! impl Op for Add {
//!     type Value = i64;
//!     fn identity() -> i64 {
//!         0
//!     }
//!     fn op(lhs: &i64, rhs: &i64) -> i64 {
//!         lhs + rhs
//!     }
//! }
//!
//! let mut seg = SparseSegtree::<Add>::from_range(0..10);
//! seg.apply(2, |x| *x += 5);
//! seg.apply(5, |x| *x += 3);
//! assert_eq!(seg.fold(0..10), 8);
//! ```
//!
//! # 計算量
//!
//! 定義域の大きさを $n$ とする。
//!
//! - 構築（[`SparseSegtree::from_range`]）: $O(1)$
//! - 1 点更新（[`SparseSegtree::apply`]）: $O(\log n)$（未確保ノードの新規確保を含む）
//! - 畳み込み（[`SparseSegtree::fold`]）: $O(\log n)$
//! - 走査（[`SparseSegtree::visit_items`], [`SparseSegtree::visit_ranges`]）: $O(\log n)$ に加え、実際に確保済みのノード数に比例
use std::ops::Range;
use std::ops::RangeBounds;

/// モノイド $(S, \cdot, e)$ の演算を定義するトレイト。
pub trait Op {
    /// 値の型 $S$。
    type Value;
    /// 単位元 $e$。
    fn identity() -> Self::Value;
    /// 積 $x \cdot y$。結合律を満たすこと。
    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

/// 動的確保によるセグメント木。定義域 $[0, n)$ を固定し、触れた添字への経路上のノードだけを確保する。
///
/// # 例
///
/// ```rust
/// use sparse_segtree::Op;
/// use sparse_segtree::SparseSegtree;
///
/// #[derive(Clone, Debug)]
/// enum SumOp {}
/// impl Op for SumOp {
///     type Value = i64;
///
///     fn identity() -> Self::Value {
///         0
///     }
///
///     fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
///         lhs + rhs
///     }
/// }
///
/// let mut seg = SparseSegtree::<SumOp>::from_range(0..10);
///
/// seg.apply(2, |x| *x += 5);
/// assert_eq!(seg.fold(0..10), 5);
///
/// seg.apply(5, |x| *x += 3);
/// assert_eq!(seg.fold(0..10), 8);
/// ```
pub struct SparseSegtree<O: Op> {
    root: Option<Box<Node<O>>>,
}
impl<O: Op> SparseSegtree<O> {
    /// 定義域 $[0, n)$（`range`）を指定してセグメント木を構築する。
    ///
    /// 全体を覆う 1 個のノードのみ確保する（子ノードは未確保）。$n = 0$ のときは何も確保しない。
    pub fn from_range(range: Range<usize>) -> Self {
        let root = (!range.is_empty()).then(|| Box::new(Node::new_leaf(range)));
        SparseSegtree { root }
    }

    /// $x_i \gets f(x_i)$ に更新する。経路上の未確保ノードは新たに確保する。
    ///
    /// # Panics
    ///
    /// 木が空、または $i$ が定義域外のとき panic する。
    pub fn apply(&mut self, i: usize, f: impl FnMut(&mut O::Value)) {
        let Some(root) = self.root.as_mut() else {
            panic!("Cannot update an empty segment tree");
        };
        assert!(
            (root.start..root.end).contains(&i),
            "Index out of bounds for segment tree"
        );
        root.update(i, f);
    }

    /// 総積 $x_l \cdot x_{l+1} \cdots x_{r-1}$ を返す。未確保の部分木は単位元 $e$ とみなす。
    pub fn fold(&self, range: impl RangeBounds<usize>) -> O::Value {
        let mut result = O::identity();
        self.visit_ranges(range, |_, value| {
            result = O::op(&result, value);
        });
        result
    }

    /// 確保済みの添字 $i \in [l, r)$ について、左から右へ $f(i, x_i)$ を呼ぶ。
    ///
    /// 一度も [`apply`](Self::apply) されていない添字はノードごと未確保のため呼ばれない。
    /// ただし確保済みでも値が単位元 $e$ のままのノードは呼ばれることがある
    /// （フィルタが必要なら呼び出し側で $x_i = e$ を判定する）。
    ///
    /// # Panics
    ///
    /// `range` が定義域外のとき panic する。
    ///
    /// # 例
    ///
    /// ```rust
    /// use sparse_segtree::Op;
    /// use sparse_segtree::SparseSegtree;
    /// /* define `enum SumOp` and implement `Op` trait */
    /// # #[derive(Clone, Debug)]
    /// # enum SumOp {}
    /// # impl Op for SumOp {
    /// #    type Value = i64;
    /// #    fn identity() -> Self::Value {
    /// #        0
    /// #    }
    /// #    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
    /// #        lhs + rhs
    /// #    }
    /// # }
    /// let mut seg = SparseSegtree::<SumOp>::from_range(0..10);
    /// seg.apply(2, |x| *x += 5);
    /// seg.apply(5, |x| *x += 3);
    /// assert_eq!(seg.fold(0..10), 8);
    /// ```
    pub fn visit_items(&self, range: impl RangeBounds<usize>, mut f: impl FnMut(usize, &O::Value)) {
        let range = open(range, self.root.as_ref().map_or(0..0, |n| n.start..n.end));
        if let Some(root) = &self.root {
            assert!(
                root.start <= range.start && range.start <= range.end && range.end <= root.end,
                "Range out of bounds for segment tree"
            );
            root.visit_items(range, &mut f);
        }
    }

    /// 区間 $[l, r)$ を部分木の境界に沿って分解し、分解後の各区間 $[a, b)$ に対して
    /// $f([a, b), x_a \cdot \dots \cdot x_{b-1})$ を呼ぶ。
    ///
    /// 未確保の部分木は単位元 $e$ とみなされるため、その部分の呼び出しは省略される。
    ///
    /// # Panics
    ///
    /// `range` が定義域外のとき panic する。
    pub fn visit_ranges(
        &self,
        range: impl RangeBounds<usize>,
        mut f: impl FnMut(Range<usize>, &O::Value),
    ) {
        let range = open(range, self.root.as_ref().map_or(0..0, |n| n.start..n.end));
        if let Some(root) = &self.root {
            assert!(
                root.start <= range.start && range.start <= range.end && range.end <= root.end,
                "Range out of bounds for segment tree"
            );
            root.visit_ranges(range, &mut f);
        }
    }
}
impl<O: Op> Default for SparseSegtree<O> {
    fn default() -> Self {
        SparseSegtree { root: None }
    }
}
impl<O: Op> Clone for SparseSegtree<O>
where
    O::Value: Clone,
{
    fn clone(&self) -> Self {
        SparseSegtree {
            root: self.root.clone(),
        }
    }
}
impl<O: Op> std::fmt::Debug for SparseSegtree<O>
where
    O::Value: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn dfs<'a, O: Op>(
            node: &'a Node<O>,
            result: &mut std::collections::BTreeMap<usize, &'a O::Value>,
        ) where
            O::Value: std::fmt::Debug,
        {
            if node.start + 1 == node.end {
                result.insert(node.start, &node.value);
            } else {
                if let Some(left) = &node.left {
                    dfs(left, result);
                }
                if let Some(right) = &node.right {
                    dfs(right, result);
                }
            }
        }
        let mut result = std::collections::BTreeMap::new();
        if let Some(root) = &self.root {
            dfs(root, &mut result);
        }
        f.debug_struct("PtrSegtree")
            .field(
                "range",
                &self
                    .root
                    .as_ref()
                    .map_or("(empty)".to_string(), |n| format!("{}..{}", n.start, n.end)),
            )
            .field("nodes", &result)
            .finish()
    }
}
struct Node<O: Op> {
    start: usize,
    end: usize,
    value: O::Value,
    left: Option<Box<Self>>,
    right: Option<Box<Self>>,
}
impl<O: Op> Node<O> {
    fn new_leaf(range: Range<usize>) -> Self {
        let Range { start, end } = range;
        Node {
            start,
            end,
            value: O::identity(),
            left: None,
            right: None,
        }
    }

    fn update(&mut self, i: usize, mut f: impl FnMut(&mut O::Value)) {
        if self.start + 1 == self.end {
            f(&mut self.value);
            return;
        }
        let mid = usize::midpoint(self.start, self.end);
        if i < mid {
            self.left
                .get_or_insert_with(|| Box::new(Node::new_leaf(self.start..mid)))
                .update(i, f);
        } else {
            self.right
                .get_or_insert_with(|| Box::new(Node::new_leaf(mid..self.end)))
                .update(i, f);
        }
        self.recalculate_value();
    }

    fn visit_items(&self, range: Range<usize>, f: &mut impl FnMut(usize, &O::Value)) {
        if self.start + 1 == self.end {
            f(self.start, &self.value);
        } else {
            let mid = usize::midpoint(self.start, self.end);
            if range.start < mid
                && let Some(left) = &self.left
            {
                left.visit_items(open(range.start..range.end, self.start..mid), f);
            }
            if range.end > mid
                && let Some(right) = &self.right
            {
                right.visit_items(open(range.start..range.end, mid..self.end), f);
            }
        }
    }

    fn visit_ranges(&self, range: Range<usize>, f: &mut impl FnMut(Range<usize>, &O::Value)) {
        let Range { start, end } = range;
        if (start, end) == (self.start, self.end) {
            f(self.start..self.end, &self.value);
            return;
        }
        let mid = usize::midpoint(self.start, self.end);
        if end <= mid {
            if let Some(left) = &self.left {
                left.visit_ranges(range, f);
            }
        } else if mid <= start {
            if let Some(right) = &self.right {
                right.visit_ranges(range, f);
            }
        } else {
            if let Some(left) = &self.left {
                left.visit_ranges(start..mid, f);
            }
            if let Some(right) = &self.right {
                right.visit_ranges(mid..end, f);
            }
        }
    }

    fn recalculate_value(&mut self) {
        self.value = O::identity();
        if let Some(left) = &self.left {
            self.value = O::op(&self.value, &left.value);
        }
        if let Some(right) = &self.right {
            self.value = O::op(&self.value, &right.value);
        }
    }
}
impl<O: Op> Clone for Node<O>
where
    O::Value: Clone,
{
    fn clone(&self) -> Self {
        Node {
            start: self.start,
            end: self.end,
            value: self.value.clone(),
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }
}

fn open(a: impl RangeBounds<usize>, b: Range<usize>) -> Range<usize> {
    let start = match a.start_bound() {
        std::ops::Bound::Included(&s) => s,
        std::ops::Bound::Excluded(&s) => s + 1,
        std::ops::Bound::Unbounded => b.start,
    };
    let end = match a.end_bound() {
        std::ops::Bound::Included(&e) => e + 1,
        std::ops::Bound::Excluded(&e) => e,
        std::ops::Bound::Unbounded => b.end,
    };
    Range { start, end }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::BTreeMap;
    use std::mem;

    const P: u32 = 19;
    #[derive(Clone, Debug, Copy, PartialEq, Eq)]
    struct Value {
        a: u32,
        b: u32,
    }

    #[derive(Clone, Debug)]
    enum O {}
    impl Op for O {
        type Value = Value;

        fn identity() -> Self::Value {
            Value { a: 1, b: 0 }
        }

        fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            Value {
                a: (lhs.a * rhs.a) % P,
                b: (lhs.b * rhs.a + rhs.b) % P,
            }
        }
    }

    #[derive(Clone, Debug)]
    struct Mock<O: Op> {
        map: BTreeMap<usize, O::Value>,
    }
    impl<O: Op> Mock<O> {
        fn new() -> Self {
            Mock {
                map: BTreeMap::new(),
            }
        }

        fn update(&mut self, i: usize, f: impl FnOnce(&mut O::Value)) {
            let value = self.map.entry(i).or_insert_with(O::identity);
            f(value);
        }

        fn fold(&self, range: Range<usize>) -> O::Value {
            let mut result = O::identity();
            for i in range {
                if let Some(value) = self.map.get(&i) {
                    result = O::op(&result, value);
                }
            }
            result
        }
    }

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..=30);
            let mut seg = SparseSegtree::<O>::from_range(0..n);
            let mut mock = Mock::<O>::new();
            for _ in 0..3 * n {
                match rng.gen_range(0..3) {
                    // x[i] <- (a, b)
                    0 => {
                        let i = rng.gen_range(0..n);
                        let a = rng.gen_range(1..P);
                        let b = rng.gen_range(0..P);
                        let value = Value { a, b };
                        seg.apply(i, |v| *v = value);
                        mock.update(i, |v| *v = Value { a, b });
                    }
                    // print fold(l..r)
                    1 => {
                        let mut l = rng.gen_range(0..=n);
                        let mut r = rng.gen_range(0..n);
                        if l > r {
                            mem::swap(&mut l, &mut r);
                        }
                        let result = seg.fold(l..r);
                        let expected = mock.fold(l..r);
                        assert_eq!(result, expected, "Failed for range {l}..{r}");
                    }
                    // x[i] <- x[i] * (a, b)
                    2 => {
                        let i = rng.gen_range(0..n);
                        let a = rng.gen_range(1..P);
                        let b = rng.gen_range(0..P);
                        seg.apply(i, |v| {
                            *v = O::op(v, &Value { a, b });
                        });
                        mock.update(i, |v| {
                            *v = O::op(v, &Value { a, b });
                        });
                    }
                    // Visit [l..r[
                    3 => {
                        let mut l = rng.gen_range(0..=n);
                        let mut r = rng.gen_range(0..n);
                        if l > r {
                            mem::swap(&mut l, &mut r);
                        }
                        let mut iter = mock.map.range(l..r).map(|(&i, &v)| (i, v));
                        seg.visit_items(l..r, |i, &v| {
                            if v == O::identity() {
                                return;
                            }
                            let expected = iter
                                .next()
                                .expect("Segment tree visit_leaves should match mock visit_leaves");
                            let result = (i, v);
                            assert_eq!(
                                result, expected,
                                "Segment tree visit mismatch: expected {result:?}, got \
                                 {expected:?}"
                            );
                        });
                        assert!(
                            iter.next().is_none(),
                            "Segment tree visit_leaves should not have extra elements"
                        );
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
