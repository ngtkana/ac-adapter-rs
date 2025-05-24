//! Sparse Segment Tree
use std::ops::{Range, RangeBounds};

/// Trait for operations on the segment tree.
pub trait Op {
    type Value;
    fn identity() -> Self::Value;
    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

/// A sparse segment tree.
///
/// # Example
///
/// ```rust
/// use sparse_segtree::{SparseSegtree, Op};
///
/// #[derive(Clone, Debug)]
/// enum SumOp {}
/// impl Op for SumOp {
///    type Value = i64;
///    fn identity() -> Self::Value {
///        0
///    }
///    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
///        lhs + rhs
///    }
/// }
///
/// let mut seg = SparseSegtree::<SumOp>::from_range(0..10);
///
/// seg.update(2, |x| *x += 5);
/// assert_eq!(seg.fold(0..10), 5);
///
/// seg.update(5, |x| *x += 3);
/// assert_eq!(seg.fold(0..10), 8);
/// ```
pub struct SparseSegtree<O: Op> {
    root: Option<Box<Node<O>>>,
}
impl<O: Op> SparseSegtree<O> {
    /// Create a new sparse segment tree from a range (domain of definition).
    pub fn from_range(range: Range<usize>) -> Self {
        let root = (!range.is_empty()).then(|| Box::new(Node::new_leaf(range)));
        SparseSegtree { root }
    }
    /// Mutate $x_i$ by $f(x_i)$.
    pub fn update(&mut self, i: usize, f: impl FnMut(&mut O::Value)) {
        let Some(root) = self.root.as_mut() else {
            panic!("Cannot update an empty segment tree");
        };
        assert!(
            (root.start..root.end).contains(&i),
            "Index out of bounds for segment tree"
        );
        root.update(i, f);
    }
    /// Return $x_l \cdot x_{l+1} \cdots x_{r-1}$.
    pub fn fold(&self, range: Range<usize>) -> O::Value {
        let mut result = O::identity();
        self.visit_ranges(range, |_, value| {
            result = O::mul(&result, value);
        });
        result
    }
    /// Call $f(i, x_i)$ for each $i \in [l, r[$ from left to right,
    ///
    /// # Notes
    ///
    /// This may visit extra $\mathrm{id}$s.
    ///
    /// # Example
    ///
    /// ```rust
    /// use sparse_segtree::{SparseSegtree, Op};
    /// /* define `enum SumOp` and implement `Op` trait */
    /// # #[derive(Clone, Debug)]
    /// # enum SumOp {}
    /// # impl Op for SumOp {
    /// #    type Value = i64;
    /// #    fn identity() -> Self::Value {
    /// #        0
    /// #    }
    /// #    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
    /// #        lhs + rhs
    /// #    }
    /// # }
    /// let mut seg = SparseSegtree::<SumOp>::from_range(0..10);
    /// seg.update(2, |x| *x += 5);
    /// seg.update(5, |x| *x += 3);
    /// assert_eq!(seg.fold(0..10), 8);
    /// ```
    pub fn visit_items(&self, range: impl RangeBounds<usize>, mut f: impl FnMut(usize, &O::Value)) {
        let range = open(range, self.root.as_ref().map_or(0..0, |n| n.start..n.end));
        if let Some(root) = &self.root {
            root.visit_items(range, &mut f);
        }
    }

    /// Call $f(l..r, \mathrm{fold}(l..r))$ decomposing the range into segments.
    pub fn visit_ranges(
        &self,
        range: impl RangeBounds<usize>,
        mut f: impl FnMut(Range<usize>, &O::Value),
    ) {
        let range = open(range, self.root.as_ref().map_or(0..0, |n| n.start..n.end));
        if let Some(root) = &self.root {
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
        let mid = (self.start + self.end) / 2;
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
            let mid = (self.start + self.end) / 2;
            if range.start < mid {
                if let Some(left) = &self.left {
                    left.visit_items(open(range.start..range.end, self.start..mid), f);
                }
            }
            if range.end > mid {
                if let Some(right) = &self.right {
                    right.visit_items(open(range.start..range.end, mid..self.end), f);
                }
            }
        }
    }
    fn visit_ranges(&self, range: Range<usize>, f: &mut impl FnMut(Range<usize>, &O::Value)) {
        let Range { start, end } = range;
        if (start, end) == (self.start, self.end) {
            f(self.start..self.end, &self.value);
            return;
        }
        let mid = (self.start + self.end) / 2;
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
            self.value = O::mul(&self.value, &left.value);
        }
        if let Some(right) = &self.right {
            self.value = O::mul(&self.value, &right.value);
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
    use std::{collections::BTreeMap, mem};

    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};

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
        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
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
                    result = O::mul(&result, value);
                }
            }
            result
        }
    }

    #[test]
    fn test() {
        let mut rng = StdRng::from_entropy();
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
                        seg.update(i, |v| *v = value);
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
                        seg.update(i, |v| {
                            *v = O::mul(v, &Value { a, b });
                        });
                        mock.update(i, |v| {
                            *v = O::mul(v, &Value { a, b });
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
                                "Segment tree visit mismatch: expected {result:?}, got {expected:?}"
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
