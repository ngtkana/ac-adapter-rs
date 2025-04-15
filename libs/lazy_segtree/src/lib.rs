//! # LazySegtree
//!
//! Defines a struct [`LazySegtree`] and a trait [`Op`] for a lazy segment tree.
//!
//! # Note
//!
//! It does not support binary searches.
//!
//! # Example
//!
//! ```
//! use lazy_segtree::LazySegtree;
//! use lazy_segtree::Op;
//!
//! enum O {}
//! impl Op for O {
//!     type Operator = u64;
//!     type Value = u64;
//!
//!     fn identity() -> Self::Value {
//!         0
//!     }
//!
//!     fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
//!         (*lhs).max(*rhs)
//!     }
//!
//!     fn apply(op: &Self::Operator, value: &Self::Value) -> Self::Value {
//!         *op + *value
//!     }
//!
//!     fn identity_op() -> Self::Operator {
//!         0
//!     }
//!
//!     fn compose(op: &Self::Operator, other: &Self::Operator) -> Self::Operator {
//!         *op + *other
//!     }
//! }
//!
//! let mut seg = LazySegtree::<O>::new(&[3, 1, 4, 1, 5, 9, 2, 6]);
//! assert_eq!(seg.fold(0..8), 9);
//! seg.range_apply(3..6, &2);
//! assert_eq!(seg.fold(0..8), 11);
//! ```
use std::iter::FromIterator;
use std::mem::replace;
use std::ops::RangeBounds;

/// Opertions for a lazy segment tree.
pub trait Op {
    /// The value type.
    type Value;
    /// The operator type.
    type Operator: PartialEq;

    /// Returns the identity value.
    fn identity() -> Self::Value;
    /// Multiplies two values.
    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
    /// Applies an operator to a value.
    fn apply(op: &Self::Operator, value: &Self::Value) -> Self::Value;
    /// Returns the identity operator.
    fn identity_op() -> Self::Operator;
    /// Composes two operators.
    /// The result of `compose(a, b)` is equivalent to applying `b` and then `a`.
    fn compose(op: &Self::Operator, other: &Self::Operator) -> Self::Operator;
}

/// A lazy segment tree.
#[derive(Debug, Clone)]
pub struct LazySegtree<O: Op> {
    values: Vec<O::Value>,
    operators: Vec<O::Operator>,
}
impl<O: Op> LazySegtree<O> {
    /// Constructs a new lazy segment tree.
    /// You can use `from_iter` instead of this method.
    pub fn new(values: &[O::Value]) -> Self
    where
        O::Value: Clone,
        O::Operator: Clone,
    {
        let values_ = values;
        let n = values_.len();
        let mut values = vec![O::identity(); 2 * n];
        values[n..].clone_from_slice(values_);
        for i in (1..n).rev() {
            values[i] = O::op(&values[i * 2], &values[i * 2 + 1]);
        }
        Self {
            values,
            operators: vec![O::identity_op(); 2 * n],
        }
    }

    /// Applies an operator to a range.
    pub fn range_apply<R: RangeBounds<usize>>(&mut self, range: R, f: &O::Operator) {
        let n = self.operators.len() / 2;
        let (l, r) = open(range, n);
        if l == r {
            return;
        }
        let l = n + l;
        let r = n + r;
        for p in (0..usize::BITS - r.leading_zeros()).rev() {
            self.push(l >> p);
            self.push((r - 1) >> p);
        }
        {
            let mut l = l;
            let mut r = r;
            while l < r {
                if l & 1 != 0 {
                    self.operators[l] = O::compose(f, &self.operators[l]);
                    l += 1;
                }
                if r & 1 != 0 {
                    r -= 1;
                    self.operators[r] = O::compose(f, &self.operators[r]);
                }
                l >>= 1;
                r >>= 1;
            }
        }
        for p in 1..usize::BITS - r.leading_zeros() {
            self.update(l >> p);
            self.update((r - 1) >> p);
        }
    }

    /// Folds a range.
    pub fn fold<R: RangeBounds<usize>>(&mut self, range: R) -> O::Value {
        let n = self.operators.len() / 2;
        let (mut l, mut r) = open(range, n);
        if l == r {
            return O::identity();
        }
        l += n;
        r += n;
        for p in (0..usize::BITS - r.leading_zeros()).rev() {
            self.push(l >> p);
            self.push((r - 1) >> p);
        }
        for p in 1..usize::BITS - r.leading_zeros() {
            self.update(l >> p);
            self.update((r - 1) >> p);
        }
        let mut left = O::identity();
        let mut right = O::identity();
        while l < r {
            if l & 1 != 0 {
                left = O::op(&left, &O::apply(&self.operators[l], &self.values[l]));
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                right = O::op(&O::apply(&self.operators[r], &self.values[r]), &right);
            }
            l >>= 1;
            r >>= 1;
        }
        O::op(&left, &right)
    }

    /// Returns the value at the index `i`.
    pub fn get(&self, i: usize) -> O::Value
    where
        O::Value: Clone,
    {
        let mut i = self.operators.len() / 2 + i;
        let mut value = self.values[i].clone();
        while i > 0 {
            value = O::apply(&self.operators[i], &value);
            i >>= 1;
        }
        value
    }

    /// Returns the values as a vector.
    /// It takes $O(n \log n)$ time because it calls `get` for each index.
    pub fn collect(&self) -> Vec<O::Value>
    where
        O::Value: Clone,
    {
        (0..self.operators.len() / 2).map(|i| self.get(i)).collect()
    }

    fn push(&mut self, i: usize) {
        let a = replace(&mut self.operators[i], O::identity_op());
        self.values[i] = O::apply(&a, &self.values[i]);
        if i < self.operators.len() / 2 {
            self.operators[i << 1] = O::compose(&a, &self.operators[i << 1]);
            self.operators[i << 1 | 1] = O::compose(&a, &self.operators[i << 1 | 1]);
        }
    }

    fn update(&mut self, i: usize) {
        self.values[i] = O::op(
            &O::apply(&self.operators[i << 1], &self.values[i << 1]),
            &O::apply(&self.operators[i << 1 | 1], &self.values[i << 1 | 1]),
        );
    }
}

impl<O: Op> FromIterator<O::Value> for LazySegtree<O>
where
    O::Value: Clone,
    O::Operator: Clone,
{
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        Self::new(&iter.into_iter().collect::<Vec<_>>())
    }
}

fn open<B: RangeBounds<usize>>(bounds: B, n: usize) -> (usize, usize) {
    use std::ops::Bound;
    let start = match bounds.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    };
    let end = match bounds.end_bound() {
        Bound::Unbounded => n,
        Bound::Included(&x) => x + 1,
        Bound::Excluded(&x) => x,
    };
    (start, end)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    const P: u64 = 998_244_353;

    #[derive(Debug, Clone, Copy, PartialEq)]
    struct Affine {
        a: u64,
        b: u64,
    }
    #[derive(Debug, Clone, Copy, PartialEq)]
    struct Value {
        value: u64,
        len: usize,
    }
    enum O {}
    impl Op for O {
        type Operator = Affine;
        type Value = Value;

        fn identity() -> Self::Value {
            Value { value: 0, len: 0 }
        }

        fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            Value {
                value: (lhs.value + rhs.value) % P,
                len: lhs.len + rhs.len,
            }
        }

        fn apply(op: &Self::Operator, value: &Self::Value) -> Self::Value {
            Value {
                value: (op.a * value.value + op.b * value.len as u64) % P,
                len: value.len,
            }
        }

        fn identity_op() -> Self::Operator {
            Affine { a: 1, b: 0 }
        }

        fn compose(op: &Self::Operator, other: &Self::Operator) -> Self::Operator {
            Affine {
                a: op.a * other.a % P,
                b: (op.a * other.b + op.b) % P,
            }
        }
    }

    #[test]
    fn test_affine() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..=40);
            let q = rng.gen_range(1..=40);
            let mut vec = (0..n)
                .map(|_| Value {
                    value: rng.gen_range(0..P),
                    len: 1,
                })
                .collect::<Vec<_>>();
            let mut seg = LazySegtree::<O>::new(&vec);
            for _ in 0..q {
                match rng.gen_range(0..2) {
                    // range_apply
                    0 => {
                        let mut l = rng.gen_range(0..=n + 1);
                        let mut r = rng.gen_range(0..=n);
                        if l > r {
                            (l, r) = (r, l - 1);
                        }
                        let f = Affine {
                            a: rng.gen_range(0..P),
                            b: rng.gen_range(0..P),
                        };
                        seg.range_apply(l..r, &f);
                        for x in &mut vec[l..r] {
                            *x = O::apply(&f, &*x);
                        }
                    }
                    // fold
                    1 => {
                        let mut l = rng.gen_range(0..=n + 1);
                        let mut r = rng.gen_range(0..=n);
                        if l > r {
                            (l, r) = (r, l - 1);
                        }
                        let result = seg.fold(l..r);
                        let expected = vec[l..r]
                            .iter()
                            .fold(Value { value: 0, len: 0 }, |acc, &x| O::op(&acc, &x));
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
