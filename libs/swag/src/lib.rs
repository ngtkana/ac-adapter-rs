//! # Sliding Window Aggregation (SWAG)
//!
//! * [`DequeueSwag`]: A foldable deque.
//!
//! # Constructors
//!
//! * [`new()`](DequeueSwag::new): Constructs a new [`DequeueSwag`].
//! * [`from`](DequeueSwag::from): [`Vec`] -> [`DequeueSwag`].
//! * [`from_iter`](DequeueSwag::from_iter): [`IntoIterator`] -> [`DequeueSwag`].
//! * [`clone_from_slice`](DequeueSwag::clone_from_slice), [`copy_from_slice`](DequeueSwag::copy_from_slice): [`&[T]`] -> [`DequeueSwag`].

use std::iter::FromIterator;
use std::ops::Index;

/// Operations
pub trait Op {
    /// Value type
    type Value;

    /// Associative operation
    fn op(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

/// DequeueSwag
pub struct DequeueSwag<O: Op> {
    front: Vec<O::Value>,
    back: Vec<O::Value>,
    front_sum: Vec<O::Value>,
    back_sum: Vec<O::Value>,
}
impl<O: Op> DequeueSwag<O> {
    /// Constructs a new `DequeueSwag`.
    pub fn new() -> Self {
        Self {
            front: Vec::new(),
            back: Vec::new(),
            front_sum: Vec::new(),
            back_sum: Vec::new(),
        }
    }

    /// Returns the element at the index.
    pub fn get(&self, i: usize) -> Option<&O::Value> {
        if i < self.front.len() {
            Some(&self.front[self.front.len() - i - 1])
        } else if i < self.front.len() + self.back.len() {
            Some(&self.back[i - self.front.len()])
        } else {
            None
        }
    }

    /// Returns the length of the `DequeueSwag`.
    pub fn len(&self) -> usize {
        self.front.len() + self.back.len()
    }

    /// Returns whether the `DequeueSwag` is empty.
    pub fn is_empty(&self) -> bool {
        self.front.is_empty() && self.back.is_empty()
    }

    /// Append an element to the front.
    ///
    /// # Example
    ///
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[2, 3, 4]);
    /// swag.push_front(1);
    /// assert_eq!(swag.collect_vec(), vec![1, 2, 3, 4]);
    /// ```
    pub fn push_front(&mut self, x: O::Value)
    where
        O::Value: Clone,
    {
        self.front_sum.push(if self.front_sum.is_empty() {
            x.clone()
        } else {
            O::op(&x, self.front_sum.last().unwrap())
        });
        self.front.push(x);
    }

    /// Append an element to the back.
    ///
    /// # Example
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// swag.push_back(4);
    /// assert_eq!(swag.collect_vec(), vec![1, 2, 3, 4]);
    /// ```
    pub fn push_back(&mut self, x: O::Value)
    where
        O::Value: Clone,
    {
        self.back_sum.push(if self.back_sum.is_empty() {
            x.clone()
        } else {
            O::op(self.back_sum.last().unwrap(), &x)
        });
        self.back.push(x);
    }

    /// Pop an element from the front.
    /// Returns `None` if the `DequeueSwag` is empty.
    /// # Example
    /// ```
    /// use swag::DequeueSwag;
    /// # enum O {}
    /// # impl swag::Op for O {
    /// #    type Value = i32;
    /// #    fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    /// #        a + b
    /// #    }
    /// # }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// assert_eq!(swag.pop_front(), Some(1));
    /// assert_eq!(swag.collect_vec(), vec![2, 3]);
    /// ```
    pub fn pop_front(&mut self) -> Option<O::Value>
    where
        O::Value: Clone,
    {
        if self.front.is_empty() {
            let n = self.back.len();
            let mut swp = Self::new();
            for x in self.back.drain(..(n + 1) / 2).rev() {
                swp.push_front(x);
            }
            for x in self.back.drain(..) {
                swp.push_back(x);
            }
            *self = swp;
        }
        let _ = self.front_sum.pop();
        self.front.pop()
    }

    /// Pop an element from the back.
    /// Returns `None` if the `DequeueSwag` is empty.
    /// # Example
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// assert_eq!(swag.pop_back(), Some(3));
    /// assert_eq!(swag.collect_vec(), vec![1, 2]);
    /// ```
    pub fn pop_back(&mut self) -> Option<O::Value>
    where
        O::Value: Clone,
    {
        if self.back.is_empty() {
            let n = self.front.len();
            let mut swp = Self::new();
            for x in self.front.drain((n + 1) / 2..) {
                swp.push_front(x);
            }
            for x in self.front.drain(..).rev() {
                swp.push_back(x);
            }
            *self = swp;
        }
        let _ = self.back_sum.pop();
        self.back.pop()
    }

    /// Fold the `DequeueSwag`.
    /// Returns `None` if the `DequeueSwag` is empty.
    /// # Example
    /// ```
    /// use swag::DequeueSwag;
    /// enum O {}
    /// impl swag::Op for O {
    ///     type Value = i32;
    ///
    ///     fn op(a: &Self::Value, b: &Self::Value) -> Self::Value {
    ///         a + b
    ///     }
    /// }
    /// let mut swag = DequeueSwag::<O>::copy_from_slice(&[1, 2, 3]);
    /// assert_eq!(swag.fold(), Some(6));
    /// ```
    pub fn fold(&self) -> Option<O::Value>
    where
        O::Value: Clone,
    {
        match (self.front_sum.last(), self.back_sum.last()) {
            (None, None) => None,
            (Some(x), None) | (None, Some(x)) => Some(x.clone()),
            (Some(x), Some(y)) => Some(O::op(x, y)),
        }
    }

    /// Returns an iterator over the `DequeueSwag`.
    pub fn iter(&self) -> impl Iterator<Item = &O::Value> {
        self.front.iter().rev().chain(self.back.iter())
    }

    /// Collects the `DequeueSwag` into a `Vec`.
    pub fn collect_vec(&self) -> Vec<O::Value>
    where
        O::Value: Clone,
    {
        self.iter().cloned().collect()
    }

    /// Returns two slices, joining that is exactly the all elements.
    pub fn as_two_slices(&self) -> (&[O::Value], &[O::Value]) {
        (&self.front, &self.back)
    }

    /// Constructs a new `DequeueSwag` from a slice.
    pub fn clone_from_slice(slice: &[O::Value]) -> Self
    where
        O::Value: Clone,
    {
        let mut reslt = Self::new();
        for x in slice {
            reslt.push_back(x.clone());
        }
        reslt
    }

    /// Constructs a new `DequeueSwag` from a slice.
    pub fn copy_from_slice(slice: &[O::Value]) -> Self
    where
        O::Value: Copy,
    {
        let mut reslt = Self::new();
        for x in slice {
            reslt.push_back(*x);
        }
        reslt
    }
}

impl<O: Op> Default for DequeueSwag<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Op> Index<usize> for DequeueSwag<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.front.len() {
            &self.front[self.front.len() - index - 1]
        } else {
            &self.back[index - self.front.len()]
        }
    }
}

impl<O: Op> std::fmt::Debug for DequeueSwag<O>
where
    O::Value: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DequeueSwag")
            .field("front", &self.front)
            .field("back", &self.back)
            .field("front_sum", &self.front_sum)
            .field("back_sum", &self.back_sum)
            .finish()
    }
}

impl<O: Op> From<Vec<O::Value>> for DequeueSwag<O>
where
    O::Value: Clone,
{
    fn from(mut values: Vec<O::Value>) -> Self {
        let mut reslt = Self::new();
        let n = values.len();
        for x in values.drain(n / 2..) {
            reslt.push_back(x);
        }
        for x in values.into_iter().rev() {
            reslt.push_front(x);
        }
        reslt
    }
}

impl<O: Op> IntoIterator for DequeueSwag<O> {
    type IntoIter = std::iter::Chain<
        std::iter::Rev<std::vec::IntoIter<O::Value>>,
        std::vec::IntoIter<O::Value>,
    >;
    type Item = O::Value;

    fn into_iter(self) -> Self::IntoIter {
        self.front.into_iter().rev().chain(self.back)
    }
}

impl<'a, O: Op> IntoIterator for &'a DequeueSwag<O> {
    type IntoIter = std::iter::Chain<
        std::iter::Rev<std::slice::Iter<'a, O::Value>>,
        std::slice::Iter<'a, O::Value>,
    >;
    type Item = &'a O::Value;

    fn into_iter(self) -> Self::IntoIter {
        self.front.iter().rev().chain(self.back.iter())
    }
}

impl<O: Op> FromIterator<O::Value> for DequeueSwag<O>
where
    O::Value: Clone,
{
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        iter.into_iter().collect::<Vec<_>>().into()
    }
}

impl<O: Op> Extend<O::Value> for DequeueSwag<O>
where
    O::Value: Clone,
{
    fn extend<T: IntoIterator<Item = O::Value>>(&mut self, iter: T) {
        for x in iter {
            self.push_back(x);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::VecDeque;
    use std::fmt::Debug;
    use std::ops::Add;
    use std::ops::Mul;

    const P: u64 = 998244353;

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    struct Fp(u64);
    impl Debug for Fp {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }
    impl Add for Fp {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output {
            Fp((self.0 + rhs.0) % P)
        }
    }

    impl Mul for Fp {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            Fp(self.0 * rhs.0 % P)
        }
    }

    enum Affine {}
    impl Op for Affine {
        type Value = (Fp, Fp);

        fn op(&(a, b): &Self::Value, &(c, d): &Self::Value) -> Self::Value {
            (a * c, d + c * b)
        }
    }

    #[test]
    fn test_swag() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let q = 10;
            let mut swag = DequeueSwag::<Affine>::new();
            let mut deque = VecDeque::new();
            for _ in 0..q {
                match rng.gen_range(0..4) {
                    0 => {
                        let a = Fp(rng.gen_range(0..4));
                        let b = Fp(rng.gen_range(0..4));
                        eprintln!("push_front {:?}", (a, b));
                        swag.push_front((a, b));
                        deque.push_front((a, b));
                    }
                    1 => {
                        let a = Fp(rng.gen_range(0..4));
                        let b = Fp(rng.gen_range(0..4));
                        eprintln!("push_back {:?}", (a, b));
                        swag.push_back((a, b));
                        deque.push_back((a, b));
                    }
                    2 => {
                        eprintln!("pop_front");
                        assert_eq!(swag.pop_front(), deque.pop_front());
                    }
                    3 => {
                        eprintln!("pop_back");
                        assert_eq!(swag.pop_back(), deque.pop_back());
                    }
                    _ => unreachable!(),
                }
                eprintln!("{:?}", deque);
                eprintln!("{:?}", swag);
                let result = swag.fold().unwrap_or((Fp(1), Fp(0)));
                let expected = deque
                    .iter()
                    .fold((Fp(1), Fp(0)), |acc, x| Affine::op(&acc, x));
                assert_eq!(result, expected);
                let result = swag.collect_vec();
                let expected = deque.iter().copied().collect::<Vec<_>>();
                assert_eq!(result, expected);
                eprintln!("---");
            }
        }
    }
}
