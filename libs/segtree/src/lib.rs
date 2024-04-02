use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Index;
use std::ops::RangeBounds;

pub trait Op {
    /// The value type.
    type Value;

    /// Returns the identity value.
    fn identity() -> Self::Value;
    /// Multiplies two values.
    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

pub struct Segtree<O: Op> {
    values: Vec<O::Value>,
}
impl<O: Op> Segtree<O> {
    pub fn new(values: &[O::Value]) -> Self
    where
        O::Value: Clone,
    {
        let values_ = values;
        let n = values.len();
        let mut values = vec![O::identity(); 2 * n];
        values[n..].clone_from_slice(values_);
        for i in (1..n).rev() {
            values[i] = O::op(&values[i * 2], &values[i * 2 + 1]);
        }
        Self { values }
    }

    pub fn fold<R: RangeBounds<usize>>(&mut self, range: R) -> O::Value {
        let n = self.values.len() / 2;
        let (mut start, mut end) = open(range, n);
        start += n;
        end += n;
        let mut left = O::identity();
        let mut right = O::identity();
        while start < end {
            if start % 2 == 1 {
                left = O::op(&left, &self.values[start]);
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                right = O::op(&self.values[end], &right);
            }
            start /= 2;
            end /= 2;
        }
        O::op(&left, &right)
    }

    pub fn entry(&mut self, index: usize) -> Entry<O> {
        let n = self.values.len() / 2;
        Entry {
            segtree: self,
            index: n + index,
        }
    }

    pub fn as_slice(&self) -> &[O::Value] {
        &self.values[self.values.len() / 2..]
    }
}

impl<O: Op> Index<usize> for Segtree<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        &self.values[self.values.len() / 2 + index]
    }
}

pub struct Entry<'a, O: Op> {
    segtree: &'a mut Segtree<O>,
    index: usize,
}
impl<'a, O: Op> Drop for Entry<'a, O> {
    fn drop(&mut self) {
        let mut index = self.index;
        while index != 0 {
            index >>= 1;
            self.segtree.values[index] = O::op(
                &self.segtree.values[index << 1],
                &self.segtree.values[(index << 1) + 1],
            );
        }
    }
}
impl<'a, O: Op> Deref for Entry<'a, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target {
        &self.segtree.values[self.index]
    }
}
impl<'a, O: Op> DerefMut for Entry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.segtree.values[self.index]
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
    use std::iter::repeat_with;
    use std::ops::Range;

    const P: u64 = 998244353;
    const BASE: u64 = 10;
    enum O {}
    impl Op for O {
        type Value = (u64, u64);

        fn identity() -> Self::Value {
            (0, 1)
        }

        fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            ((lhs.0 * rhs.1 + rhs.0) % P, lhs.1 * rhs.1 % P)
        }
    }

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let mut vec = repeat_with(|| (rng.gen_range(0..BASE), BASE))
                .take(n)
                .collect::<Vec<_>>();
            let mut segtree = Segtree::<O>::new(&vec);
            for _ in 0..q {
                match rng.gen_range(0..2) {
                    // fold
                    0 => {
                        let range = random_range(&mut rng, n);
                        let expected = vec[range.clone()]
                            .iter()
                            .fold(O::identity(), |acc, x| O::op(&acc, x));
                        let result = segtree.fold(range);
                        assert_eq!(expected, result);
                    }
                    // update
                    1 => {
                        let i = rng.gen_range(0..n);
                        let x = (rng.gen_range(0..BASE), BASE);
                        vec[i] = x;
                        *segtree.entry(i) = x;
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    fn random_range(rng: &mut StdRng, n: usize) -> Range<usize> {
        let start = rng.gen_range(0..=n + 1);
        let end = rng.gen_range(0..=n);
        if start <= end {
            start..end
        } else {
            end..start - 1
        }
    }
}
