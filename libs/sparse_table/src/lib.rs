//! Sparse table です。いまのところ Argmin しかありません。
use std::ops;

#[derive(Debug, Clone)]
pub struct SparseTableArgmin<T> {
    table: Vec<Vec<usize>>,
    seq: Vec<T>,
}

impl<T: Ord> SparseTableArgmin<T> {
    pub fn from_vec(seq: Vec<T>) -> Self {
        let n = seq.len();
        let mut table = vec![(0..n).collect::<Vec<_>>()];
        let mut d = 1;
        while 2 * d < n {
            let prv = table.last().unwrap();
            let mut crr = prv.clone();
            for i in 0..n - d {
                if seq[crr[i + d]] < seq[crr[i]] {
                    crr[i] = crr[i + d];
                }
            }
            table.push(crr);
            d *= 2;
        }
        Self { table, seq }
    }

    pub fn query(&self, range: impl ops::RangeBounds<usize>) -> Option<usize> {
        let ops::Range { start, end } = convert_to_range(self.seq.len(), range);
        assert!(start <= end);
        if start == end {
            None
        } else {
            Some(if start + 1 == end {
                start
            } else {
                let d = (end - start).next_power_of_two() / 2;
                let row = &self.table[d.trailing_zeros() as usize];
                let u = row[start];
                let v = row[end - d];
                if self.seq[u] <= self.seq[v] {
                    u
                } else {
                    v
                }
            })
        }
    }

    #[inline]
    pub fn min(&self, range: impl ops::RangeBounds<usize>) -> Option<&T> {
        self.query(range).map(|i| &self.seq[i])
    }

    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&I::Output>
    where
        I: std::slice::SliceIndex<[T]>,
    {
        self.seq.get(index)
    }
}

impl<I, T> ops::Index<I> for SparseTableArgmin<T>
where
    I: std::slice::SliceIndex<[T]>,
    T: Clone,
{
    type Output = I::Output;

    fn index(&self, index: I) -> &I::Output {
        self.seq.index(index)
    }
}

fn convert_to_range<T>(len: usize, range_bound: T) -> ops::Range<usize>
where
    T: ops::RangeBounds<usize>,
{
    use ops::Bound::Excluded;
    use ops::Bound::Included;
    use ops::Bound::Unbounded;
    ops::Range {
        start: match range_bound.start_bound() {
            Excluded(&x) => x + 1,
            Included(&x) => x,
            Unbounded => 0,
        },
        end: match range_bound.end_bound() {
            Excluded(&x) => x,
            Included(&x) => x + 1,
            Unbounded => len,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hand() {
        let a = vec![4, 3, 5, 1, 3, 2];
        let spt = SparseTableArgmin::from_vec(a);
        assert_eq!(spt.query(3..3), None);
        assert_eq!(spt.query(5..6), Some(5));
        assert_eq!(spt.query(1..3), Some(1));
        assert_eq!(spt.query(1..5), Some(3));
        assert_eq!(spt.query(0..6), Some(3));
        assert_eq!(spt.query(0..=3), Some(3));
        assert_eq!(spt.query(0..=2), Some(1));
        assert_eq!(spt.query(..), Some(3));
    }

    #[test]
    fn test_random() {
        const LEN_MAX: usize = 40;
        const VALUE_MAX: u32 = 16;
        const NUMBER_OF_INSTANCE: usize = 80;
        const NUMBER_OF_QUERIES: usize = 80;

        for _ in 0..NUMBER_OF_INSTANCE {
            let a = std::iter::repeat_with(|| rand::random::<u32>() % VALUE_MAX)
                .take(LEN_MAX)
                .collect::<Vec<_>>();
            let spt = SparseTableArgmin::from_vec(a.clone());

            for _ in 0..NUMBER_OF_QUERIES {
                let (l, r) = {
                    let mut l = rand::random::<usize>() % LEN_MAX;
                    let mut r = rand::random::<usize>() % LEN_MAX;
                    if l > r {
                        std::mem::swap(&mut l, &mut r);
                    }
                    r += 1;
                    (l, r)
                };
                let expected = a
                    .iter()
                    .enumerate()
                    .skip(l)
                    .take(r - l)
                    .map(|(i, &x)| (x, i))
                    .min()
                    .map(|(_, i)| i);
                let result = spt.query(l..r);
                assert_eq!(expected, result);
            }
        }
    }
}
