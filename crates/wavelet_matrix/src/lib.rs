use std::mem::size_of;

const UNIT: usize = size_of::<usize>();

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct StaticBitVec {
    len: usize,
    rank: Vec<usize>,
    pattern: Vec<usize>,
}
impl FromIterator<bool> for StaticBitVec {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        let mut rank = Vec::new();
        let mut pattern = Vec::new();
        let mut rank_c = 0;
        let mut pattern_c = 0;
        let mut len = 0;
        'OUTER: loop {
            rank.push(rank_c);
            for i in 0..UNIT {
                match iter.next() {
                    None => {
                        pattern.push(pattern_c);
                        break 'OUTER;
                    }
                    Some(false) => (),
                    Some(true) => {
                        pattern_c |= 1 << i;
                        rank_c += 1;
                    }
                }
                len += 1;
            }
            pattern.push(pattern_c);
            pattern_c = 0;
        }
        Self { len, rank, pattern }
    }
}
impl StaticBitVec {
    /// `a[i]`
    pub fn access(&self, i: usize) -> bool {
        assert!(i < self.len);
        let (q, r) = divrem(i, UNIT);
        self.pattern[q] >> r & 1 == 1
    }
    /// `sum(a[..end])`
    pub fn rank(&self, end: usize) -> usize {
        assert!(end <= self.len);
        let (q, r) = divrem(end, UNIT);
        self.rank[q] + (self.pattern[q] & ((1 << r) - 1)).count_ones() as usize
    }
    /// min i s.t. `target <= sum(a[..i])`
    pub fn select(&self, target: usize) -> usize {
        if target == 0 {
            return 0;
        }
        let mut lr = [0, self.rank.len()];
        while 1 < lr[1] - lr[0] {
            let c = lr[0] + (lr[1] - lr[0]) / 2;
            lr[(target <= self.rank[c]) as usize] = c;
        }
        let q = lr[0];
        let mut lr = [0, UNIT];
        while 1 < lr[1] - lr[0] {
            let c = lr[0] + (lr[1] - lr[0]) / 2;
            lr[(target <= self.rank[q] + (self.pattern[q] & ((1 << c) - 1)).count_ones() as usize)
                as usize] = c;
        }
        let r = lr[1];
        q * UNIT + r
    }
}

fn divrem(num: usize, den: usize) -> (usize, usize) {
    let q = num / den;
    (q, num - q * den)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use std::iter::repeat_with;

    #[test]
    fn test_static_bitvec_small() {
        for n in 0..=8_usize {
            for bs in 0..1_u32 << n {
                let bitvec = (0..n).map(|i| bs >> i & 1 == 1).collect::<StaticBitVec>();

                // access
                for i in 0..n {
                    let expected = bs >> i & 1 == 1;
                    assert_eq!(bitvec.access(i), expected);
                }

                // rank
                for i in 0..=n {
                    let expected = (bs & (1 << i) - 1).count_ones() as usize;
                    assert_eq!(bitvec.rank(i), expected);
                }

                // select
                for j in 0..=bs.count_ones() as usize {
                    let expected = (0..).find(|&i| j <= bitvec.rank(i)).unwrap();
                    assert_eq!(bitvec.select(j), expected);
                }
            }
        }
    }

    #[test]
    fn test_static_bitvec_large() {
        let mut rng = StdRng::seed_from_u64(42);
        for (n, p) in vec![(9, 0.5), (15, 0.5), (300, 0.5), (300, 0.1), (300, 0.9)] {
            for _ in 0..20 {
                let vec = repeat_with(|| rng.gen_bool(p)).take(n).collect::<Vec<_>>();
                let bitvec = vec.iter().copied().collect::<StaticBitVec>();

                // access
                for i in 0..n {
                    let expected = vec[i];
                    assert_eq!(bitvec.access(i), expected);
                }

                // rank
                for i in 0..=n {
                    let expected = vec[..i].iter().filter(|&&b| b).count();
                    assert_eq!(bitvec.rank(i), expected);
                }

                // select
                let count = vec.iter().filter(|&&b| b).count();
                for j in 0..=count {
                    let expected = (0..).find(|&i| j <= bitvec.rank(i)).unwrap();
                    assert_eq!(bitvec.select(j), expected);
                }
            }
        }
    }
}
