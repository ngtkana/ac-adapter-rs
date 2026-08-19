use std::fmt::Display;

use crate::{div_rem, BitVec, Iter, Range, B};

/// [`BitVec`] の mutable な部分列。[`BitVec::range`] で構築できます。
pub struct RangeMut<'a> {
    pub items: &'a mut [u64],
    pub start: usize,
    pub end: usize,
}

impl RangeMut<'_> {
    /// 範囲内の bit を全て flip します。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// bv.range_mut(2..6).flip();
    ///
    /// assert_eq!(bv.to_string(), "00001001");
    /// ```
    pub fn flip(&mut self) {
        assert!(self.start <= self.end);
        if self.start == self.end {
            return;
        }
        let (q0, r0) = div_rem(self.start);
        let (q1, r1) = div_rem(self.end);
        if q0 == q1 {
            self.items[q0] ^= (1 << r1) - (1 << r0);
            return;
        }
        if r0 == 0 {
            self.items[q0] = !self.items[q0];
        } else {
            self.items[q0] ^= ((1 << (B - r0)) - 1) << r0;
        }
        for item in &mut self.items[q0 + 1..q1] {
            *item = !*item;
        }
        if r1 != 0 {
            self.items[q1] ^= (1 << r1) - 1;
        }
    }
    /// Bitwise or で更新します。長さが異なる場合は短い方に合わせます。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// bv.range_mut(2..6).or_assign(&("1111").parse::<BitVec>().unwrap());
    ///
    /// assert_eq!(bv.to_string(), "00111101");
    /// ```
    pub fn or_assign<'a>(&'a mut self, other: impl Into<Range<'a>>) {
        let other = other.into();
        let mut self_start = self.start;
        let mut other_start = other.start;
        while self_start < self.end && other_start < other.end {
            let (q0, r0) = div_rem(self_start);
            let (q1, r1) = div_rem(other_start);
            let d = (self.end - self_start)
                .min(B - r0)
                .min(other.end - other_start)
                .min(B - r1);
            if d == B {
                self.items[q0] |= other.items[q1];
            } else {
                let mut value = other.items[q1] & (((1 << d) - 1) << r1);
                if r0 < r1 {
                    value >>= r1 - r0;
                } else if r0 > r1 {
                    value <<= r0 - r1;
                }
                self.items[q0] |= value;
            }
            self_start += d;
            other_start += d;
        }
    }
    /// Bitwise xor で更新します。長さが異なる場合は短い方に合わせます。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// bv.range_mut(2..6).xor_assign(&("1111").parse::<BitVec>().unwrap());
    ///
    /// assert_eq!(bv.to_string(), "00001001");
    /// ```
    pub fn xor_assign<'a>(&'a mut self, other: impl Into<Range<'a>>) {
        let other = other.into();
        let mut self_start = self.start;
        let mut other_start = other.start;
        while self_start < self.end && other_start < other.end {
            let (q0, r0) = div_rem(self_start);
            let (q1, r1) = div_rem(other_start);
            let d = (self.end - self_start)
                .min(B - r0)
                .min(other.end - other_start)
                .min(B - r1);
            if d == B {
                self.items[q0] ^= other.items[q1];
            } else {
                let mut value = other.items[q1] & (((1 << d) - 1) << r1);
                if r0 < r1 {
                    value >>= r1 - r0;
                } else if r0 > r1 {
                    value <<= r0 - r1;
                }
                self.items[q0] ^= value;
            }
            self_start += d;
            other_start += d;
        }
    }
    /// 範囲内の bit を順に返す iterator を構築します
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// let mut range = bv.range_mut(3..5);
    ///
    /// let mut iter = range.iter();
    /// assert_eq!(iter.next(), Some(true));
    /// assert_eq!(iter.next(), Some(false));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            items: self.items,
            start: self.start,
            end: self.end,
        }
    }
    /// 範囲内の bit 全体からなる [`Vec<bool>`] に変換します。これは `.iter().collect()` の短絡メソッドです。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// let mut range = bv.range_mut(3..5);
    ///
    /// assert_eq!(range.collect_vec()[..], [true, false][..]);
    /// ```
    pub fn collect_vec(&self) -> Vec<bool> {
        self.iter().collect()
    }
}

impl Display for RangeMut<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.iter()
                .map(|b| if b { '1' } else { '0' })
                .collect::<String>()
        )
    }
}

impl<'a> IntoIterator for &'a RangeMut<'a> {
    type Item = bool;

    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> From<&'a mut BitVec> for RangeMut<'a> {
    fn from(value: &'a mut BitVec) -> Self {
        let BitVec { ref mut items, len } = *value;
        Self {
            items,
            start: 0,
            end: len,
        }
    }
}

// pub fn or_assign<'a>(&'a mut self, other: impl Into<Range<'a>>) {
//     let other = other.into();
//     let len = (self.end - self.start).min(other.end - other.start);
//     let (qi0, ri0) = div_rem(self.start);
//     let (qj0, rj0) = div_rem(other.start);
//     let (qi1, ri1) = div_rem(self.start + len);
//     let (qj1, rj1) = div_rem(other.start + len);
//     let a = &mut self.items;
//     let b = &other.items;
//     #[allow(unused_variables)]
//     let (qi0, ri0, qj0, rj0) = match ri0.cmp(&rj0) {
//         Ordering::Less => {
//             if qj0 == qj1 {
//                 a[qi0] |= (a[qj0] >> (rj0 - ri0)) & ((1 << ri1) - (1 << ri0));
//                 return;
//             }
//             a[qi0] |= (a[qj0] & (u64::MAX - (1 << rj0))) >> (rj0 - ri0);
//             if qi0 == qj1 {
//                 a[qi0] |= a[qj0 + 1] & ((1 << rj0) - 1) << (ri0 + B - rj0);
//                 return;
//             }
//             a[qi0] |= a[qj0 + 1] << (B - rj0 + ri0);
//             (qi0 + 1, 0, qj0 + 1, rj0 - ri0)
//         }
//         Ordering::Greater => {
//             if qi0 == qj1 {
//                 a[qi0] |= (b[qj0] << (ri0 - rj0)) & ((1 << ri1) - (1 << ri0));
//                 return;
//             }
//             a[qi0] |= (b[qj0] << (ri0 - rj0)) & (u64::MAX - (1 << ri0));
//             (qi0 + 1, 0, qj0, B - ri0 + rj0)
//         }
//         Ordering::Equal => {
//             if qi0 == qj1 {
//                 a[qi0] |= b[qj0] & ((1 << ri1) - (1 << ri0));
//                 return;
//             }
//             if ri0 != 0 {
//                 a[qi0] |= b[qj0] & (u64::MAX - (1 << ri0));
//             }
//             (qi0 + 1, 0, qj0, 0)
//         }
//     };
//     if rj0 == 0 {
//         assert_eq!(ri1, rj1);
//         assert_eq!(qi1 - qi0, qj1 - qj0);
//         for (qi, qj) in (qi0..qi1).zip(qj0..) {
//             a[qi] |= b[qj];
//         }
//         if ri1 != 0 {
//             a[qi1] |= b[qj1] & ((1 << rj1) - 1);
//         }
//     } else {
//         if 2 <= qi1 - qi0 {
//             for (qi, qj) in (qi0..qi1 - 1).zip(qj0..) {
//                 a[qi] |= a[qj] >> rj0 | a[qj + 1] << (B - rj0);
//             }
//         }
//         if ri1 < rj1 {
//             assert_eq!(qi1 - qi0, qj1 - qj0);
//             a[qi1 - 1] |= (b[qj1 - 1] >> rj0) & (1 << rj0);
//         } else {
//             assert_eq!(qi1 - qi0 + 1, qj1 - qj0);
//             a[qi1 - 1] |= b[qj1 - 2] >> rj0;
//             a[qi1 - 1] |= (b[qj1 - 1] << (B - rj0)) & ((1 << ri1) - 1);
//         }
//     }
// }
