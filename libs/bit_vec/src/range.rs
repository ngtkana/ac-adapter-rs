use std::fmt::Display;

use crate::{div_rem, BitVec, Iter};

/// [`BitVec`] の immutable な部分列。[`BitVec::range`] で構築できます。
#[derive(Clone, Copy)]
pub struct Range<'a> {
    pub items: &'a [u64],
    pub start: usize,
    pub end: usize,
}

impl<'a> Range<'a> {
    /// 範囲内の $1$ の bit の個数を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv: BitVec = "00110101".parse().unwrap();
    ///
    /// assert_eq!(bv.range(2..6).count_ones(), 3);
    /// ```
    pub fn count_ones(self) -> usize {
        assert!(self.start <= self.end);
        if self.start == self.end {
            return 0;
        }
        let (q0, r0) = div_rem(self.start);
        let (q1, r1) = div_rem(self.end);
        if q0 == q1 {
            return (self.items[q0] & ((1 << r1) - (1 << r0))).count_ones() as usize;
        }
        let mut result = 0;
        result += (self.items[q0] >> r0).count_ones() as usize;
        for item in &self.items[q0 + 1..q1] {
            result += item.count_ones() as usize;
        }
        if r1 != 0 {
            result += (self.items[q1] & ((1 << r1) - 1)).count_ones() as usize;
        }
        result
    }
    pub fn first_one(self) -> Option<usize> {
        let (q0, r0) = div_rem(self.start);
        let (q1, r1) = div_rem(self.end);
        if q0 == q1 {
            let masked = self.items[q0] & ((1 << r1) - (1 << r0));
            return checked_lsb_position(masked);
        }
        let masked = self.items[q0] & (u64::MAX - (1 << r0));
        if let Some(lsb) = checked_lsb_position(masked) {
            return Some(lsb);
        }
        for &value in &self.items[q0 + 1..q1] {
            if let Some(lsb) = checked_lsb_position(value) {
                return Some(lsb);
            }
        }
        if r1 != 0 {
            let masked = self.items[q1] & ((1 << r1) - 1);
            return checked_lsb_position(masked);
        }
        None
    }
    /// 範囲内の bit を順に返す iterator を構築します
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv: BitVec = "00110101".parse().unwrap();
    ///
    /// let mut iter = bv.range(3..5).iter();
    /// assert_eq!(iter.next(), Some(true));
    /// assert_eq!(iter.next(), Some(false));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(self) -> Iter<'a> {
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
    /// let bv: BitVec = "00110101".parse().unwrap();
    ///
    /// assert_eq!(bv.range(3..5).collect_vec()[..], [true, false][..]);
    /// ```
    pub fn collect_vec(&self) -> Vec<bool> {
        self.iter().collect()
    }
}

impl Display for Range<'_> {
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

impl<'a> IntoIterator for Range<'a> {
    type Item = bool;

    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> From<&'a BitVec> for Range<'a> {
    fn from(value: &'a BitVec) -> Self {
        let BitVec { ref items, len } = *value;
        Self {
            items,
            start: 0,
            end: len,
        }
    }
}

fn checked_lsb_position(value: u64) -> Option<usize> {
    (value != 0).then(|| (value & value.wrapping_neg()).trailing_zeros() as usize)
}
