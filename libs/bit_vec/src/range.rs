use std::fmt::Display;

use crate::{div_rem, BitVec, Iter, B};

/// [`BitVec`] のimmutableな部分列。[`BitVec::range`] で構築する。
#[derive(Clone, Copy)]
pub struct Range<'a> {
    pub items: &'a [u64],
    pub start: usize,
    pub end: usize,
}

impl<'a> Range<'a> {
    /// 範囲内の $1$ のビットの個数を返す。
    ///
    /// # 計算量
    ///
    /// 範囲の要素数を $n$、$w = 64$ として $O(n / w)$
    ///
    /// # 例
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
    /// 範囲内で最初に $1$ が立つインデックスを返す。無ければ `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv: BitVec = "00110101".parse().unwrap();
    ///
    /// assert_eq!(bv.range(2..).first_one(), Some(2));
    /// assert_eq!(bv.range(8..).first_one(), None);
    /// ```
    pub fn first_one(self) -> Option<usize> {
        let (q0, r0) = div_rem(self.start);
        let (q1, r1) = div_rem(self.end);
        if q0 == q1 {
            let masked = self.items[q0] & ((1 << r1) - (1 << r0));
            return checked_lsb_position(masked).map(|lsb| q0 * B + lsb);
        }
        let masked = self.items[q0] & (u64::MAX << r0);
        if let Some(lsb) = checked_lsb_position(masked) {
            return Some(q0 * B + lsb);
        }
        for (i, &value) in self.items[q0 + 1..q1].iter().enumerate() {
            if let Some(lsb) = checked_lsb_position(value) {
                return Some((q0 + 1 + i) * B + lsb);
            }
        }
        if r1 != 0 {
            let masked = self.items[q1] & ((1 << r1) - 1);
            return checked_lsb_position(masked).map(|lsb| q1 * B + lsb);
        }
        None
    }
    /// 範囲内のビットを順に返すイテレータを構築する。
    ///
    /// # 例
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
    /// 範囲内のビット全体を `Vec<bool>` に変換する。`.iter().collect()` の短絡メソッド。
    ///
    /// # 例
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
