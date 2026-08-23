use std::{fmt::Display, ops};

use crate::{div_rem, range_mask, BitVec, Iter, Range, B};

/// [`BitVec`] の mutable な部分列。[`BitVec::range`] で構築できます。
pub struct RangeMut<'a> {
    pub items: &'a mut [u64],
    pub start: usize,
    pub end: usize,
}

impl<'a> RangeMut<'a> {
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
    pub fn or_assign(&'a mut self, other: impl Into<Range<'a>>) {
        self.visit(other, |x, y| *x |= y);
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
    pub fn xor_assign(&mut self, other: impl Into<Range<'a>>) {
        self.visit(other, |x, y| *x ^= y);
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
    fn visit(&mut self, other: impl Into<Range<'a>>, f: impl FnMut(&mut u64, u64)) {
        let other: Range = other.into();
        let len = (self.end - self.start).min(other.end - other.start);
        if len == 0 {
            return;
        }

        let dbit = other.start as isize - self.start as isize;
        let dq = dbit.div_euclid(B as isize);
        let dr = (dbit - dq * B as isize) as usize;
        let j = |i: usize| -> usize { i.checked_add_signed(dq).unwrap() };

        let (q0, r0) = div_rem(self.start);
        let (q1, r1) = div_rem(self.start + len);

        #[allow(clippy::collapsible_else_if)]
        if dr == 0 {
            if q0 == q1 {
                visit_case_1_parallel_short(&mut *self.items, other.items, q0, r0..r1, f, j);
            } else {
                visit_case_2_parallel_long(&mut *self.items, other.items, q0..q1, r0..r1, f, j);
            }
        } else {
            if q0 == q1 {
                visit_case_3_skew_short(&mut *self.items, other.items, q0, r0..r1, f, j, dr);
            } else {
                visit_case_4_skew_long(&mut *self.items, other.items, q0..q1, r0..r1, f, j, dr);
            }
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

fn visit_case_1_parallel_short(
    a: &mut [u64],
    b: &[u64],
    q0: usize,
    ops::Range { start: r0, end: r1 }: ops::Range<usize>,
    mut f: impl FnMut(&mut u64, u64),
    j: impl Fn(usize) -> usize,
) {
    f(&mut a[q0], b[j(q0)] & range_mask(r0..r1));
}

fn visit_case_2_parallel_long(
    a: &mut [u64],
    b: &[u64],
    ops::Range { start: q0, end: q1 }: ops::Range<usize>,
    ops::Range { start: r0, end: r1 }: ops::Range<usize>,
    mut f: impl FnMut(&mut u64, u64),
    j: impl Fn(usize) -> usize,
) {
    f(&mut a[q0], b[j(q0)] & range_mask(r0..));
    for i in q0 + 1..q1 {
        f(&mut a[i], b[j(i)]);
    }
    if r1 != 0 {
        f(&mut a[q1], b[j(q1)] & range_mask(..r1));
    }
}

#[allow(clippy::precedence)]
fn visit_case_3_skew_short(
    a: &mut [u64],
    b: &[u64],
    q0: usize,
    ops::Range { start: r0, end: r1 }: ops::Range<usize>,
    mut f: impl FnMut(&mut u64, u64),
    j: impl Fn(usize) -> usize,
    dr: usize,
) {
    if r0 + dr < B {
        if r1 + dr <= B {
            f(&mut a[q0], b[j(q0)] >> dr & range_mask(r0..r1));
        } else {
            f(&mut a[q0], b[j(q0)] >> dr & range_mask(r0..));
            f(&mut a[q0], b[j(q0 + 1)] << B - dr & range_mask(..r1));
        }
    } else {
        f(&mut a[q0], b[j(q0 + 1)] << B - dr & range_mask(r0..r1));
    }
}

#[allow(clippy::precedence)]
fn visit_case_4_skew_long(
    a: &mut [u64],
    b: &[u64],
    ops::Range { start: q0, end: q1 }: ops::Range<usize>,
    ops::Range { start: r0, end: r1 }: ops::Range<usize>,
    mut f: impl FnMut(&mut u64, u64),
    j: impl Fn(usize) -> usize,
    dr: usize,
) {
    if r0 + dr < B {
        f(&mut a[q0], b[j(q0)] >> dr & range_mask(r0..));
        f(&mut a[q0], b[j(q0 + 1)] << B - dr);
    } else {
        f(&mut a[q0], b[j(q0 + 1)] << B - dr & range_mask(r0..));
    }
    for i in q0 + 1..q1 {
        f(&mut a[i], b[j(i)] >> dr);
        f(&mut a[i], b[j(i + 1)] << B - dr);
    }
    if r1 != 0 {
        if r1 + dr <= B {
            f(&mut a[q1], b[j(q1)] >> dr & range_mask(..r1));
        } else {
            f(&mut a[q1], b[j(q1)] >> dr);
            f(&mut a[q1], b[j(q1 + 1)] << B - dr & range_mask(..r1));
        }
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
