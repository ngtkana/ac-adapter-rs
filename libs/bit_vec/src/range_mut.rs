use std::fmt::Display;

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
    #[allow(clippy::precedence)]
    fn visit(&mut self, other: impl Into<Range<'a>>, mut f: impl FnMut(&mut u64, u64)) {
        let mut a = RangeMut {
            items: &mut *self.items,
            start: self.start,
            end: self.end,
        };
        let mut b: Range = other.into();
        let len = (a.end - a.start).min(b.end - b.start);
        if len == 0 {
            return;
        }
        a.end = a.start + len;
        b.end = b.start + len;

        if a.start % B == b.start % B {
            if a.start / B == a.end / B {
                f(
                    &mut a.items[a.start / B],
                    b.items[b.start / B] & range_mask(b.start % B..b.end % B),
                );
            } else {
                f(
                    &mut a.items[a.start / B],
                    b.items[b.start / B] & range_mask(a.start % B..),
                );
                for (i, j) in (a.start / B + 1..a.end / B).zip(b.start / B + 1..b.end / B) {
                    f(&mut a.items[i], b.items[j]);
                }
                if a.end % B != 0 {
                    f(
                        &mut a.items[a.end / B],
                        b.items[b.end / B] & range_mask(..b.end % B),
                    );
                }
            }
        } else {
            let dbit = b.start as isize - a.start as isize;
            let dq = dbit.div_euclid(B as isize);
            let dr = (dbit - dq * B as isize) as usize;
            let j = |i: usize| -> usize { i.checked_add_signed(dq).unwrap() };
            if a.start / B == a.end / B {
                if a.start % B < b.start % B {
                    if a.end % B + dr <= B {
                        f(
                            &mut a.items[a.start / B],
                            b.items[j(a.start / B)] >> dr & range_mask(a.start % B..a.end % B),
                        );
                    } else {
                        f(
                            &mut a.items[a.start / B],
                            b.items[j(a.start / B)] >> dr & range_mask(a.start % B..),
                        );
                        f(
                            &mut a.items[a.start / B],
                            b.items[j(a.start / B) + 1] << B - dr & range_mask(..a.end % B),
                        );
                    }
                } else {
                    f(
                        &mut a.items[a.start / B],
                        b.items[((a.start / B) as isize + dq + 1) as usize] << B - dr
                            & range_mask(a.start % B..a.end % B),
                    );
                }
            } else {
                if a.start % B < b.start % B {
                    f(
                        &mut a.items[a.start / B],
                        b.items[j(a.start / B)] >> dr & range_mask(a.start % B..),
                    );
                    f(
                        &mut a.items[a.start / B],
                        b.items[j(a.start / B) + 1] << B - dr,
                    );
                } else {
                    f(
                        &mut a.items[a.start / B],
                        b.items[b.start / B] << B - dr & range_mask(a.start % B..),
                    );
                }
                for i in a.start / B + 1..a.end / B {
                    f(&mut a.items[i], b.items[j(i)] >> dr);
                    f(&mut a.items[i], b.items[j(i) + 1] << B - dr);
                }
                if a.end % B != 0 {
                    if a.end % B + dr <= B {
                        f(
                            &mut a.items[a.end / B],
                            b.items[j(a.end / B)] >> dr & range_mask(..a.end % B),
                        );
                    } else {
                        f(&mut a.items[a.end / B], b.items[j(a.end / B)] >> dr);
                        f(
                            &mut a.items[a.end / B],
                            b.items[j(a.end / B) + 1] << B - dr & range_mask(..a.end % B),
                        );
                    }
                }
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
