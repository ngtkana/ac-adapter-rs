//! 論理的な [`bool`] 配列 $A$ を、長さ $\lceil \\# A / 64 \rceil$ の [`Vec<u64>`] に pack した、bit vector です。

mod range;
mod range_mut;

use std::{
    fmt::{Debug, Display},
    ops::{self, Bound, Deref, DerefMut, RangeBounds},
    str::FromStr,
};

pub use range::Range;
pub use range_mut::RangeMut;

const B: usize = u64::BITS as usize;
const C: usize = B.trailing_zeros() as usize;

/// 論理的な [`bool`] 配列 $A$ を、長さ $\lceil \\# A / 64 \rceil$ の [`Vec<u64>`] に pack した、bit vector です。
#[derive(Clone)]
pub struct BitVec {
    items: Vec<u64>,
    len: usize,
}

impl BitVec {
    /// 指定した長さの all-zero ビットベクターを構築します。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv = BitVec::new(3);
    /// assert_eq!(bv.collect_vec()[..], [false; 3][..]);
    /// ```
    pub fn new(len: usize) -> Self {
        Self {
            items: vec![0; len.div_ceil(B)],
            len,
        }
    }

    /// 長さを返します
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv = BitVec::new(3);
    /// assert_eq!(bv.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn extend(&mut self, extra_len: usize) {
        self.resize(self.len() + extra_len);
    }

    pub fn resize(&mut self, new_len: usize) {
        self.items.resize(new_len.div_ceil(B), 0);
        self.len = new_len;
    }

    pub fn pop_front_many(&mut self, count: usize) {
        let (q, r) = div_rem(count);
        self.items.rotate_left(q);
        for _ in 0..q {
            self.items.pop().unwrap();
        }
        if r != 0 {
            for i in 0..self.items.len() {
                if i + 1 < self.items.len() {
                    self.items[i] = self.items[i] >> r | (self.items[i + 1] & ((1 << r) - 1));
                } else {
                    self.items[i] >>= r;
                }
            }
        }
        self.len -= count;
        if self.len + B <= self.items.len() * B {
            self.items.pop().unwrap();
        }
    }

    /// 論理的な [`bool`] 配列 $A$ が空列のとき [`true`] を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// assert!(BitVec::new(0).is_empty());
    /// assert!(!BitVec::new(3).is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Immutable な部分列を取得します。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv: BitVec = "00110101".parse().unwrap();
    /// let range = bv.range(2..6);
    /// assert_eq!(range.collect_vec()[..], [true, true, false, true][..]);
    /// ```
    pub fn range(&self, range: impl RangeBounds<usize>) -> Range<'_> {
        let std::ops::Range { start, end } = to_range(range, self.len);
        assert!(start <= end);
        Range {
            items: &self.items,
            start,
            end,
        }
    }

    /// Mutable な部分列を取得します。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// let mut range = bv.range_mut(2..6);
    ///
    /// let other: BitVec = "11111111111111111".parse().unwrap();
    /// range.xor_assign(other.range(..));
    /// assert_eq!(range.to_string(), "0010");
    /// ```
    pub fn range_mut(&mut self, range: impl RangeBounds<usize>) -> RangeMut<'_> {
        let std::ops::Range { start, end } = to_range(range, self.len);
        assert!(start <= end);
        RangeMut {
            items: &mut self.items,
            start,
            end,
        }
    }

    /// 論理的な [`bool`] 配列 $A$ の要素への mutable 参照を取得する
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// *bv.entry(3) = false;
    /// *bv.entry(7) = false;
    ///
    /// assert_eq!(bv.to_string(), "00100100");
    /// ```
    pub fn entry(&mut self, index: usize) -> Entry<'_> {
        let value = self.get(index);
        Entry {
            bit_vec: self,
            index,
            value,
        }
    }

    /// 論理的な [`bool`] 配列 $A$ のビットを取得する
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv: BitVec = "00110101".parse().unwrap();
    ///
    /// assert!(bv.get(3));
    /// assert!(!bv.get(4));
    /// ```
    pub fn get(&self, index: usize) -> bool {
        assert!(index < self.len);
        let (q, r) = div_rem(index);
        self.items[q] >> r & 1 == 1
    }

    /// Or-Shift Convolution を行います。
    ///
    /// # Specification
    ///
    /// `shift` の要素全体の集合を $S$ として、次の更新を同時に行います。($0$ が追加されていることに注意)
    ///
    /// $$
    /// A _ i ← \bigvee _ { j \\{ 0 \\} \cup S } A _ {i - j}
    /// $$
    ///
    /// # Complexity
    ///
    /// $A, S$ の要素数を $N, K$ として、$O(NK / w)$
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "01000010".parse().unwrap();
    ///
    /// bv.or_shift_convolution_with_zero(&[1, 3]);
    /// assert_eq!(bv.to_string(), "01101011");
    /// ```
    pub fn or_shift_convolution_with_zero(&mut self, shift: &[usize]) {
        for i in (0..self.items.len()).rev() {
            let value = self.items[i];
            for &shift in shift {
                let (q, r) = div_rem(shift);
                if i + q >= self.items.len() {
                    continue;
                }
                self.items[i + q] |= value << r;
                if r != 0 && i + q + 1 < self.items.len() {
                    self.items[i + q + 1] |= value >> (B - r);
                }
            }
        }
        self.clear_extra_zeros();
    }

    /// 論理的な [`bool`] 配列 $A$ の要素を順に返す iterator を構築します。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv: BitVec = "01".parse().unwrap();
    /// let mut iter = bv.iter();
    /// assert_eq!(iter.next(), Some(false));
    /// assert_eq!(iter.next(), Some(true));
    /// assert_eq!(iter.next(), None);
    ///
    /// let bv: BitVec = "01".parse().unwrap();
    /// for b in &bv {
    ///     let _: bool = b;
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            items: &self.items,
            start: 0,
            end: self.len,
        }
    }
    /// [`Vec<bool>`] に変換します。これは `.iter().collect()` の短絡メソッドです。
    ///
    /// # Example
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let bv: BitVec = "01".parse().unwrap();
    /// assert_eq!(bv.collect_vec()[..], [false, true][..]);
    /// ```
    pub fn collect_vec(&self) -> Vec<bool> {
        self.iter().collect()
    }

    fn clear_extra_zeros(&mut self) {
        let (q, r) = div_rem(self.len);
        if r != 0 {
            self.items[q] &= (1 << r) - 1;
        }
    }
}

impl Debug for BitVec {
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

impl Display for BitVec {
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

pub struct PrintDetails<'a>(pub &'a BitVec);
impl Debug for PrintDetails<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BitVec")
            .field("len", &self.0.len)
            .field(
                "items",
                &self
                    .0
                    .items
                    .iter()
                    .map(|&x| {
                        (0..B)
                            .map(|i| if x >> i & 1 == 1 { '1' } else { '0' })
                            .collect::<String>()
                    })
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

pub struct PrintOnes<'a>(pub &'a BitVec);
impl Debug for PrintOnes<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BitVec")
            .field("len", &self.0.len)
            .field(
                "ones",
                &(0..self.0.len)
                    .filter(|&i| self.0.get(i))
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl<'a> IntoIterator for &'a BitVec {
    type Item = bool;

    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromIterator<bool> for BitVec {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut items = vec![];
        let mut len = 0;
        let mut value = 0;
        let mut r = 0;
        for b in iter {
            value |= u64::from(b) << r;
            r += 1;
            len += 1;
            if r == B {
                items.push(value);
                r = 0;
                value = 0;
            }
        }
        if r != 0 {
            items.push(value);
        }
        Self { items, len }
    }
}

impl FromStr for BitVec {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.chars()
            .map(|c| match c {
                '0' => false,
                '1' => true,
                _ => panic!(),
            })
            .collect())
    }
}

/// [`BitVec`] 内の bit の handler 型。 [`BitVec::entry`] で取得できます。
pub struct Entry<'a> {
    bit_vec: &'a mut BitVec,
    index: usize,
    value: bool,
}

impl Deref for Entry<'_> {
    type Target = bool;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl DerefMut for Entry<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl Drop for Entry<'_> {
    fn drop(&mut self) {
        let (q, r) = div_rem(self.index);
        if self.value {
            self.bit_vec.items[q] |= 1 << r;
        } else {
            self.bit_vec.items[q] &= !(1 << r);
        }
    }
}

/// 範囲内の [`bool`] を順に返すイテレータ
pub struct Iter<'a> {
    items: &'a [u64],
    start: usize,
    end: usize,
}
impl Iterator for Iter<'_> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None;
        }
        let (q, r) = div_rem(self.start);
        let value = self.items[q] >> r & 1 == 1;
        self.start += 1;
        Some(value)
    }
}

fn div_rem(index: usize) -> (usize, usize) {
    let q = index >> C;
    let r = index & (B - 1);
    (q, r)
}

trait RangeMask {
    fn range_mask(self) -> u64;
}

fn range_mask<R: RangeMask>(range: R) -> u64 {
    range.range_mask()
}

impl RangeMask for ops::Range<usize> {
    fn range_mask(self) -> u64 {
        (1 << self.end) - (1 << self.start)
    }
}

impl RangeMask for ops::RangeFrom<usize> {
    fn range_mask(self) -> u64 {
        u64::MAX << self.start
    }
}

impl RangeMask for ops::RangeTo<usize> {
    fn range_mask(self) -> u64 {
        (1 << self.end) - 1
    }
}

fn to_range(range: impl RangeBounds<usize>, len: usize) -> std::ops::Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end + 1,
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };
    start..end
}
