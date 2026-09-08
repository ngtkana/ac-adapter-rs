//! 論理配列 $A \in \{0, 1\}^n$ を64ビット単位でpackして保持するbit vector。
//!
//! `Vec<u64>` にビットを詰めることで、範囲へのOR/XOR/popcountなどの操作をword単位（64ビットずつ）に
//! まとめて処理でき、素朴な `Vec<bool>` より高速に扱える。範囲アクセスは [`Range`] / [`RangeMut`] が
//! word境界をまたぐケースをマスク処理で吸収して提供する。
//!
//! # 仕様
//!
//! - 構築: [`BitVec::new`]（全要素 `false`）、`"01"` からなる文字列の `FromStr`
//! - アクセス: [`BitVec::get`], [`BitVec::entry`]（mutable参照）, [`BitVec::iter`]
//! - 部分列: [`BitVec::range`] → [`Range`]、[`BitVec::range_mut`] → [`RangeMut`]
//! - 集合演算: [`BitVec::or_shift_convolution_with_zero`]
//!
//! # 例
//!
//! ```
//! use bit_vec::BitVec;
//!
//! let mut bv: BitVec = "00110101".parse().unwrap();
//! assert_eq!(bv.range(2..6).count_ones(), 3);
//! bv.range_mut(0..4).flip();
//! assert_eq!(bv.to_string(), "11000101");
//! ```
//!
//! # 計算量
//!
//! $n$: 要素数、$w = 64$ をword幅とする。
//!
//! - [`BitVec::get`], [`BitVec::entry`], [`BitVec::range`], [`BitVec::range_mut`][]: $O(1)$
//! - [`Range::count_ones`], [`Range::first_one`], [`RangeMut::flip`] などの範囲操作: $O(n / w)$
//! - [`BitVec::or_shift_convolution_with_zero`]（shift数 $K$）: $O(nK / w)$

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

/// 論理配列 $A \in \{0, 1\}^n$ を64ビット単位でpackして保持するbit vector。
#[derive(Clone)]
pub struct BitVec {
    items: Vec<u64>,
    len: usize,
}

impl BitVec {
    /// 長さ $n$、全要素 `false` のbit vectorを構築する。
    ///
    /// # 例
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

    /// 長さ $n$ を返す。
    ///
    /// # 例
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

    /// 末尾に `false` を `extra_len` 個追加し、長さを伸ばす。
    ///
    /// # 例
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv = BitVec::new(2);
    /// bv.extend(2);
    /// assert_eq!(bv.len(), 4);
    /// ```
    pub fn extend(&mut self, extra_len: usize) {
        self.resize(self.len() + extra_len);
    }

    /// 長さを `new_len` に変更する。伸びた分は `false` で埋め、縮む場合は末尾を切り捨てる。
    ///
    /// # 例
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "1111".parse().unwrap();
    /// bv.resize(2);
    /// assert_eq!(bv.to_string(), "11");
    /// ```
    pub fn resize(&mut self, new_len: usize) {
        self.items.resize(new_len.div_ceil(B), 0);
        self.len = new_len;
    }

    /// 先頭 `count` 要素を取り除き、残りを前に詰める。
    ///
    /// # 例
    ///
    /// ```
    /// use bit_vec::BitVec;
    ///
    /// let mut bv: BitVec = "00110101".parse().unwrap();
    /// bv.pop_front_many(3);
    /// assert_eq!(bv.to_string(), "10101");
    /// ```
    pub fn pop_front_many(&mut self, count: usize) {
        let (q, r) = div_rem(count);
        self.items.rotate_left(q);
        for _ in 0..q {
            self.items.pop().unwrap();
        }
        if r != 0 {
            for i in 0..self.items.len() {
                if i + 1 < self.items.len() {
                    self.items[i] = self.items[i] >> r | (self.items[i + 1] << (B - r));
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

    /// 長さ $n = 0$ のとき `true` を返す。
    ///
    /// # 例
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

    /// 区間 `range` のimmutableな部分列 [`Range`] を取得する。
    ///
    /// # 例
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

    /// 区間 `range` のmutableな部分列 [`RangeMut`] を取得する。
    ///
    /// # 例
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

    /// $A_i$ への mutable な参照を [`Entry`] として取得する。`Drop` 時に書き戻される。
    ///
    /// # 例
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

    /// $A_i$（`index` 番目のビット）を返す。
    ///
    /// # 例
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

    /// `shift` の要素集合を $S$ として、$A_i \gets \bigvee_{j \in \{0\} \cup S} A_{i - j}$ を同時に行う（OR-shift畳み込み）。
    ///
    /// # 計算量
    ///
    /// $n$: 要素数、$K$: `shift.len()` として $O(nK / w)$（$w = 64$）
    ///
    /// # 例
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

    /// $A_0, \ldots, A_{n-1}$ を順に返すイテレータを構築する。
    ///
    /// # 例
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
    /// `Vec<bool>` に変換する。`.iter().collect()` の短絡メソッド。
    ///
    /// # 例
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

/// `{:?}` で内部の各wordをビット列として表示するデバッグ用ラッパー。
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

/// `{:?}` で $1$ が立っているインデックス一覧を表示するデバッグ用ラッパー。
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

/// `'0'`/`'1'` からなる文字列をパースする。それ以外の文字が含まれるとpanicする。
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

/// [`BitVec`] 内のビットへのmutableな参照。`Drop` 時に元のビットへ書き戻す。[`BitVec::entry`] で取得する。
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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};

    #[test]
    fn test_pop_front_many_random() {
        let mut rng = StdRng::seed_from_u64(1);
        for _ in 0..2000 {
            let len = rng.gen_range(1..400);
            let count = rng.gen_range(0..=len);
            let bits: Vec<bool> = (0..len).map(|_| rng.gen_bool(0.5)).collect();
            let mut bv: BitVec = bits.iter().copied().collect();
            bv.pop_front_many(count);
            let expected = &bits[count..];
            let actual = bv.collect_vec();
            assert_eq!(actual, expected, "len={len} count={count}");
        }
    }

    #[test]
    fn test_or_shift_convolution_with_zero_random() {
        let mut rng = StdRng::seed_from_u64(2);
        for _ in 0..2000 {
            let len = rng.gen_range(1..300);
            let k = rng.gen_range(0..5);
            let shift: Vec<usize> = (0..k).map(|_| rng.gen_range(0..len)).collect();
            let bits: Vec<bool> = (0..len).map(|_| rng.gen_bool(0.5)).collect();
            let mut bv: BitVec = bits.iter().copied().collect();
            bv.or_shift_convolution_with_zero(&shift);

            let mut expected = bits.clone();
            for i in 0..len {
                if bits[i] {
                    for &s in shift.iter().chain(std::iter::once(&0)) {
                        if i + s < len {
                            expected[i + s] = true;
                        }
                    }
                }
            }
            let actual = bv.collect_vec();
            assert_eq!(actual, expected, "len={len} shift={shift:?}");
        }
    }

    #[test]
    fn test_range_count_ones_and_first_one_random() {
        let mut rng = StdRng::seed_from_u64(3);
        for _ in 0..2000 {
            let len = rng.gen_range(1..600);
            let start = rng.gen_range(0..=len);
            let end = rng.gen_range(start..=len);
            let bits: Vec<bool> = (0..len).map(|_| rng.gen_bool(0.5)).collect();
            let bv: BitVec = bits.iter().copied().collect();
            let range = bv.range(start..end);
            let expected_count = bits[start..end].iter().filter(|&&b| b).count();
            assert_eq!(
                range.count_ones(),
                expected_count,
                "len={len} start={start} end={end}"
            );
            let expected_first = bits[start..end].iter().position(|&b| b).map(|p| p + start);
            assert_eq!(
                range.first_one(),
                expected_first,
                "len={len} start={start} end={end}"
            );
        }
    }
}
