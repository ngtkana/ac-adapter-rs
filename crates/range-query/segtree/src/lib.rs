//! セグメント木です。
//!
//! # 愉快な仲間たち
//!
//! - [`Segtree`] : 本体
//! - [`Ops`] : 演算
//!
//!
//! # Examples
//!
//! ```
//! use segtree::{Segtree, Ops};
//!
//! // 演算の実装
//! enum O {}
//! impl Ops for O {
//!     type Value = i32;
//!     fn op(x: &i32, y: &i32) -> i32 {
//!         x + y
//!     }
//!     fn identity() -> i32 {
//!         0
//!     }
//! }
//!
//! // 本体の使い方
//! let mut seg = Segtree::<O>::new(vec![0; 5]);
//! assert_eq!(&[0, 0, 0, 0, 0], seg.as_ref());
//! *seg.entry(1) = 2;
//! *seg.entry(3) = 5;
//! assert_eq!(&[0, 2, 0, 5, 0], seg.as_ref());
//! assert_eq!(seg.fold(..), 7);
//! ```
//!
use std::{
    collections::VecDeque,
    fmt::Debug,
    iter::{repeat_with, FromIterator},
    ops::{Bound, Deref, DerefMut, Index, Range, RangeBounds},
    slice::SliceIndex,
};

////////////////////////////////////////////////////////////////////////////////
// 演算
////////////////////////////////////////////////////////////////////////////////
pub trait Ops {
    type Value: Debug + Default;
    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
    fn identity() -> Self::Value;
}

////////////////////////////////////////////////////////////////////////////////
// 本体
////////////////////////////////////////////////////////////////////////////////
/// セグツリー
///
/// # 構築
///
/// - メソッド :
///     - [`new()`](Self::new) : [`ExactSizeIterator`] に [`IntoIterator`] できるものから構築します。
/// - トレイト :
///     - [`impl From<Vec>>`](struct.Segtree.html#impl-From<Vec<<O%20as%20Ops>%3A%3AValue%2C%20Global>>)
///     - [`impl FromIterator`](struct.Segtree.html#impl-FromIterator<<O%20as%20Ops>%3A%3AValue>)
///
/// # 値の取得・更新
///
/// - メソッド :
///     - [`entry()`](Self::entry) : [`Entry`]
///     を返します。これは値の取得と更新のできるライフタイム付きハンドラです。
/// - トレイト :
///     - [`impl Index`](struct.Segtree.html#impl-Index<Idx>)
///
/// # 畳み込み
///
/// - [`fold()`](Self::fold) : 畳み込みができます。
///
///
/// # スライスへの変換
///
/// - メソッド :
///     - [`as_slice()`](Self::as_slice) : 不変版
///     - [`as_slice_mut()`](Self::as_slice_mut) : 可変版
///
/// - トレイト :
///     - [`impl AsRef`](struct.Segtree.html#impl-AsRef<%5B<O%20as%20Ops>%3A%3AValue%5D>) : 不変版
///     - [`impl AsMut`](struct.Segtree.html#impl-AsMut<%5B<O%20as%20Ops>%3A%3AValue%5D>) : 可変版
///
///
/// # 各メソッドのドキュメントのサンプルコードの先頭にはこれが隠れています。
///
/// ```
/// use segtree::Ops;
/// enum O {}
/// impl Ops for O {
///     type Value = i32;
///     fn op(x: &i32, y: &i32) -> i32 {
///         x + y
///     }
///     fn identity() -> i32 {
///         0
///     }
/// }
/// ```
pub struct Segtree<O: Ops> {
    table: Box<[O::Value]>,
}
impl<O: Ops> Segtree<O> {
    /// [`IntoIterator`] により [`ExactSizeIterator`] にできるもの（例えば [`Vec`]）から [`Segtree`] を構築します。
    ///
    /// ```
    /// # use segtree::Ops;
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = i32;
    /// #     fn op(x: &i32, y: &i32) -> i32 {
    /// #         x + y
    /// #     }
    /// #     fn identity() -> i32 {
    /// #         0
    /// #     }
    /// # }
    /// use segtree::Segtree;
    ///
    /// let seg = Segtree::<O>::new(vec![0, 1, 2]);
    /// assert_eq!(seg.as_ref(), &[0, 1, 2]);
    /// ```
    pub fn new<I: ExactSizeIterator<Item = O::Value>, T: IntoIterator<IntoIter = I>>(
        iter: T,
    ) -> Self {
        let iter = iter.into_iter();
        let n = iter.len();
        let mut table = repeat_with(O::Value::default).take(n).collect::<Vec<_>>();
        table.extend(iter);
        (1..n)
            .rev()
            .for_each(|i| table[i] = O::op(&table[2 * i], &table[2 * i + 1]));
        let table = table.into_boxed_slice();
        Segtree { table }
    }
    /// 表している配列が空であるときに `true` です。
    ///
    /// ```
    /// # use segtree::Ops;
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = i32;
    /// #     fn op(x: &i32, y: &i32) -> i32 {
    /// #         x + y
    /// #     }
    /// #     fn identity() -> i32 {
    /// #         0
    /// #     }
    /// # }
    /// use segtree::Segtree;
    ///
    /// let seg = Segtree::<O>::new(vec![0, 1, 2]);
    /// assert_eq!(seg.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }
    /// 表している配列を返します。
    ///
    /// ```
    /// # use segtree::Ops;
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = i32;
    /// #     fn op(x: &i32, y: &i32) -> i32 {
    /// #         x + y
    /// #     }
    /// #     fn identity() -> i32 {
    /// #         0
    /// #     }
    /// # }
    /// use segtree::Segtree;
    ///
    /// let seg = Segtree::<O>::new(vec![0, 1, 2]);
    /// assert_eq!(seg.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.table.len() / 2
    }
    /// 与えられた範囲で畳み込みます。
    ///
    /// # Panics
    ///
    /// 標準ライブラリの [`SliceIndex`] と同じ条件でパニックします。
    ///
    /// # Output
    ///
    /// `range = [l, r[` のとき、`op(a[l], ..., a[r - 1])` を返します。ただし空のときには
    /// `identity()` を返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use segtree::Ops;
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = i32;
    /// #     fn op(x: &i32, y: &i32) -> i32 {
    /// #         x + y
    /// #     }
    /// #     fn identity() -> i32 {
    /// #         0
    /// #     }
    /// # }
    /// use segtree::Segtree;
    ///
    /// let seg = Segtree::<O>::new(vec![0, 1, 2]);
    /// assert_eq!(seg.fold(1..3), 3);
    /// ```
    pub fn fold(&self, range: impl RangeBounds<usize>) -> O::Value {
        let mut left = O::identity();
        let mut right = O::identity();
        let Range { mut start, mut end } = into_slice_range(self.len(), range);
        if end < start {
            segtree_index_order_fail(start, end);
        }
        if self.len() < end {
            segtree_end_index_len_fail(end, self.len());
        }
        start += self.len();
        end += self.len();
        while start != end {
            if start % 2 == 1 {
                left = O::op(&left, &self.table[start]);
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                right = O::op(&self.table[end], &right);
            }
            start /= 2;
            end /= 2;
        }
        O::op(&left, &right)
    }
    /// 要素の可変ハンドラを返します。
    ///
    /// # Panics
    ///
    /// [`Deref`] か [`Drop`] するまではパニックしません。
    /// [`Deref`] か [`Drop`] でパニックする条件は [`SliceIndex`] と同じです。
    ///
    /// # Output
    ///
    /// `range = [l, r[` のとき、`op(a[l], ..., a[r - 1])` を返します。ただし空のときには
    /// `identity()` を返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use segtree::Ops;
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = i32;
    /// #     fn op(x: &i32, y: &i32) -> i32 {
    /// #         x + y
    /// #     }
    /// #     fn identity() -> i32 {
    /// #         0
    /// #     }
    /// # }
    /// use segtree::Segtree;
    ///
    /// let mut seg = Segtree::<O>::new(vec![0, 1, 2]);
    /// *seg.entry(0) = 10;
    /// assert_eq!(seg.fold(..), 13);
    /// ```
    pub fn entry(&mut self, idx: usize) -> Entry<'_, O> {
        Entry { idx, seg: self }
    }
    /// 表している配列をスライスで返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use segtree::Ops;
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = i32;
    /// #     fn op(x: &i32, y: &i32) -> i32 {
    /// #         x + y
    /// #     }
    /// #     fn identity() -> i32 {
    /// #         0
    /// #     }
    /// # }
    /// use segtree::Segtree;
    ///
    /// let seg = Segtree::<O>::new(vec![0, 1, 2]);
    /// assert_eq!(seg.as_slice(), &[0, 1, 2]);
    /// ```
    pub fn as_slice(&self) -> &[O::Value] {
        self.as_ref()
    }
    /// 表している配列を可変スライスで返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use segtree::Ops;
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = i32;
    /// #     fn op(x: &i32, y: &i32) -> i32 {
    /// #         x + y
    /// #     }
    /// #     fn identity() -> i32 {
    /// #         0
    /// #     }
    /// # }
    /// use segtree::Segtree;
    ///
    /// let mut seg = Segtree::<O>::new(vec![0, 1, 2]);
    /// assert_eq!(seg.as_slice_mut(), &mut [0, 1, 2]);
    /// ```
    pub fn as_slice_mut(&mut self) -> &mut [O::Value] {
        self.as_mut()
    }
}
////////////////////////////////////////////////////////////////////////////////
// 要素アクセス
////////////////////////////////////////////////////////////////////////////////
impl<O: Ops, Idx: SliceIndex<[O::Value], Output = O::Value>> Index<Idx> for Segtree<O> {
    type Output = O::Value;
    fn index(&self, index: Idx) -> &Self::Output {
        &self.as_slice()[index]
    }
}
pub struct Entry<'a, O: Ops> {
    idx: usize,
    seg: &'a mut Segtree<O>,
}
impl<'a, O: Ops> Drop for Entry<'a, O> {
    fn drop(&mut self) {
        self.idx += self.seg.len();
        self.idx /= 2;
        while self.idx != 0 {
            self.seg.table[self.idx] = O::op(
                &self.seg.table[2 * self.idx],
                &self.seg.table[2 * self.idx + 1],
            );
            self.idx /= 2;
        }
    }
}
impl<O: Ops> Deref for Entry<'_, O> {
    type Target = O::Value;
    fn deref(&self) -> &Self::Target {
        &self.seg.as_slice()[self.idx]
    }
}
impl<O: Ops> DerefMut for Entry<'_, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.seg.as_slice_mut()[self.idx]
    }
}

////////////////////////////////////////////////////////////////////////////////
// 変換
////////////////////////////////////////////////////////////////////////////////
impl<O: Ops> From<Vec<O::Value>> for Segtree<O> {
    fn from(v: Vec<O::Value>) -> Self {
        Self::new(v)
    }
}
impl<O: Ops> FromIterator<O::Value> for Segtree<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut v = iter.into_iter().collect::<VecDeque<_>>();
        let n = v.len();
        let mut table = repeat_with(O::Value::default)
            .take(n)
            .collect::<VecDeque<_>>();
        table.append(&mut v);
        (1..n)
            .rev()
            .for_each(|i| table[i] = O::op(&table[2 * i], &table[2 * i + 1]));
        let table = Vec::from(table).into_boxed_slice();
        Segtree { table }
    }
}
impl<O: Ops> AsRef<[O::Value]> for Segtree<O> {
    fn as_ref(&self) -> &[O::Value] {
        &self.table[self.len()..]
    }
}
impl<O: Ops> AsMut<[O::Value]> for Segtree<O> {
    fn as_mut(&mut self) -> &mut [O::Value] {
        let n = self.len();
        &mut self.table[n..]
    }
}

////////////////////////////////////////////////////////////////////////////////
// フォーマット
////////////////////////////////////////////////////////////////////////////////
impl<O: Ops> Debug for Segtree<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(f)
    }
}

////////////////////////////////////////////////////////////////////////////////
// プライベート - RangeBounds 関連
////////////////////////////////////////////////////////////////////////////////
fn into_slice_range(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start
            .checked_add(1)
            .unwrap_or_else(|| slice_start_index_overflow_fail()),
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end
            .checked_add(1)
            .unwrap_or_else(|| slice_end_index_overflow_fail()),
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };
    start..end
}
fn segtree_end_index_len_fail(index: usize, len: usize) -> ! {
    panic!(
        "range end index {} out of range for segtree of length {}",
        index, len
    );
}
fn segtree_index_order_fail(index: usize, end: usize) -> ! {
    panic!("segtree index starts at {} but ends at {}", index, end);
}
fn slice_start_index_overflow_fail() -> ! {
    panic!("attempted to index slice from after maximum usize");
}
fn slice_end_index_overflow_fail() -> ! {
    panic!("attempted to index slice up to maximum usize");
}

////////////////////////////////////////////////////////////////////////////////
// テスト
////////////////////////////////////////////////////////////////////////////////
#[cfg(test)]
mod tests {
    use std::ops::Bound;

    use {
        super::{Ops, Segtree},
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::{iter::once, mem::swap},
    };

    #[test]
    fn test_fold() {
        enum O {}
        impl Ops for O {
            type Value = i32;
            fn op(lhs: &i32, rhs: &i32) -> i32 {
                lhs + rhs
            }
            fn identity() -> i32 {
                0
            }
        }
        let a = vec![1, 2, 4, 8, 16];
        let seg = Segtree::<O>::new(a.clone());
        let n = a.len();
        (0..=n)
            .cartesian_product(0..=n)
            .flat_map(|(l, r)| {
                let mut v = Vec::new();
                if l <= r {
                    v.push((seg.fold(l..r), &a[l..r]));
                }
                if l <= r && r < n {
                    v.push((seg.fold(l..=r), &a[l..=r]));
                }
                if l != 0 && l < r {
                    let range = (Bound::Excluded(l), Bound::Excluded(r));
                    v.push((seg.fold(range), &a[range]));
                }
                if l != 0 && l <= r && r < n {
                    let range = (Bound::Excluded(l), Bound::Included(r));
                    v.push((seg.fold(range), &a[range]));
                }
                v
            })
            .chain((0..=n).flat_map(|i| {
                let mut v = Vec::new();
                v.push((seg.fold(i..), &a[i..]));
                v.push((seg.fold(..i), &a[..i]));
                if i != n {
                    v.push((seg.fold(..=i), &a[..=i]));
                }
                if i != 0 && i != n {
                    let range = (Bound::Excluded(i), Bound::Unbounded);
                    v.push((seg.fold(range), &a[range]));
                }
                v
            }))
            .chain(once((seg.fold(..), a.as_ref())))
            .for_each(|(result, expected)| {
                let expected = expected.iter().fold(O::identity(), |acc, x| O::op(&acc, x));
                assert_eq!(result, expected);
            });
    }

    #[test]
    fn test_cat() {
        enum O {}
        impl Ops for O {
            type Value = String;
            fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                lhs.chars().chain(rhs.chars()).collect()
            }
            fn identity() -> Self::Value {
                String::new()
            }
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=10);
            let mut a = ('a'..).take(n).map(|c| c.to_string()).collect::<Vec<_>>();
            let mut seg = Segtree::<O>::new(a.iter().cloned());
            for _ in 0..2 * n {
                match rng.gen_range(0..2) {
                    0 => {
                        let i = rng.gen_range(0..n);
                        let x = rng.gen_range('a'..='z').to_string();
                        a[i] = x.clone();
                        *seg.entry(i) = x;
                    }
                    1 => {
                        let mut l = rng.gen_range(0..n);
                        let mut r = rng.gen_range(0..n + 1);
                        if r <= l {
                            swap(&mut l, &mut r);
                            r += 1;
                        }
                        let expected = a[l..r].iter().fold(O::identity(), |acc, x| O::op(&acc, x));
                        let result = seg.fold(l..r);
                        assert_eq!(expected, result);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
