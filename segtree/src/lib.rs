#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! セグツリーです。

/// セグツリーの中に入る値です。
pub trait SegValue: Clone + std::fmt::Debug {}

impl<Value: Clone + std::fmt::Debug> SegValue for Value {}

/// セグツリー演算の情報です。
pub trait SegInfo {
    /// セグツリーの中に入る値です。
    type Value: SegValue;

    /// 単位元です。
    fn id() -> Self::Value;

    /// マージ演算です。
    fn op(x: &Self::Value, y: &Self::Value) -> Self::Value;

    /// マージ演算の Assign バージョンです。
    fn op_assign(x: &mut Self::Value, y: &Self::Value) {
        *x = Self::op(x, y);
    }
}

/// ゼロです。
/// [`AddInfo`] で要求されます。
///
/// [`AddInfo`]: struct.AddInfo.html
pub trait Zero {
    /// ゼロを返します。
    fn zero() -> Self;
}
macro_rules! impl_zero {
    ($($ty: ty)+) => { $(impl Zero for $ty { fn zero() -> Self { 0 } })+ };
}
impl_zero! {
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
}
/// 最小値を持つ型です。
/// 最大値セグツリーの [`SegInfo`] である [`MaxInfo`] で要求されます。
///
/// [`SegInfo`]: trait.SegInfo.html
/// [`MinMaxInfo`]: struct.MMaxInfo.html
pub trait MinValue {
    /// 最大値を返します。
    ///
    /// # Example
    ///
    /// ```
    /// assert_eq!(std::u8::MIN, <u8 as segtree::MinValue>::min_value());
    /// ```
    fn min_value() -> Self;
}
macro_rules! impl_min {
    ($($ty: ident)+) => { $(impl MinValue for $ty { fn min_value() -> Self { std::$ty::MIN } })+ };
}
impl_min! {
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
}

/// 最大値を持つ型です。[`MinInfo`] で要求されます。
///
/// [`MinInfo`]: struct.MinInfo.html
pub trait MaxValue {
    /// 最大値を返します。
    ///
    /// # Example
    ///
    /// ```
    /// assert_eq!(std::u8::MAX, <u8 as segtree::MaxValue>::max_value());
    /// ```
    fn max_value() -> Self;
}
macro_rules! impl_max {
    ($($ty: ident)+) => { $(impl MaxValue for $ty { fn max_value() -> Self { std::$ty::MAX } })+ };
}
impl_max! {
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
}

/// 加算セグツリーのための [`SegInfo`] です。
///
/// # Example
///
/// ```
/// use segtree::{Segtree, AddInfo, segtree};
///
/// let seg: Segtree::<AddInfo<u8>> = segtree![4, 6, 3];
///
/// assert_eq!(seg.fold_all(), 13);
/// ```
///
/// [`SegInfo`]: trait.SegInfo.html
///
pub struct AddInfo<Value: SegValue + std::ops::Add> {
    _marker: std::marker::PhantomData<Value>,
}

impl<Value: SegValue + Zero + std::ops::Add<Output = Value> + std::ops::AddAssign> SegInfo
    for AddInfo<Value>
{
    type Value = Value;
    fn id() -> Self::Value {
        Self::Value::zero()
    }
    fn op(x: &Self::Value, y: &Self::Value) -> Self::Value {
        x.clone() + y.clone()
    }
    fn op_assign(x: &mut Self::Value, y: &Self::Value) {
        *x += y.clone()
    }
}
/// `Min` セグツリーのための [`SegInfo`] です。
///
/// # Example
///
/// ```
/// use segtree::{Segtree, MinInfo, segtree};
///
/// let seg: Segtree::<MinInfo<u8>> = segtree![4, 6, 3];
///
/// assert_eq!(seg.fold_all(), 3);
/// ```
///
/// [`SegInfo`]: trait.SegInfo.html
///
pub struct MinInfo<Value: SegValue + MaxValue + std::cmp::Ord> {
    _marker: std::marker::PhantomData<Value>,
}
impl<Value: SegValue + MaxValue + std::cmp::Ord> SegInfo for MinInfo<Value> {
    type Value = Value;
    fn id() -> Self::Value {
        Self::Value::max_value()
    }
    fn op(x: &Self::Value, y: &Self::Value) -> Self::Value {
        x.clone().min(y.clone())
    }
}
/// `Max` セグツリーのための [`SegInfo`] です。
///
/// # Example
///
/// ```
/// use segtree::{Segtree, MaxInfo, segtree};
///
/// let seg: Segtree::<MaxInfo<u8>> = segtree![4, 6, 3];
///
/// assert_eq!(seg.fold_all(), 6);
/// ```
///
/// [`SegInfo`]: trait.SegInfo.html
///
pub struct MaxInfo<Value: SegValue + MinValue + std::cmp::Ord> {
    _marker: std::marker::PhantomData<Value>,
}
impl<Value: SegValue + MinValue + std::cmp::Ord> SegInfo for MaxInfo<Value> {
    type Value = Value;
    fn id() -> Self::Value {
        Self::Value::min_value()
    }
    fn op(x: &Self::Value, y: &Self::Value) -> Self::Value {
        x.clone().max(y.clone())
    }
}

/// 本体です。
#[derive(Clone)]
pub struct Segtree<Info: SegInfo>(Vec<Info::Value>);

impl<Info: SegInfo> Segtree<Info> {
    /// 長さ `len` の配列に対応するセグツリーを作ります。
    /// 内部的には、これの 2 倍の長さの `Vec` が構築されます。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo};
    /// let seg = Segtree::<AddInfo<u8>>::new(3);
    /// ```
    ///
    pub fn new(len: usize) -> Self {
        Self(vec![Info::id(); 2 * len])
    }

    /// 対応する配列が空であることを判定します。
    /// 内部的な配列が空であることと同値です。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo};
    /// let seg = Segtree::<AddInfo<u8>>::new(0);
    /// assert!(seg.is_empty());
    /// ```
    ///
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// 対応する配列の長さを返します。
    /// 内部的長さの半分です。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo};
    /// let seg = Segtree::<AddInfo<u8>>::new(3);
    /// assert_eq!(seg.len(), 3);
    /// ```
    ///
    pub fn len(&self) -> usize {
        self.0.len() / 2
    }

    /// 対応する配列をスライスの参照として返します。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo, segtree};
    /// let seg: Segtree<AddInfo<u8>> = segtree![4, 3, 6];
    /// assert_eq!(seg.as_slice(), [4, 3, 6]);
    /// ```
    ///
    pub fn as_slice(&self) -> &[Info::Value] {
        &self.0[self.len()..self.0.len()]
    }

    /// 対応する配列を走査するイテレータを返します。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo, segtree};
    /// let seg: Segtree<AddInfo<u8>> = segtree![4, 3, 6];
    /// let mut iter = seg.iter();
    /// assert_eq!(*iter.next().unwrap(), 4);
    /// assert_eq!(*iter.next().unwrap(), 3);
    /// assert_eq!(*iter.next().unwrap(), 6);
    /// ```
    ///
    pub fn iter(&self) -> std::slice::Iter<Info::Value> {
        self.0[self.len()..self.0.len()].iter()
    }

    /// 対応する配列を `Vec` にして返します。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo, segtree};
    /// let seg: Segtree<AddInfo<u8>> = segtree![4, 3, 6];
    /// assert_eq!(seg.vec(), vec![4, 3, 6]);
    /// ```
    ///
    pub fn vec(&self) -> Vec<Info::Value> {
        self.0[self.len()..self.0.len()].into()
    }

    /// 添字 `i` の場所の値を `x` にセットします。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo};
    /// let mut seg = Segtree::<AddInfo<u8>>::new(3);
    ///
    /// seg.set(2, 5);
    /// ```
    ///
    pub fn set(&mut self, i: usize, x: Info::Value) {
        let i = i + self.len();
        self.0[i] = x;
        self.rebuild_one_leaf(i);
    }

    /// 添字 i の場所の値を編集します。
    ///
    /// # TODO
    ///
    /// `std::collections::BTreeMap::entry` のようなことをすると良かったりするのでしょうか。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo, segtree};
    /// let mut seg: Segtree::<AddInfo<u8>> = segtree![4, 6, 3];
    ///
    /// seg.modify(1, |x| *x -= 2);
    /// assert_eq!(seg.as_slice(), [4, 4, 3]);
    /// ```
    ///
    pub fn modify(&mut self, i: usize, f: impl Fn(&mut Info::Value)) {
        let i = i + self.len();
        f(&mut self.0[i]);
        self.rebuild_one_leaf(i);
    }

    /// 添字 `l` から `r` までの半開区間で、畳み込みをします。
    ///
    /// # Requirements
    ///
    /// `l <= r && r <= self.len()`
    ///
    /// 違反する場合は、`assert` で落ちるようにしています。
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo, segtree};
    ///
    /// let seg: Segtree<AddInfo<u8>> = segtree![4, 6, 3];
    ///
    /// for i in 0..3 {
    ///     for j in i..3 {
    ///         assert_eq!(seg.fold(i, j), seg[i..j].iter().sum::<u8>());
    ///     }
    /// }
    /// ```
    ///
    pub fn fold(&self, mut l: usize, mut r: usize) -> Info::Value {
        assert!(l <= r && r <= self.len());
        l += self.len();
        r += self.len();
        let mut fl = Info::id();
        let mut fr = Info::id();
        while l < r {
            if l % 2 == 1 {
                Info::op_assign(&mut fl, &self.0[l]);
                l += 1;
            }
            if r % 2 == 1 {
                r -= 1;
                Info::op_assign(&mut fr, &self.0[r]);
            }
            l /= 2;
            r /= 2;
        }
        Info::op(&fl, &fr)
    }

    /// 全区間で畳み込みをします。
    /// 2 冪に広げておらず、また可換性も仮定しておらずですから、対数時間かかります。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo, segtree};
    ///
    /// let seg: Segtree<AddInfo<u8>> = segtree![4, 6, 3];
    ///
    /// assert_eq!(seg.fold_all(), 13);
    /// ```
    ///
    pub fn fold_all(&self) -> Info::Value {
        self.fold(0, self.len())
    }

    fn rebuild_one_leaf(&mut self, mut i: usize) {
        i /= 2;
        while 0 != i {
            self.0[i] = Info::op(&self.0[2 * i], &self.0[2 * i + 1]);
            i /= 2
        }
    }

    fn rebuild(&mut self) {
        for i in (1..self.len()).rev() {
            self.0[i] = Info::op(&self.0[2 * i], &self.0[2 * i + 1]);
        }
    }
}

impl<Info: SegInfo> std::convert::From<Vec<Info::Value>> for Segtree<Info> {
    /// Vec から構築します。
    ///
    /// # Example
    ///
    /// ```
    /// use segtree::{Segtree, AddInfo};
    /// let mut seg = Segtree::<AddInfo<u8>>::from(vec![3, 4, 6]);
    ///
    /// assert_eq!(seg.as_slice(), [3, 4, 6]);
    /// ```
    ///
    fn from(vec: Vec<Info::Value>) -> Self {
        let mut vec1 = Vec::with_capacity(vec.len() * 2);
        vec1.resize(vec.len(), Info::id());
        vec1.extend(vec);
        let mut seg = Self(vec1);
        seg.rebuild();
        seg
    }
}

impl<Info: SegInfo, I: std::slice::SliceIndex<[Info::Value]>> std::ops::Index<I> for Segtree<Info> {
    type Output = I::Output;

    /// 対応する配列の要素にアクセスです。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::{segtree, Segtree, AddInfo};
    ///
    /// let seg: Segtree<AddInfo<u8>> = segtree![4, 6, 3];
    /// assert_eq!(seg[1], 6);
    ///
    /// let seg: Segtree<AddInfo<u8>> = segtree![4, 6, 3];
    /// assert_eq!(seg[1..=2], [6, 3]);
    /// ```
    ///
    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        std::ops::Index::index(self.as_slice(), index)
    }
}

impl<Info: SegInfo> std::fmt::Debug for Segtree<Info> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.as_slice()).finish()
    }
}

/// `vec!` マクロと `Segtree::from` を合成です。
///
/// # Examples
///
/// ```
/// use segtree::{segtree, Segtree, AddInfo};
///
/// let seg: Segtree<AddInfo<u8>> = segtree![4; 10];
/// assert_eq!(seg.vec(), vec![4; 10]);
///
/// let seg: Segtree<AddInfo<u8>> = segtree![4, 6, 3];
/// assert_eq!(seg.vec(), vec![4, 6, 3]);
/// ```
///
#[macro_export]
macro_rules! segtree {
    ($($elem:expr),*$(,)?) => {
        Segtree::from(vec![$($elem),*])
    };
    ($elem:expr; $n:expr) => {
        Segtree::from(vec![$elem; $n])
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_range_minimum_queries_sample_1() {
        let n = 3;
        let queries = vec![(0, 0, 1), (0, 1, 2), (0, 2, 3), (1, 0, 2), (1, 1, 2)];
        let mut ans = vec![];

        let mut seg: Segtree<MinInfo<u32>> = segtree![0; n];
        for (c, x, y) in queries {
            match c {
                0 => {
                    let (i, x) = (x as usize, y);
                    seg.set(i, x);
                }
                1 => {
                    let (l, r) = (x as usize, y as usize + 1);
                    ans.push(seg.fold(l, r));
                }
                _ => panic!(),
            }
        }

        let expected = vec![1, 2];
        assert_eq!(ans, expected);
    }

    #[test]
    fn test_range_sum_queries_sample_1() {
        let n = 3;
        let queries = vec![(0, 1, 1), (0, 2, 2), (0, 3, 3), (1, 1, 2), (1, 2, 2)];
        let mut ans = vec![];

        let mut seg: Segtree<AddInfo<u32>> = segtree![0; n];
        for (c, x, y) in queries {
            match c {
                0 => {
                    let (i, x) = (x as usize - 1, y);
                    seg.modify(i, |y| *y += x);
                }
                1 => {
                    let (l, r) = (x as usize - 1, y as usize);
                    ans.push(seg.fold(l, r));
                }
                _ => panic!(),
            }
        }

        let expected = vec![3, 2];
        assert_eq!(ans, expected);
    }
}
