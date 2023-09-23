//! [`Box`] で実装された、ポインタベースのセグツリーです。
//!
//! # 使い方
//!
//! [`Ops`] トレイトを実装した型を用意して、第二型引数に入れます。
//! 次のコードは、[`u32`] 型の加法による例です。
//!
//! ```
//! use box_segtree::{Segtree, Ops};
//! enum O {}
//! impl Ops for O {
//!     type Value = u32;
//!     fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
//!         lhs + rhs
//!     }
//!     fn id() -> Self::Value {
//!         0
//!     }
//!     // init(len) = id() がデフォルト実装です。
//!     fn init(_len: usize) -> Self::Value {
//!         0
//!     }
//! }
//! ```
//!
//! 型定義が済んだら構築です！
//!
//! ```
//! # use box_segtree::{Segtree, Ops};
//! # enum O {}
//! # impl Ops for O {
//! #     type Value = u32;
//! #     fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
//! #         lhs + rhs
//! #     }
//! #     fn id() -> Self::Value {
//! #         0
//! #     }
//! # }
//! // 構築
//! let mut seg = Segtree::<_, O>::new(10);
//!
//! // 一点編集
//! seg.set(3, 10);
//! seg.set(7, 20);
//! seg.modify(3, |x| *x *= 3);
//!
//! // 区間演算
//! assert_eq!(seg.fold(..), 50);
//! ```
//!
//!
//! # [`Ops`] の要件
//!
//! * `op` が結合的
//! * `id` がその単位元
//!

use std::{
    fmt::{Debug, DebugList, DebugMap, Formatter, Result},
    iter::repeat_with,
    marker::PhantomData,
    ops::{Bound, Range, RangeBounds},
};

/// セグツリーです。
///
/// [大まかな使い方はモジュールレベルドキュメントをご覧ください。](self)
#[derive(Clone, Default, Hash, PartialEq)]
pub struct Segtree<T, O> {
    seg: Option<Box<Nonempty<T, O>>>,
    len: usize,
}
impl<T: Clone, O: Ops<Value = T>> Segtree<T, O> {
    /// 新しいセグツリーを構築します。
    pub fn new(len: usize) -> Self {
        Self {
            seg: if len == 0 {
                None
            } else {
                Some(Box::new(__internal_new(len.next_power_of_two())))
            },
            len,
        }
    }
    /// [`Self::modify`] を呼んで第 `i` 項に `x` を代入します。
    pub fn set(&mut self, i: usize, x: T) {
        self.modify(i, move |y| *y = x);
    }
    /// 第 `i` 項を `f` で編集し、それに従ってその祖先の `value` を再計算します。
    pub fn modify(&mut self, i: usize, f: impl FnOnce(&mut T)) {
        assert!(i < self.len, "範囲外です。 i = {}, len = {}", i, self.len);
        __internal_modify_recurse(self.seg.as_mut().unwrap(), i, f);
    }
    /// `range` の範囲の `value` を、[`Ops::op`] で畳み込みます。
    ///
    /// # Examples
    ///
    /// ```
    /// # use box_segtree::{Segtree, Ops};
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = u32;
    /// #     fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
    /// #         lhs + rhs
    /// #     }
    /// #     fn id() -> Self::Value {
    /// #         0
    /// #     }
    /// # }
    /// let mut seg = Segtree::<_, O>::new(7); // 演算は `u32` の加法
    /// seg.set(3, 10);
    /// seg.set(5, 20);
    /// assert_eq!(seg.fold(..), 30);
    /// ```
    pub fn fold(&self, range: impl RangeBounds<usize>) -> T {
        let Range { start, end } = __internal_open(range, self.len);
        assert!(
            start <= end && end <= self.len,
            "範囲外です。 range = {:?}, len = {}",
            &(start..end),
            self.len
        );
        __internal_fold_recurse(&self.seg, start, end)
    }
    pub fn iter(&self) -> Iter<'_, T, O> {
        Iter(match &self.seg {
            None => Vec::new(),
            Some(seg) => vec![(0, seg)],
        })
    }
    /// [`self`] を型に包んで [`Debug`] トレイトを上書きし、存在しないノードも [`Ops::id`]
    /// で埋めた感じのリスト形式で出力するようにします。
    ///
    /// ちなみにこれを使わずにそのまま出力するとマップ形式になります。
    ///
    /// # Examples
    ///
    /// ```
    /// # use box_segtree::{Segtree, Ops};
    /// # enum O {}
    /// # impl Ops for O {
    /// #     type Value = u32;
    /// #     fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
    /// #         lhs + rhs
    /// #     }
    /// #     fn id() -> Self::Value {
    /// #         0
    /// #     }
    /// # }
    /// let mut seg = Segtree::<_, O>::new(7); // 演算は `u32` の加法
    /// seg.set(3, 10);
    /// seg.set(5, 20);
    /// assert_eq!(
    ///     format!("{:?}", seg.debug_list()),
    ///     "[0, 0, 0, 10, 0, 20, 0]".to_string(),
    /// );
    /// ```
    pub fn debug_list(&self) -> SegtreeDebugList<'_, T, O> {
        SegtreeDebugList(self)
    }
}

#[derive(Clone, Default, Hash, PartialEq)]
struct Nonempty<T, O> {
    len: usize,
    value: T,
    child: [Option<Box<Self>>; 2],
    __marker: PhantomData<fn(O) -> O>,
}
fn __internal_new<T: Clone, O: Ops<Value = T>>(len: usize) -> Nonempty<T, O> {
    assert!(len.is_power_of_two());
    Nonempty {
        len,
        value: O::init(len),
        child: [None, None],
        __marker: PhantomData,
    }
}
fn __internal_fold_recurse<T: Clone, O: Ops<Value = T>>(
    seg: &Option<Box<Nonempty<T, O>>>,
    l: usize,
    r: usize,
) -> T {
    match seg {
        None => O::init(r - l),
        Some(seg) => {
            let len = seg.len;
            let half = len / 2;
            if [l, r] == [0, len] {
                seg.value.clone()
            } else if l == r {
                O::id()
            } else if r <= half {
                __internal_fold_recurse(&seg.child[0], l, r)
            } else if half <= l {
                __internal_fold_recurse(&seg.child[1], l - half, r - half)
            } else {
                O::op(
                    &__internal_fold_recurse(&seg.child[0], l, half),
                    &__internal_fold_recurse(&seg.child[1], 0, r - half),
                )
            }
        }
    }
}
fn __internal_modify_recurse<T: Clone, O: Ops<Value = T>>(
    seg: &mut Nonempty<T, O>,
    i: usize,
    f: impl FnOnce(&mut O::Value),
) {
    let len = seg.len;
    debug_assert!(i < len);
    if len == 1 {
        f(&mut seg.value);
    } else {
        let (e, i) = if len / 2 <= i {
            (1, i - len / 2)
        } else {
            (0, i)
        };
        __internal_modify_recurse(
            seg.child[e].get_or_insert_with(|| Box::new(__internal_new(len / 2))),
            i,
            f,
        );
        __internal_update(seg);
    }
}
fn __internal_update<T: Clone, O: Ops<Value = T>>(seg: &mut Nonempty<T, O>) {
    seg.value = O::op(
        &seg.child[0]
            .as_ref()
            .map_or_else(|| O::init(seg.len / 2), |c| c.value.clone()),
        &seg.child[1]
            .as_ref()
            .map_or_else(|| O::init(seg.len / 2), |c| c.value.clone()),
    );
}

impl<T: Clone + Debug, O: Ops<Value = T>> Debug for Segtree<T, O> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut map = f.debug_map();
        if let Some(seg) = self.seg.as_ref() {
            __internal_debug_map_recurse(seg, &mut map, 0);
        }
        map.finish()
    }
}
fn __internal_debug_map_recurse<T: Clone + Debug, O: Ops<Value = T>>(
    seg: &Nonempty<T, O>,
    map: &mut DebugMap<'_, '_>,
    offset: usize,
) {
    if seg.len == 1 {
        map.entry(&offset, &seg.value);
    } else {
        for e in 0..2 {
            if let Some(c) = seg.child[e].as_ref() {
                __internal_debug_map_recurse(c, map, offset + seg.len / 2 * e);
            }
        }
    }
}

/// [`Segtree::debug_list`] の生成物です。[`Segtree::debug_list` のドキュメントをご覧ください。](`Segtree::debug_list`)
#[derive(Clone, Hash, PartialEq, Copy)]
pub struct SegtreeDebugList<'a, T, O>(&'a Segtree<T, O>);
impl<'a, T: Clone + Debug, O: Ops<Value = T>> Debug for SegtreeDebugList<'a, T, O> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut list = f.debug_list();
        let mut rest = self.0.len;
        if let Some(seg) = self.0.seg.as_ref() {
            __internal_debug_list_recurse(seg, &mut list, &mut rest);
        }
        list.finish()
    }
}
fn __internal_debug_list_recurse<T: Clone + Debug, O: Ops<Value = T>>(
    seg: &Nonempty<T, O>,
    list: &mut DebugList<'_, '_>,
    rest: &mut usize,
) {
    if seg.len == 1 {
        list.entry(&seg.value);
        *rest -= 1;
    } else {
        for e in 0..2 {
            if let Some(c) = seg.child[e].as_ref() {
                __internal_debug_list_recurse(c, list, rest);
            } else {
                let take = (seg.len / 2).min(*rest);
                list.entries(repeat_with(O::id).take(seg.len).take(take));
                *rest -= take;
            }
        }
    }
}

/// [`Segtree::iter`] の返す型です。
#[derive(Clone, Hash, PartialEq)]
pub struct Iter<'a, T: Clone, O: Ops<Value = T>>(Vec<(usize, &'a Nonempty<T, O>)>);
impl<'a, T: Clone, O: Ops<Value = T>> Iterator for Iter<'a, T, O> {
    type Item = (usize, &'a T);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.pop() {
                None => return None,
                Some((offset, seg)) => {
                    if seg.len == 1 {
                        return Some((offset, &seg.value));
                    }
                    for e in 0..2 {
                        if let Some(c) = seg.child[e].as_ref() {
                            self.0.push((offset + seg.len / 2 * e, c));
                        }
                    }
                }
            }
        }
    }
}
impl<'a, T: 'a + Clone, O: 'a + Ops<Value = T>> IntoIterator for &'a Segtree<T, O> {
    type IntoIter = Iter<'a, T, O>;
    type Item = <Self::IntoIter as Iterator>::Item;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

fn __internal_open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
    (match range.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    })..match range.end_bound() {
        Bound::Excluded(&x) => x,
        Bound::Included(&x) => x + 1,
        Bound::Unbounded => len,
    }
}

/// [`Segtree`] の演算の情報を持つ型です。
///
/// [大まかな使い方はモジュールレベルドキュメントをご覧ください。](self)
pub trait Ops {
    /// 要素型
    type Value: Clone;
    /// 畳み込む演算
    ///
    /// # 要件
    ///
    /// 結合的
    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
    /// [`Self::op`] の単位元
    ///
    /// # 要件
    ///
    /// 単位元
    fn id() -> Self::Value;
    /// 初期状態の `len` セル分の値の畳み込み
    fn init(_len: usize) -> Self::Value {
        Self::id()
    }
}

#[cfg(test)]
mod tests {

    use {
        super::{Ops, Segtree},
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::SubRange,
    };

    enum Cat {}
    impl Ops for Cat {
        type Value = String;
        fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            lhs.chars().chain(rhs.chars()).collect::<String>()
        }
        fn id() -> Self::Value {
            String::new()
        }
        fn init(len: usize) -> Self::Value {
            "?".repeat(len)
        }
    }

    #[test]
    fn test_seg() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..20);
            println!("n = {}", n);
            let mut a = vec!["?".to_string(); n];
            let mut seg = Segtree::<_, Cat>::new(n);
            for iter in 0..2 * n {
                match rng.gen_range(0..3) {
                    // set
                    0 => {
                        let i = rng.gen_range(0..n);
                        let s = ((b'a' + (iter % 26) as u8) as char).to_string();
                        println!("Set {}, {}", i, &s);
                        a[i] = s.clone();
                        seg.set(i, s);
                    }
                    // fold
                    1 => {
                        let range = rng.sample(SubRange(0..n));
                        println!("Fold {:?}", &range);
                        let expected = a[range.clone()]
                            .iter()
                            .fold(Cat::id(), |x, y| Cat::op(&x, y));
                        let result = seg.fold(range);
                        assert_eq!(expected, result);
                    }
                    // collect
                    2 => {
                        let mut result = vec!["?".to_string(); n];
                        for (k, v) in &seg {
                            result[k] = v.clone();
                        }
                        println!("Collect. result = {:?}", &result);
                        assert_eq!(&result, &a);
                    }
                    _ => unreachable!(),
                }
                println!("seg = {:?}", &seg);
                println!("seg = {:?}", seg.debug_list());
            }
            println!();
        }
    }
}
