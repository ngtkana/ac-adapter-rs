//! van Emde Boas 木による整数集合の述語（predecessor/successor）データ構造。
//!
//! 全体を $\sqrt n$ 個ずつの塊（チャンク）に分割し、各チャンクを容量 $\sqrt n$ の
//! van Emde Boas 木として再帰的に管理する。どのチャンクが空でないかは
//! 別の van Emde Boas 木（summary）で管理し、目的の値が属するチャンク内に
//! 答えがなければ summary を辿って次の非空チャンクへ飛ぶ。この再帰により
//! 容量 $n$ の木の深さは $O(\log \log n)$ に抑えられ、`succ`/`pred`/`insert`/`remove`
//! もすべて同じ計算量で行える。最小値・最大値は各ノードにキャッシュしておくことで
//! `min`/`max` を $O(1)$ で返す。ハッシュマップ実装のため、事前に確保するのは
//! 容量 $n$ の数値のみで、実メモリは要素数に応じて増える。
//!
//! # 仕様
//!
//! - [`VebSet`][]: 整数集合 $S \subseteq \{0, \ldots, n-1\}$
//!   - `new(n)`: 容量 $n$ で空集合を構築
//!   - `insert(x)`: $S \leftarrow S \cup \{x\}$、新規追加なら `true`
//!   - `remove(x)`: $S \leftarrow S \setminus \{x\}$、存在したら `true`
//!   - `contains(x)`: $x \in S$
//!   - `min()`, `max()`: $\min(S)$, $\max(S)$（空なら `None`）
//!   - `succ(x)`: $x$ より大きい最小要素、`pred(x)`: $x$ より小さい最大要素
//!   - `pred_eq(x)`: $x$ 以下の最大要素
//!   - `len()`, `is_empty()`, `collect()`: 要素数、空判定、昇順の [`Vec`] 化
//! - [`VebMap`][]`<V>`: [`VebSet`] にキーごとの値 `V` を付加したマップ
//!   - 各操作はキー用の `VebSet` と値の `HashMap` を同期して更新する
//!   - `_key`/`_value` 接尾辞のメソッドでキーのみ・値のみを取得できる
//!
//! # 例
//!
//! ```
//! # use veb::VebSet;
//! let mut veb = VebSet::new(1000); // 容量
//! veb.insert(42);
//! assert!(veb.contains(42));
//! veb.remove(42);
//! assert!(!veb.contains(42));
//!
//! let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
//! assert_eq!(veb.collect(), vec![12, 34, 56, 78]);
//! assert_eq!(veb.min(), Some(12));
//! assert_eq!(veb.max(), Some(78));
//! assert_eq!(veb.succ(34), Some(56));
//! assert_eq!(veb.pred(34), Some(12));
//! assert_eq!(veb.contains(34), true);
//! assert_eq!(veb.contains(35), false);
//! assert_eq!(veb.len(), 4);
//! ```
//!
//! # 計算量
//!
//! $n$ を容量とする。
//!
//! - `insert`, `remove`, `contains`, `succ`, `pred`, `pred_eq`: $O(\log \log n)$
//! - `min`, `max`, `len`, `is_empty`: $O(1)$
//! - `collect`: $O(|S| \log \log n)$

use std::collections::HashMap;

macro_rules! multi_or_else {
    ($e:expr, $($f:expr),+) => {
        $e.or_else(|| multi_or_else!($($f),+))
    };
    ($e:expr) => {
        $e
    };
}

/// [`VebSet`] にハッシュマップで値を対応付けたマップ。
///
/// # 例
/// ```
/// use veb::VebMap;
/// let mut veb = VebMap::from_iter(vec![(42, "foo"), (43, "bar")]);
/// assert_eq!(veb.get(42), Some(&"foo"));
/// assert_eq!(veb.get(43), Some(&"bar"));
/// assert_eq!(veb.get(44), None);
///
/// assert_eq!(veb.min(), Some((42, &"foo")));
/// assert_eq!(veb.min_key(), Some(42));
/// assert_eq!(veb.min_value(), Some(&"foo"));
/// ```
pub struct VebMap<V> {
    veb: VebSet,
    map: HashMap<usize, V>,
}
impl<V> VebMap<V> {
    /// 容量 $n$ の空のマップを構築する。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::new(1000);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            veb: VebSet::new(n),
            map: HashMap::new(),
        }
    }

    /// キー $i$ に値 $v$ を挿入する。キーが既に存在した場合は前の値を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1000);
    /// assert_eq!(veb.insert(42, "foo"), None);
    /// assert_eq!(veb.insert(42, "bar"), Some("foo"));
    /// ```
    pub fn insert(&mut self, i: usize, v: V) -> Option<V> {
        self.veb.insert(i);
        self.map.insert(i, v)
    }

    /// キー $i$ を削除し、その値を返す。存在しなければ `None`。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1000);
    /// veb.insert(42, "foo");
    /// assert_eq!(veb.remove(42), Some("foo"));
    /// assert_eq!(veb.remove(42), None);
    /// ```
    pub fn remove(&mut self, i: usize) -> Option<V> {
        self.veb.remove(i);
        self.map.remove(&i)
    }

    /// キーに対応する値の参照を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1000);
    /// veb.insert(42, "foo");
    /// assert_eq!(veb.get(42), Some(&"foo"));
    /// assert_eq!(veb.get(43), None);
    /// ```
    pub fn get(&self, i: usize) -> Option<&V> {
        self.map.get(&i)
    }

    /// キーに対応する値の可変参照を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1000);
    /// veb.insert(42, "foo");
    /// assert_eq!(veb.get_mut(42), Some(&mut "foo"));
    /// assert_eq!(veb.get_mut(43), None);
    /// ```
    pub fn get_mut(&mut self, i: usize) -> Option<&mut V> {
        self.map.get_mut(&i)
    }

    /// 最小キー $\min(S)$ を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.min_key(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.min_key(), Some(42));
    /// ```
    pub fn min_key(&self) -> Option<usize> {
        self.veb.min()
    }

    /// 最小キーに対応する値を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.min_value(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.min_value(), Some(&"foo"));
    /// ```
    pub fn min_value(&self) -> Option<&V> {
        self.veb.min().and_then(|i| self.map.get(&i))
    }

    /// 最小キーとその値の組を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.min(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.min(), Some((42, &"foo")));
    /// ```
    pub fn min(&self) -> Option<(usize, &V)> {
        self.veb
            .min()
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// 最大キー $\max(S)$ を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.max_key(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.max_key(), Some(42));
    /// ```
    pub fn max_key(&self) -> Option<usize> {
        self.veb.max()
    }

    /// 最大キーに対応する値を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.max_value(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.max_value(), Some(&"foo"));
    /// ```
    pub fn max_value(&self) -> Option<&V> {
        self.veb.max().and_then(|i| self.map.get(&i))
    }

    /// 最大キーとその値の組を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.max(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.max(), Some((42, &"foo")));
    /// ```
    pub fn max(&self) -> Option<(usize, &V)> {
        self.veb
            .max()
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// $i$ より大きい最小キーを返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_key(34), Some(56));
    /// assert_eq!(veb.succ_value(34), Some(&"baz"));
    /// assert_eq!(veb.succ(34), Some((56, &"baz")));
    /// assert_eq!(veb.succ(78), None);
    /// ```
    pub fn succ_key(&self, i: usize) -> Option<usize> {
        self.veb.succ(i)
    }

    /// $i$ より大きい最小キーに対応する値を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_value(34), Some(&"baz"));
    /// assert_eq!(veb.succ_value(78), None);
    /// ```
    pub fn succ_value(&self, i: usize) -> Option<&V> {
        self.veb.succ(i).and_then(|i| self.map.get(&i))
    }

    /// $i$ より大きい最小キーとその値の組を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ(34), Some((56, &"baz")));
    /// assert_eq!(veb.succ(78), None);
    /// ```
    pub fn succ(&self, i: usize) -> Option<(usize, &V)> {
        self.veb
            .succ(i)
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// $i$ 以上の最小キーを返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_eq_key(34), Some(34));
    /// assert_eq!(veb.succ_eq_key(35), Some(56));
    /// ```
    pub fn succ_eq_key(&self, i: usize) -> Option<usize> {
        if self.contains_key(i) {
            return Some(i);
        }
        self.succ_key(i)
    }

    /// $i$ 以上の最小キーに対応する値を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_eq_value(34), Some(&"bar"));
    /// assert_eq!(veb.succ_eq_value(35), Some(&"baz"));
    /// ```
    pub fn succ_eq_value(&self, i: usize) -> Option<&V> {
        if let Some(v) = self.get(i) {
            return Some(v);
        }
        self.succ_value(i)
    }

    /// $i$ 以上の最小キーとその値の組を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_eq(34), Some((34, &"bar")));
    /// assert_eq!(veb.succ_eq(35), Some((56, &"baz")));
    /// ```
    pub fn succ_eq(&self, i: usize) -> Option<(usize, &V)> {
        if let Some(v) = self.get(i) {
            return Some((i, v));
        }
        self.succ(i)
    }

    /// $i$ より小さい最大キーを返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_key(34), Some(12));
    /// assert_eq!(veb.pred_value(34), Some(&"foo"));
    /// assert_eq!(veb.pred(34), Some((12, &"foo")));
    /// assert_eq!(veb.pred(12), None);
    /// ```
    pub fn pred_key(&self, i: usize) -> Option<usize> {
        self.veb.pred(i)
    }

    /// $i$ より小さい最大キーに対応する値を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_value(34), Some(&"foo"));
    /// assert_eq!(veb.pred_value(12), None);
    /// ```
    pub fn pred_value(&self, i: usize) -> Option<&V> {
        self.veb.pred(i).and_then(|i| self.map.get(&i))
    }

    /// $i$ より小さい最大キーとその値の組を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred(34), Some((12, &"foo")));
    /// assert_eq!(veb.pred(12), None);
    /// ```
    pub fn pred(&self, i: usize) -> Option<(usize, &V)> {
        self.veb
            .pred(i)
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// $i$ 以下の最大キーを返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_eq_key(34), Some(34));
    /// assert_eq!(veb.pred_eq_key(33), Some(12));
    /// ```
    pub fn pred_eq_key(&self, i: usize) -> Option<usize> {
        if self.contains_key(i) {
            return Some(i);
        }
        self.pred_key(i)
    }

    /// $i$ 以下の最大キーに対応する値を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_eq_value(34), Some(&"bar"));
    /// assert_eq!(veb.pred_eq_value(33), Some(&"foo"));
    /// ```
    pub fn pred_eq_value(&self, i: usize) -> Option<&V> {
        if let Some(v) = self.get(i) {
            return Some(v);
        }
        self.pred_value(i)
    }

    /// $i$ 以下の最大キーとその値の組を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_eq(34), Some((34, &"bar")));
    /// assert_eq!(veb.pred_eq(33), Some((12, &"foo")));
    /// ```
    pub fn pred_eq(&self, i: usize) -> Option<(usize, &V)> {
        if let Some(v) = self.get(i) {
            return Some((i, v));
        }
        self.pred(i)
    }

    /// マップの要素数 $|S|$ を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.len(), 0);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.veb.len()
    }

    /// マップが空なら `true` を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::<()>::from_iter(vec![]);
    /// assert_eq!(veb.is_empty(), true);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.veb.is_empty()
    }

    /// マップが指定したキーを含むなら `true` を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.contains_key(42), true);
    /// assert_eq!(veb.contains_key(43), false);
    /// ```
    pub fn contains_key(&self, i: usize) -> bool {
        self.veb.contains(i)
    }

    /// マップの要素をキーの昇順に並べた [`Vec`] を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.collect(), vec![
    ///     (12, &"foo"),
    ///     (34, &"bar"),
    ///     (56, &"baz"),
    ///     (78, &"qux")
    /// ]);
    /// ```
    pub fn collect(&self) -> Vec<(usize, &V)> {
        self.veb
            .collect()
            .into_iter()
            .filter_map(|i| self.map.get(&i).map(|v| (i, v)))
            .collect()
    }
}

impl<V: std::fmt::Debug> std::fmt::Debug for VebMap<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.collect()).finish()
    }
}

impl<V> std::iter::FromIterator<(usize, V)> for VebMap<V> {
    fn from_iter<I: IntoIterator<Item = (usize, V)>>(iter: I) -> Self {
        let vec = iter.into_iter().collect::<Vec<_>>();
        let mut veb = VebMap::new(vec.iter().map(|(i, _)| *i).max().unwrap_or(0) + 1);
        for (i, v) in vec {
            veb.insert(i, v);
        }
        veb
    }
}

impl<V> std::ops::Index<usize> for VebMap<V> {
    type Output = V;

    fn index(&self, i: usize) -> &V {
        self.get(i).unwrap()
    }
}
impl<V> std::ops::IndexMut<usize> for VebMap<V> {
    fn index_mut(&mut self, i: usize) -> &mut V {
        self.get_mut(i).unwrap()
    }
}

/// van Emde Boas 木で実装した整数集合。
pub enum VebSet {
    Internal {
        min: usize,
        max: usize,
        len: usize,
        csize: usize,
        summary: Box<VebSet>,
        chunks: HashMap<usize, VebSet>,
    },
    Leaf(u64),
}
impl VebSet {
    /// 容量 $n$ の空集合を構築する。
    ///
    /// # 例
    /// ```
    /// use veb::VebSet;
    /// let veb = VebSet::new(1000);
    /// ```
    pub fn new(n: usize) -> Self {
        if n <= 64 {
            VebSet::Leaf(0)
        } else {
            let csize = (n as f64).sqrt().ceil() as usize;
            let ccount = n.div_ceil(csize);
            Self::Internal {
                min: 0,
                max: 0,
                csize,
                len: 0,
                summary: Box::new(VebSet::new(ccount)),
                chunks: HashMap::new(),
            }
        }
    }

    /// 集合の最小値を返す。空なら `None`。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).min(), None);
    /// assert_eq!(VebSet::from_iter(vec![42]).min(), Some(42));
    /// assert_eq!(VebSet::from_iter(vec![42, 43]).min(), Some(42));
    /// ```
    pub fn min(&self) -> Option<usize> {
        match self {
            Self::Internal { min, len, .. } => Some(*min).filter(|_| *len > 0),
            Self::Leaf(bs) => Some(bs.trailing_zeros() as usize).filter(|&i| i < 64),
        }
    }

    /// 集合の最大値を返す。空なら `None`。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).max(), None);
    /// assert_eq!(VebSet::from_iter(vec![42]).max(), Some(42));
    /// assert_eq!(VebSet::from_iter(vec![42, 43]).max(), Some(43));
    /// ```
    pub fn max(&self) -> Option<usize> {
        match self {
            Self::Internal { max, len, .. } => Some(*max).filter(|_| *len > 0),
            Self::Leaf(bs) => bs.checked_ilog2().map(|i| i as usize),
        }
    }

    /// 集合の要素数を返す。
    ///
    /// # 例
    /// ```
    /// use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).len(), 0);
    /// assert_eq!(VebSet::from_iter(vec![42]).len(), 1);
    /// assert_eq!(VebSet::from_iter(vec![42, 43]).len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        match self {
            Self::Internal { len, .. } => *len,
            Self::Leaf(bs) => bs.count_ones() as usize,
        }
    }

    /// 集合が空なら `true` を返す。`self.len() == 0` と等価。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).is_empty(), true);
    /// assert_eq!(VebSet::from_iter(vec![42]).is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 要素を集合に挿入する。既に存在しなければ `true` を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// let mut veb = VebSet::new(1000);
    /// assert_eq!(veb.insert(42), true);
    /// assert_eq!(veb.insert(42), false);
    /// ```
    pub fn insert(&mut self, mut i: usize) -> bool {
        match self {
            Self::Internal {
                min,
                max,
                csize,
                len,
                summary,
                chunks,
            } => {
                if *len == 0 {
                    *min = i;
                    *max = i;
                    *len = 1;
                    true
                } else {
                    if i < *min {
                        std::mem::swap(&mut i, min);
                    }
                    *max = (*max).max(i);
                    if i == *min {
                        return false;
                    }
                    let j = i / *csize;
                    let k = i % *csize;
                    let result = if let Some(chunk) = chunks.get_mut(&j) {
                        chunk.insert(k)
                    } else {
                        let mut chunk = VebSet::new(*csize);
                        assert!(chunk.insert(k));
                        chunks.insert(j, chunk);
                        summary.insert(j);
                        true
                    };
                    if result {
                        *len += 1;
                    }
                    result
                }
            }
            Self::Leaf(bs) => {
                let result = *bs >> i & 1;
                *bs |= 1 << i;
                result == 0
            }
        }
    }

    /// 要素を集合から削除する。存在すれば `true` を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// let mut veb = VebSet::new(1000);
    /// veb.insert(42);
    /// assert_eq!(veb.remove(42), true);
    /// assert_eq!(veb.remove(42), false);
    /// ```
    pub fn remove(&mut self, mut i: usize) -> bool {
        match self {
            Self::Internal {
                min,
                max,
                csize,
                len,
                summary,
                chunks,
            } => match len {
                0 => false,
                1 => {
                    let result = i == *min;
                    if result {
                        *min = 0;
                        *max = 0;
                        *len = 0;
                    }
                    result
                }
                _ => {
                    if i == *min {
                        let j = summary.min().unwrap();
                        i = j * *csize + chunks[&j].min().unwrap();
                        *min = i;
                    }
                    let j = i / *csize;
                    let k = i % *csize;
                    let result = chunks.get_mut(&j).is_some_and(|chunk| chunk.remove(k));
                    if result {
                        *len -= 1;
                        if chunks[&j].is_empty() {
                            chunks.remove(&j);
                            summary.remove(j);
                        }
                        if i == *max {
                            *max = if let Some(j) = summary.max() {
                                j * *csize + chunks[&j].max().unwrap()
                            } else {
                                *min
                            };
                        }
                    }
                    result
                }
            },
            Self::Leaf(bs) => {
                let result = *bs >> i & 1;
                *bs &= !(1 << i);
                result == 1
            }
        }
    }

    /// $i$ より大きい最小要素を返す。$i$ が最大要素なら `None`。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
    /// assert_eq!(veb.succ(34), Some(56));
    /// assert_eq!(veb.succ(78), None);
    /// ```
    pub fn succ(&self, i: usize) -> Option<usize> {
        match self {
            Self::Internal {
                min,
                max,
                len,
                csize,
                summary,
                chunks,
                ..
            } => {
                let j = i / csize;
                let k = i % csize;
                match () {
                    () if *len == 0 || *max <= i => None,
                    () if i < *min => Some(*min),
                    () => multi_or_else!(
                        chunks
                            .get(&j)
                            .and_then(|chunk| chunk.succ(k))
                            .map(|k1| j * csize + k1),
                        summary
                            .succ(j)
                            .map(|j1| j1 * csize + chunks[&j1].min().unwrap())
                    ),
                }
            }
            &Self::Leaf(bs) => match i {
                63 => None,
                _ => Some(i + 1 + (bs >> (i + 1)).trailing_zeros() as usize).filter(|&i1| i1 < 64),
            },
        }
    }

    /// $i$ より小さい最大要素 $\max\{j \in S \mid j < i\}$ を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
    /// assert_eq!(veb.pred(34), Some(12));
    /// assert_eq!(veb.pred(12), None);
    /// ```
    pub fn pred(&self, i: usize) -> Option<usize> {
        match self {
            Self::Internal {
                min,
                max,
                csize,
                len,
                summary,
                chunks,
            } => {
                let j = i / csize;
                let k = i % csize;
                match () {
                    () if *len == 0 || i <= *min => None,
                    () if *max < i => Some(*max),
                    () => multi_or_else!(
                        chunks
                            .get(&j)
                            .and_then(|chunk| chunk.pred(k))
                            .map(|k1| { j * csize + k1 }),
                        summary
                            .pred(j)
                            .map(|j1| { j1 * csize + chunks[&j1].max().unwrap() }),
                        Some(*min)
                    ),
                }
            }
            &Self::Leaf(bs) => (bs & ((1 << i) - 1)).checked_ilog2().map(|j| j as usize),
        }
    }

    /// $i$ 以下の最大要素 $\max\{j \in S \mid j \le i\}$ を返す。
    pub fn pred_eq(&self, i: usize) -> Option<usize> {
        if self.contains(i) {
            return Some(i);
        }
        self.pred(i)
    }

    /// 集合が指定した要素を含むなら `true` を返す。
    ///
    /// # 例
    /// ```
    /// # use veb::VebSet;
    /// let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
    /// assert_eq!(veb.contains(34), true);
    /// assert_eq!(veb.contains(35), false);
    /// ```
    pub fn contains(&self, i: usize) -> bool {
        match self {
            Self::Internal {
                min,
                csize,
                len,
                chunks,
                ..
            } => {
                let j = i / csize;
                let k = i % csize;
                *len != 0 && (i == *min || chunks.get(&j).is_some_and(|chunk| chunk.contains(k)))
            }
            Self::Leaf(bs) => bs >> i & 1 == 1,
        }
    }

    /// 集合の要素を昇順に並べた [`Vec`] を返す。
    pub fn collect(&self) -> Vec<usize> {
        let mut result = Vec::with_capacity(self.len());
        let mut i = self.min();
        for _ in 0..self.len() {
            result.push(i.unwrap());
            i = self.succ(i.unwrap());
        }
        result
    }
}

impl std::fmt::Debug for VebSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.collect()).finish()
    }
}

impl std::iter::FromIterator<usize> for VebSet {
    fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
        let vec: Vec<_> = iter.into_iter().collect();
        let mut veb = VebSet::new(vec.iter().copied().max().unwrap_or(0) + 1);
        for i in vec {
            veb.insert(i);
        }
        veb
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;
    use std::ops::RangeInclusive;

    #[rstest]
    #[case(0..=64)]
    #[case(62..=66)]
    #[case(65..=4096)]
    #[case(4094..=4098)]
    #[case(1_000_000_000..=2_000_000_000)]
    fn test_veb_set(#[case] nrange: RangeInclusive<usize>) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(nrange.clone());
            let mut veb = VebSet::new(n);
            let mut set = BTreeSet::new();
            for _ in 0..200 {
                let i = rng.gen_range(0..n);
                match rng.gen_range(0..5) {
                    0 => assert_eq!(veb.insert(i), set.insert(i), "insert({i})"),
                    1 => assert_eq!(veb.remove(i), set.remove(&i), "remove({i})"),
                    2 => assert_eq!(veb.succ(i), set.range(i + 1..).next().copied(), "succ({i})"),
                    3 => assert_eq!(
                        veb.pred(i),
                        set.range(..i).next_back().copied(),
                        "pred({i})"
                    ),
                    4 => assert_eq!(veb.contains(i), set.contains(&i), "contains({i})"),
                    _ => unreachable!(),
                }
                assert_eq!(veb.min(), set.iter().next().copied(), "min");
                assert_eq!(veb.max(), set.iter().next_back().copied(), "max");
            }
        }
    }

    #[rstest]
    fn test_veb_map() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..1_000);
            let mut veb = VebMap::new(n);
            let mut map = BTreeMap::new();
            for _ in 0..200 {
                let i = rng.gen_range(0..n);
                match rng.gen_range(0..5) {
                    0 => {
                        let v = rng.gen_range(0..1_000);
                        assert_eq!(veb.insert(i, v), map.insert(i, v), "insert({i})");
                    }
                    1 => assert_eq!(veb.remove(i), map.remove(&i), "remove({i})"),
                    2 => assert_eq!(
                        veb.succ(i),
                        map.range(i + 1..).next().map(|(&i, v)| (i, v)),
                        "succ({i})"
                    ),
                    3 => assert_eq!(
                        veb.pred(i),
                        map.range(..i).next_back().map(|(&i, v)| (i, v)),
                        "pred({i})"
                    ),
                    4 => assert_eq!(veb.get(i), map.get(&i), "get({i})"),
                    _ => unreachable!(),
                }
                assert_eq!(veb.min(), map.iter().next().map(|(&i, v)| (i, v)), "min");
                assert_eq!(
                    veb.max(),
                    map.iter().next_back().map(|(&i, v)| (i, v)),
                    "max"
                );
            }
        }
    }
}
