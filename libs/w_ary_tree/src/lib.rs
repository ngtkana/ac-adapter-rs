//! $w$-ary tree による整数集合の predecessor/successor データ構造。
//!
//! 要素を $B = 64$（`u64::BITS`）分木のビットマスクとして管理する。深さ $i$ の各ノードは
//! 64 個の子のうち要素を含むものを 1 ビットで表し、根から葉までの経路をビット演算
//! （trailing/leading zeros）でたどることで、挿入・削除・predecessor/successor 探索を
//! すべて $O(\log_B n)$ で行える。
//!
//! # 仕様
//!
//! 全体集合 $[0, n)$ の部分集合 $S$ を管理する。
//!
//! - `WAryTree::new`: 空の $S$（全体集合のサイズ $n$）を構築
//! - `WAryTree::from_slice_of_bool`: `bool` スライスから構築（`true` の位置が $S$ の要素）
//! - `WAryTree::insert`: $x$ を $S$ に追加し、追加前に $x \notin S$ だったかを返す
//! - `WAryTree::remove`: $x$ を $S$ から削除し、削除前に $x \in S$ だったかを返す
//! - `WAryTree::contains`: $x \in S$ か判定
//! - `WAryTree::min`, `WAryTree::max`: $\min(S)$, $\max(S)$
//! - `WAryTree::successor_including`, `WAryTree::successor_excluding`: $\min(S \cap [x, \infty))$, $\min(S \cap (x, \infty))$
//! - `WAryTree::predecessor_including`, `WAryTree::predecessor_excluding`: $\max(S \cap (-\infty, x])$, $\max(S \cap (-\infty, x))$
//!
//! # 例
//!
//! ```
//! use w_ary_tree::WAryTree;
//!
//! let mut tree = WAryTree::new(10);
//! tree.insert(3);
//! tree.insert(7);
//! assert_eq!(tree.min(), Some(3));
//! assert_eq!(tree.successor_excluding(3), Some(7));
//! ```
//!
//! # 計算量
//!
//! 木の高さは $O(\log_B n)$（$B = 64$）。
//!
//! - 構築: $O(n / B)$
//! - `WAryTree::insert`, `WAryTree::remove`, `WAryTree::contains`: $O(\log_B n)$
//! - `WAryTree::min`, `WAryTree::max`、predecessor/successor 系: $O(\log_B n)$

const B: usize = u64::BITS as usize;

/// $B$-分木（$B = 64$）で整数集合を管理するデータ構造。
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct WAryTree {
    items: Vec<Vec<u64>>,
    len: usize,
}

impl WAryTree {
    /// 全体集合 $[0, \mathrm{len})$、部分集合 $S = \emptyset$ で構築する。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::new(10);
    /// assert_eq!(tree.len(), 10);
    /// assert!(!tree.is_empty());
    ///
    /// let empty = WAryTree::new(0);
    /// assert!(empty.is_empty());
    /// ```
    pub fn new(len: usize) -> Self {
        if len == 0 {
            return Self {
                items: vec![],
                len: 0,
            };
        }
        let mut n = len;
        let mut items = vec![];
        loop {
            let q = n.div_ceil(B);
            items.push(vec![0; q]);
            if q == 1 {
                break;
            }
            n = q;
        }
        Self { items, len }
    }

    /// 全体集合の大きさ $n$（`len`）を返す。
    pub fn len(&self) -> usize {
        self.len
    }

    /// 全体集合が空（$n = 0$）かどうかを返す。
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// `bool` スライスから構築する。`slice[i]` が `true` の位置が $S$ の要素になる。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let slice = vec![true, false, true, false];
    /// let tree = WAryTree::from_slice_of_bool(&slice);
    /// assert_eq!(tree.len(), 4);
    /// assert!(tree.contains(0));
    /// assert!(!tree.contains(1));
    /// assert!(tree.contains(2));
    /// assert!(!tree.contains(3));
    /// ```
    pub fn from_slice_of_bool(slice: &[bool]) -> Self {
        slice.iter().copied().collect()
    }

    /// $x \in S$ かどうかを返す（`x < self.len()` が前提）。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[true, false, true]);
    /// assert!(tree.contains(0));
    /// assert!(!tree.contains(1));
    /// assert!(tree.contains(2));
    /// ```
    pub fn contains(&self, x: usize) -> bool {
        assert!(x < self.len());
        self.items[0][x / B] >> (x % B) & 1 == 1
    }

    /// $x$ を $S$ に追加する（`x < self.len()` が前提）。
    ///
    /// 追加前に $x \notin S$ だったかを返す。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let mut tree = WAryTree::new(5);
    /// assert!(tree.insert(2));  // 新規挿入
    /// assert!(!tree.insert(2)); // 既に存在
    /// assert!(tree.contains(2));
    /// ```
    pub fn insert(&mut self, mut x: usize) -> bool {
        assert!(x < self.len());
        if self.contains(x) {
            return false;
        }
        for items in &mut self.items {
            items[x / B] |= 1 << (x % B);
            x /= B;
        }
        true
    }

    /// $x$ を $S$ から削除する（`x < self.len()` が前提）。
    ///
    /// 削除前に $x \in S$ だったかを返す。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let mut tree = WAryTree::from_slice_of_bool(&[true, false]);
    /// assert!(tree.remove(0));  // 存在していた
    /// assert!(!tree.remove(1)); // 存在していなかった
    /// assert!(!tree.contains(0));
    /// ```
    pub fn remove(&mut self, mut x: usize) -> bool {
        assert!(x < self.len());
        if !self.contains(x) {
            return false;
        }
        for items in &mut self.items {
            items[x / B] ^= 1 << (x % B);
            if items[x / B] != 0 {
                break;
            }
            x /= B;
        }
        true
    }

    /// $\mathrm{min}(S)$ を返す。なければ `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[false, true, false, true]);
    /// assert_eq!(tree.min(), Some(1));
    ///
    /// let empty = WAryTree::new(5);
    /// assert_eq!(empty.min(), None);
    /// ```
    pub fn min(&self) -> Option<usize> {
        (self.items.last().is_some_and(|last| last[0] != 0)).then(|| subtree_min(&self.items, 0))
    }

    /// $\mathrm{min}(S \cap \small[x, \infty\small[)$ を返す。なければ `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[true, false, true, false]);
    /// assert_eq!(tree.successor_including(1), Some(2));
    /// assert_eq!(tree.successor_including(0), Some(0));
    /// ```
    pub fn successor_including(&self, x: usize) -> Option<usize> {
        if self.contains(x) { Some(x) } else { self.successor_excluding(x) }
    }

    /// $\min(S \cap \small] x, \infty \small[)$ を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[true, false, true, false]);
    /// assert_eq!(tree.successor_excluding(0), Some(2));
    /// assert_eq!(tree.successor_excluding(2), None);
    /// ```
    pub fn successor_excluding(&self, mut x: usize) -> Option<usize> {
        for (i, items) in self.items.iter().enumerate() {
            let bs = items[x / B] >> (x % B) & !1;
            if bs == 0 {
                x /= B;
            } else {
                x += bs.trailing_zeros() as usize;
                return Some(subtree_min(&self.items[..i], x));
            }
        }
        None
    }

    /// $\mathrm{max}(S)$ を返す。なければ `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[false, true, false, true]);
    /// assert_eq!(tree.max(), Some(3));
    ///
    /// let empty = WAryTree::new(5);
    /// assert_eq!(empty.max(), None);
    /// ```
    pub fn max(&self) -> Option<usize> {
        (self.items.last().is_some_and(|last| last[0] != 0)).then(|| subtree_max(&self.items, 0))
    }

    /// $\mathrm{max}(S \cap (-\infty, x])$ を返す。なければ `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[true, false, true, false]);
    /// assert_eq!(tree.predecessor_including(2), Some(2));
    /// assert_eq!(tree.predecessor_including(1), Some(0));
    /// ```
    pub fn predecessor_including(&self, x: usize) -> Option<usize> {
        if self.contains(x) { Some(x) } else { self.predecessor_excluding(x) }
    }

    /// $\mathrm{max}(S \cap (-\infty, x))$ を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[true, false, true, false]);
    /// assert_eq!(tree.predecessor_excluding(2), Some(0));
    /// assert_eq!(tree.predecessor_excluding(0), None);
    /// ```
    pub fn predecessor_excluding(&self, mut x: usize) -> Option<usize> {
        for (i, items) in self.items.iter().enumerate() {
            let bs = items[x / B] << (B - 1 - x % B) & (u64::MAX >> 1);
            if bs == 0 {
                x /= B;
            } else {
                x -= bs.leading_zeros() as usize;
                return Some(subtree_max(&self.items[..i], x));
            }
        }
        None
    }

    /// $x \in S$ かどうかを $x = 0, 1, \ldots, n - 1$ の順に並べたイテレータを返す。
    ///
    /// # 例
    ///
    /// ```
    /// use w_ary_tree::WAryTree;
    ///
    /// let tree = WAryTree::from_slice_of_bool(&[true, false, true]);
    /// let vec: Vec<_> = tree.iter().collect();
    /// assert_eq!(vec, vec![true, false, true]);
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = bool> {
        (0..self.len).map(|x| self.contains(x))
    }
}

fn subtree_min(items: &[Vec<u64>], mut j: usize) -> usize {
    for items in items.iter().rev() {
        assert_ne!(items[j], 0);
        let lsb = items[j].trailing_zeros() as usize;
        j = j * B + lsb;
    }
    j
}

fn subtree_max(items: &[Vec<u64>], mut j: usize) -> usize {
    for items in items.iter().rev() {
        assert_ne!(items[j], 0);
        let msb = items[j].ilog2() as usize;
        j = j * B + msb;
    }
    j
}

impl FromIterator<bool> for WAryTree {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut base_items = Vec::with_capacity(iter.size_hint().0);
        let mut bs = 0u64;
        let mut len = 0;
        for b in iter {
            bs |= u64::from(b) << (len % B);
            len += 1;
            if len % B == 0 {
                base_items.push(bs);
                bs = 0;
            }
        }
        if len == 0 {
            return Self { items: vec![], len };
        }
        if len % B != 0 {
            base_items.push(bs);
        }
        let items = std::iter::successors(Some(base_items), |last| {
            (last.len() > 1).then(|| {
                last.chunks(B)
                    .map(|chunk| {
                        chunk
                            .iter()
                            .rev()
                            .fold(0, |bs, &b| bs << 1 | u64::from(b != 0))
                    })
                    .collect()
            })
        })
        .collect::<Vec<_>>();
        Self { items, len }
    }
}

#[cfg(test)]
mod tests {
    use crate::WAryTree;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    fn gen_instance(mut rng: impl Rng, p: f64) -> (usize, Vec<bool>, WAryTree) {
        let height = rng.gen_range(1..=3);
        let n = rng.gen_range(1 << ((height - 1) * 6)..(1 << (height * 6)).min(1 << 13));
        let a = (0..n).map(|_| rng.gen_bool(p)).collect::<Vec<_>>();
        let tree = WAryTree::from_slice_of_bool(&a);
        (n, a, tree)
    }

    #[test]
    fn test_w_ary_tree_insert() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let (n, mut a, mut tree) = gen_instance(&mut rng, 0.5);

            let x = rng.gen_range(0..n);
            let result = !a[x];
            a[x] = true;
            let expected = tree.insert(x);
            assert_eq!(result, expected, "x = {x}");

            let result = a.iter().copied().collect::<WAryTree>().items;
            let expected = tree.items;
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_w_ary_tree_remove() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let (n, mut a, mut tree) = gen_instance(&mut rng, 0.5);

            let x = rng.gen_range(0..n);
            let result = a[x];
            a[x] = false;
            let expected = tree.remove(x);
            assert_eq!(result, expected, "x = {x}");

            let result = a.iter().copied().collect::<WAryTree>().items;
            let expected = tree.items;
            assert_eq!(result, expected);
        }
    }
}
