//! $w$-ary tree による predecessor データ構造です。
//!
//! 論理的な boolean 配列 $B_1, \dots, B_n$ を管理します。
//!
//! 言い換えると、$[0, n[$ の部分集合 $S$ を管理していると思うことも出来ます。

const B: usize = u64::BITS as usize;

/// $w$-ary tree による predecessor データ構造です。
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct WAryTree {
    items: Vec<Vec<u64>>,
    len: usize,
}

impl WAryTree {
    /// 与えられた長さの空の $w$-ary tree を構築します。
    ///
    /// 長さ `len` の boolean 配列を管理する tree データ構造を作成します。
    /// 初期状態ではすべての要素が `false` です。
    ///
    /// # Examples
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
        while n != 1 {
            let q = n.div_ceil(B);
            items.push(vec![0; q]);
            n = q;
        }
        Self { items, len }
    }

    /// 管理している boolean 配列の長さを返します。
    pub fn len(&self) -> usize {
        self.len
    }

    /// tree が空 (長さが $0$) かどうかを返します。
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// boolean スライスから $w$-ary tree を構築します。
    ///
    /// 与えられた boolean スライスから tree データ構造を初期化します。
    ///
    /// # Examples
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
        if slice.is_empty() {
            return Self::new(0);
        }
        let base_items = slice
            .chunks(B)
            .map(|chunk| chunk.iter().rev().fold(0, |bs, &b| bs << 1 | u64::from(b)))
            .collect::<Vec<_>>();
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
        Self {
            items,
            len: slice.len(),
        }
    }

    /// $x \in S$ かどうかを答えます。
    ///
    /// # Panics if
    /// `x >= self.len()`
    ///
    /// # Examples
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

    /// $x$ を$S$ に追加します。
    ///
    /// # Panics if
    /// `x >= self.len()`
    ///
    /// # Returns
    /// 操作前の `!self.contains(x)`
    ///
    /// # Examples
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

    /// $S$ から $x$ を取り除きます。
    ///
    /// # Panics if
    /// `x >= self.len()`
    ///
    /// # Returns
    /// 操作前の `!self.contains(x)`
    ///
    /// # Examples
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
            x /= B;
        }
        true
    }

    /// $\mathrm{min}(S)$ を返します。なければ `None`。
    ///
    /// # Examples
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
        (self.len > 0 && self.items[0][0] != 0).then(|| subtree_min(&self.items, 0))
    }

    /// $\mathrm{min}(S \cap \small[x, \infty\small[)$ を返します。なければ `None`。
    ///
    /// # Examples
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

    /// $\min(S \cap \small] x, \infty \small[)$ を返します。
    ///
    /// # Examples
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

    /// $\mathrm{max}(S)$ を返します。なければ `None`。
    ///
    /// # Examples
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
        (self.len > 0 && self.items[0][0] != 0).then(|| subtree_max(&self.items, 0))
    }

    /// $\mathrm{max}(S \cap (-\infty, x])$ を返します。なければ `None`。
    ///
    /// # Examples
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

    /// $\mathrm{max}(S \cap (-\infty, x))$ を返します。
    ///
    /// # Examples
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

    /// bool のイテレータを返します。
    ///
    /// # Examples
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
        let lsb = items[j].ilog2() as usize;
        j = j * B + lsb;
    }
    j
}

impl FromIterator<bool> for WAryTree {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let slice = iter.into_iter().collect::<Vec<_>>();
        Self::from_slice_of_bool(&slice)
    }
}
