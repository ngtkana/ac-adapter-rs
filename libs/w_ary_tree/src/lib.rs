//! $w$-ary tree による predecessor データ構造です。
//!
//! 論理的な boolean 配列 $B_1, \dots, B_n$ を管理します。
//!
//! 言い換えると、$[0, n[$ の部分集合 $S$ を管理していると思うことも出来ます。

const B: usize = u64::BITS as usize;
const LG_B: usize = B.ilog2() as usize;

/// $w$-ary tree による predecessor データ構造です。
#[allow(dead_code)]
#[derive(Debug)]
pub struct WAryTree {
    items: Vec<u64>,
    offset: usize,
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
                offset: 0,
                len,
            };
        }
        let mut offset = 0;
        for _ in 0..len.ilog2() as usize / LG_B {
            offset = offset << LG_B | 1;
        }
        Self {
            items: vec![0; offset + len.div_ceil(B)],
            offset,
            len,
        }
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
        let mut result = Self::new(slice.len());
        let mut offset = result.offset;
        for (bs, chunk) in result.items[offset..].iter_mut().zip(slice.chunks(B)) {
            for &b in chunk.iter().rev() {
                *bs <<= 1;
                *bs |= u64::from(b);
            }
        }
        while offset != 0 {
            let upper_offset = offset >> LG_B;
            let (items, lower) = result.items.split_at_mut(offset);
            for (upper, chunk) in items[upper_offset..].iter_mut().zip(lower.chunks(B)) {
                for &item in chunk.iter().rev() {
                    *upper <<= 1;
                    *upper |= u64::from(item != 0);
                }
            }
            offset >>= LG_B;
        }
        result
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
        self.items[self.offset + x / B] >> (x % B) & 1 == 1
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
        let mut offset = self.offset;
        loop {
            self.items[offset + x / B] |= 1 << (x % B);
            if offset == 0 {
                return true;
            }
            x >>= LG_B;
            offset >>= LG_B;
        }
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
        let mut offset = self.offset;
        loop {
            self.items[offset + x / B] ^= 1 << (x % B);
            if offset == 0 || self.items[offset + x / B] != 0 {
                return true;
            }
            x >>= LG_B;
            offset >>= LG_B;
        }
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
        (self.len > 0 && self.items[0] != 0).then(|| self.subtree_min(0, 0))
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
        let mut offset = self.offset;
        loop {
            if x % B != B - 1 {
                let bs = self.items[offset + x / B] & u64::MAX << (x % B + 1);
                if bs != 0 {
                    let lsb = bs.trailing_zeros() as usize;
                    offset = offset << LG_B | 1;
                    x = x & usize::MAX << LG_B | lsb;
                    return Some(self.subtree_min(offset, x));
                }
            }
            if offset == 0 {
                return None;
            }
            offset >>= LG_B;
            x >>= LG_B;
        }
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
        (self.len > 0 && self.items[0] != 0).then(|| self.subtree_max(0, 0))
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
        let mut offset = self.offset;
        loop {
            if x % B != 0 {
                let bs = self.items[offset + x / B] & u64::MAX >> (B - x % B);
                if bs != 0 {
                    let msb = bs.ilog2() as usize;
                    offset = offset << LG_B | 1;
                    x = x & usize::MAX << LG_B | msb;
                    return Some(self.subtree_max(offset, x));
                }
            }
            if offset == 0 {
                return None;
            }
            offset >>= LG_B;
            x >>= LG_B;
        }
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

    fn subtree_min(&self, mut offset: usize, mut i: usize) -> usize {
        while offset < self.items.len() {
            assert_ne!(self.items[offset + i], 0);
            let lsb = self.items[offset + i].trailing_zeros() as usize;
            i = i << LG_B | lsb;
            offset = offset << LG_B | 1;
        }
        i
    }

    fn subtree_max(&self, mut offset: usize, mut i: usize) -> usize {
        while offset < self.items.len() {
            assert_ne!(self.items[offset + i], 0);
            let msb = self.items[offset + i].ilog2() as usize;
            i = i << LG_B | msb;
            offset = offset << LG_B | 1;
        }
        i
    }
}

impl FromIterator<bool> for WAryTree {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let slice = iter.into_iter().collect::<Vec<_>>();
        Self::from_slice_of_bool(&slice)
    }
}
