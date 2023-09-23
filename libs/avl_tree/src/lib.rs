//! AVL 木により二分探索可能な列を実現します。
//!
//! # できないこと
//!
//! - `iter_mut`
//! - fast [`IntoIter::nth()`]
//! - cursor
//! - fold / lazy action
//!
//!
//! # できること
//!
//! ## 二分探索してインデックスを返す系
//!
//! - [`binary_search`](AvlTree::binary_search)
//! - [`binary_search_by`](AvlTree::binary_search_by)
//! - [`binary_search_by_key`](AvlTree::binary_search_by_key)
//! - [`partition_point`](AvlTree::partition_point)
//!
//!
//! ## ランダムアクセス系
//!
//! - [`get`](AvlTree::get)
//! - [`get_mut`](AvlTree::get_mut)
//!
//!
//! ## 挿入・削除・併合・分割系
//!
//! - [`insert`](AvlTree::insert)
//! - [`remove`](AvlTree::remove)
//! - [`append`](AvlTree::append)
//! - [`split_off`](AvlTree::split_off)
//!
//!
//! ## 先頭・末尾系
//!
//! - [`front`](AvlTree::front)
//! - [`back`](AvlTree::back)
//! - [`push_front`](AvlTree::push_front)
//! - [`push_back`](AvlTree::push_back)
//! - [`pop_front`](AvlTree::pop_front)
//! - [`pop_back`](AvlTree::pop_back)
//!
//!
//! ## 走査系
//!
//! - [`iter`](AvlTree::iter)
//! - [`into_iter`](AvlTree::into_iter)
//!
use std::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::Debug,
    hash::Hash,
    iter::{successors, FromIterator},
    mem::swap,
    ops::Index,
};

/// AVL 木本体です。
#[derive(Clone)]
pub struct AvlTree<T> {
    root: Option<Box<Node<T>>>,
}
impl<T> AvlTree<T> {
    /// 空列を構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let avl = AvlTree::<()>::new();
    /// assert!(avl.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
    /// 空列であれば `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let avl = AvlTree::<()>::new();
    /// assert!(avl.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    /// 列の要素数を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// use std::iter::repeat;
    /// assert_eq!(AvlTree::<()>::new().len(), 0);
    /// assert_eq!(repeat(()).take(3).collect::<AvlTree::<_>>().len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        len(self.root.as_deref())
    }
    /// 列の末尾に要素を追加します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// avl.push_back(1);
    /// avl.push_back(3);
    /// assert_eq!(3, *avl.back().unwrap());
    /// ```
    pub fn push_back(&mut self, value: T) {
        self.append(&mut Self {
            root: Some(new(value)),
        })
    }
    /// 列の先頭に要素を追加します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// avl.push_front(1);
    /// avl.push_front(2);
    /// assert_eq!(avl.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, value: T) {
        let mut swp = Self {
            root: Some(new(value)),
        };
        swp.append(self);
        *self = swp;
    }
    /// 列の末尾の要素があれば削除して返し、空なら `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// assert_eq!(avl.pop_back(), None);
    /// avl.push_back(1);
    /// avl.push_back(3);
    /// assert_eq!(avl.pop_back(), Some(3));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        let root = self.root.take()?;
        let last_index = root.len - 1;
        let (left, center, _right) = split_delete(root, last_index);
        self.root = left;
        Some(center.value)
    }
    /// 列の先頭の要素があれば削除して返し、空なら `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// avl.push_front(1);
    /// avl.push_front(2);
    /// assert_eq!(avl.front(), Some(&2));
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        let (_left, center, right) = split_delete(self.root.take()?, 0);
        self.root = right;
        Some(center.value)
    }
    /// 列の末尾の要素があれば返し、空なら `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// assert_eq!(avl.back(), None);
    ///
    /// avl.push_back(1);
    /// avl.push_back(2);
    /// assert_eq!(avl.back(), Some(&2));
    /// ```
    pub fn back(&self) -> Option<&T> {
        self.get(self.len().checked_sub(1)?)
    }
    /// 列の先頭の要素があれば返し、空なら `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// assert_eq!(avl.front(), None);
    ///
    /// avl.push_back(1);
    /// avl.push_back(2);
    /// assert_eq!(avl.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        self.get(0)
    }
    /// 列の末尾の要素があれば返し、空なら `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl_tree = AvlTree::new();
    /// assert_eq!(avl_tree.back(), None);
    ///
    /// avl_tree.push_back(1);
    /// avl_tree.push_back(2);
    /// match avl_tree.back_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(avl_tree.back(), Some(&9));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.get_mut(self.len().checked_sub(1)?)
    }
    /// 列の先頭の要素があれば返し、空なら `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// assert_eq!(avl.front_mut(), None);
    ///
    /// avl.push_back(1);
    /// avl.push_back(2);
    /// match avl.front_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(avl.front(), Some(&9));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.get_mut(0)
    }
    /// `other` のすべての要素を `self` の後ろに挿入します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut buf: AvlTree<_> = vec![1, 2].into_iter().collect();
    /// let mut buf2: AvlTree<_> = vec![3, 4].into_iter().collect();
    /// buf.append(&mut buf2);
    /// assert_eq!(buf, [1, 2, 3, 4][..]);
    /// assert_eq!(buf2, [][..]);
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        self.root = merge(self.root.take(), other.root.take());
    }
    /// `other` の第 `index` 成分以降を切り離します。
    ///
    /// # Panics
    ///
    /// 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut buf: AvlTree<_> = vec![1, 2, 3].into_iter().collect();
    /// let buf2 = buf.split_off(1);
    /// assert_eq!(buf, [1][..]);
    /// assert_eq!(buf2, [2, 3][..]);
    /// ```
    pub fn split_off(&mut self, index: usize) -> Self {
        assert!(index <= self.len());
        let (left, right) = split(self.root.take(), index);
        self.root = left;
        Self { root: right }
    }
    /// `other` の第 `index` 成分に `value` を挿入します。
    ///
    /// # Panics
    ///
    /// 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// avl.push_back('a');
    /// avl.push_back('b');
    /// avl.push_back('c');
    /// assert_eq!(avl, ['a', 'b', 'c'][..]);
    ///
    /// avl.insert(1, 'd');
    /// assert_eq!(avl, ['a', 'd', 'b', 'c'][..]);
    /// ```
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.len());
        let other = self.split_off(index);
        self.root = Some(merge_with_root(self.root.take(), new(value), other.root));
    }
    /// `other` の第 `index` 成分があれば削除して返し、なければ `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// avl.push_back(1);
    /// avl.push_back(2);
    /// avl.push_back(3);
    /// assert_eq!(avl, [1, 2, 3][..]);
    ///
    /// assert_eq!(avl.remove(1), Some(2));
    /// assert_eq!(avl, [1, 3][..]);
    /// ```
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index < self.len() {
            let (left, center, right) = split_delete(self.root.take().unwrap(), index);
            self.root = merge(left, right);
            Some(center.value)
        } else {
            None
        }
    }
    /// `other` の第 `index` 成分があれば返し、なければ `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// avl.push_back(3);
    /// avl.push_back(4);
    /// avl.push_back(5);
    /// assert_eq!(avl.get(1), Some(&4));
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            Some(&get(self.root.as_ref().unwrap(), index).value)
        } else {
            None
        }
    }
    /// `other` の第 `index` 成分があれば返し、なければ `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut avl = AvlTree::new();
    /// avl.push_back(3);
    /// avl.push_back(4);
    /// avl.push_back(5);
    /// if let Some(elem) = avl.get_mut(1) {
    ///     *elem = 7;
    /// }
    ///
    /// assert_eq!(avl[1], 7);
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len() {
            Some(&mut get_mut(self.root.as_mut().unwrap(), index).value)
        } else {
            None
        }
    }
    /// `f` が `Equal` を返す要素があれば、なければ挿入箇所のインデックスを返します。
    ///
    /// # Requirements
    ///
    /// `f` の結果が `Less`, `Equal`, `Greater` とこの順に分割されていること。
    ///
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let avl: AvlTree<_> = vec![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into_iter().collect();
    ///
    /// assert_eq!(avl.binary_search_by(|x| x.cmp(&13)),  Ok(9));
    /// assert_eq!(avl.binary_search_by(|x| x.cmp(&4)),   Err(7));
    /// assert_eq!(avl.binary_search_by(|x| x.cmp(&100)), Err(13));
    /// let r = avl.binary_search_by(|x| x.cmp(&1));
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    pub fn binary_search_by(&self, f: impl FnMut(&T) -> Ordering) -> Result<usize, usize> {
        binary_search_by(self.root.as_deref(), f)
    }
    /// `f` が `Equal` を返す要素があれば、なければ挿入箇所のインデックスを返します。
    ///
    /// # Requirements
    ///
    /// `f` による射影が `b` と比べて小なる、等しい、大なる要素がこの順に分割されていること。
    ///
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let avl: AvlTree<_> = vec![(0, 0), (2, 1), (4, 1), (5, 1),
    ///          (3, 1), (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
    ///          (1, 21), (2, 34), (4, 55)].into_iter().collect();
    ///
    /// assert_eq!(avl.binary_search_by_key(&13, |&(a, b)| b),  Ok(9));
    /// assert_eq!(avl.binary_search_by_key(&4, |&(a, b)| b),   Err(7));
    /// assert_eq!(avl.binary_search_by_key(&100, |&(a, b)| b), Err(13));
    /// let r = avl.binary_search_by_key(&1, |&(a, b)| b);
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    pub fn binary_search_by_key<B: Ord>(
        &self,
        b: &B,
        mut f: impl FnMut(&T) -> B,
    ) -> Result<usize, usize> {
        self.binary_search_by(|x| f(x).cmp(b))
    }
    /// `value` に等しい要素があればそのインデックスを返し、なければ挿入箇所のインデックスを返します。
    ///
    /// # Requirements
    ///
    /// `value` よりも小なる、等しい、大なる要素がこの順に分割されていること。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let avl: AvlTree<_> = vec![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into_iter().collect();
    ///
    /// assert_eq!(avl.binary_search(&13),  Ok(9));
    /// assert_eq!(avl.binary_search(&4),   Err(7));
    /// assert_eq!(avl.binary_search(&100), Err(13));
    /// let r = avl.binary_search(&1);
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    pub fn binary_search<Q: Ord>(&self, value: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q>,
    {
        self.binary_search_by(|x| x.borrow().cmp(value))
    }
    pub fn partition_point(&self, mut is_right: impl FnMut(&T) -> bool) -> usize {
        partition_point(self.root.as_deref(), |node| is_right(&node.value))
    }
    /// `value` 以上の要素があればそおインデックスを、なければ要素数を返します。
    ///
    /// # Requirements
    ///
    /// 要素が全てソート済みであること。
    /// ただしソート済みでなくてもそれらしいところを返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let a: AvlTree<_> = [10, 11, 13, 13, 15].iter().copied().collect();
    /// assert_eq!(a.lower_bound(&9), 0);
    /// assert_eq!(a.lower_bound(&10), 0);
    /// assert_eq!(a.lower_bound(&11), 1);
    /// assert_eq!(a.lower_bound(&12), 2);
    /// assert_eq!(a.lower_bound(&13), 2);
    /// assert_eq!(a.lower_bound(&14), 4);
    /// assert_eq!(a.lower_bound(&15), 4);
    /// assert_eq!(a.lower_bound(&16), 5);
    /// ```
    pub fn lower_bound<Q: Ord>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
    {
        partition_point(self.root.as_deref(), |node| value <= node.value.borrow())
    }
    /// `value` より大きな要素があればそおインデックスを、なければ要素数を返します。
    ///
    /// # Requirements
    ///
    /// 要素が全てソート済みであること。
    /// ただしソート済みでなくてもそれらしいところを返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let a: AvlTree<_> = [10, 11, 13, 13, 15].iter().copied().collect();
    /// assert_eq!(a.upper_bound(&9), 0);
    /// assert_eq!(a.upper_bound(&10), 1);
    /// assert_eq!(a.upper_bound(&11), 2);
    /// assert_eq!(a.upper_bound(&12), 2);
    /// assert_eq!(a.upper_bound(&13), 4);
    /// assert_eq!(a.upper_bound(&14), 4);
    /// assert_eq!(a.upper_bound(&15), 5);
    /// assert_eq!(a.upper_bound(&16), 5);
    /// ```
    pub fn upper_bound<Q: Ord>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
    {
        partition_point(self.root.as_deref(), |node| value < node.value.borrow())
    }
    /// 要素を前から順にすべて走査するイテレータを返します。
    ///
    /// なお [`Iter`] は [`DoubleEndedIterator`] を実装しています。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlTree;
    /// let mut buf = AvlTree::new();
    /// buf.push_back(5);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// let b: &[_] = &[&5, &3, &4];
    /// let c: Vec<&i32> = buf.iter().collect();
    /// assert_eq!(&c[..], b);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            stack: successors(self.root.as_deref(), |current| current.left.as_deref()).collect(),
            rstack: successors(self.root.as_deref(), |current| current.right.as_deref()).collect(),
        }
    }
}

impl<T> Default for AvlTree<T> {
    fn default() -> Self {
        Self { root: None }
    }
}
impl<T: PartialEq> PartialEq for AvlTree<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other)
    }
}
impl<T: PartialEq, A> PartialEq<[A]> for AvlTree<T>
where
    T: PartialEq<A>,
{
    fn eq(&self, other: &[A]) -> bool {
        self.iter().eq(other)
    }
}
impl<T: Eq> Eq for AvlTree<T> {}
impl<T: PartialOrd> PartialOrd for AvlTree<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}
impl<T: Ord> Ord for AvlTree<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}
impl<T: Debug> Debug for AvlTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}
impl<T: Hash> Hash for AvlTree<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.iter().for_each(|elm| elm.hash(state));
    }
}
impl<T> IntoIterator for AvlTree<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        let mut stack = Vec::new();
        if let Some(mut current) = self.root {
            while let Some(next) = current.left.take() {
                stack.push(current);
                current = next;
            }
            stack.push(current);
        }
        IntoIter { stack }
    }
}
impl<'a, T> IntoIterator for &'a AvlTree<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<T> Index<usize> for AvlTree<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}
impl<T> FromIterator<T> for AvlTree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        fn from_slice_of_nodes<T>(nodes: &mut [Option<Box<Node<T>>>]) -> Option<Box<Node<T>>> {
            if nodes.is_empty() {
                None
            } else {
                let i = nodes.len() / 2;
                Some(merge_with_root(
                    from_slice_of_nodes(&mut nodes[..i]),
                    nodes[i].take().unwrap(),
                    from_slice_of_nodes(&mut nodes[i + 1..]),
                ))
            }
        }
        Self {
            root: from_slice_of_nodes(
                iter.into_iter()
                    .map(new)
                    .map(Some)
                    .collect::<Vec<_>>()
                    .as_mut_slice(),
            ),
        }
    }
}

/// [`AvlTree`] の要素を前から順にすべて走査するイテレータです。
pub struct Iter<'a, T> {
    stack: Vec<&'a Node<T>>,
    rstack: Vec<&'a Node<T>>,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.stack.pop()?;
        self.stack
            .extend(successors(current.right.as_deref(), |node| {
                node.left.as_deref()
            }));
        if std::ptr::eq(current, *self.rstack.last().unwrap()) {
            self.stack.clear();
            self.rstack.clear();
        }
        Some(&current.value)
    }
}
impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let current = self.rstack.pop()?;
        self.rstack
            .extend(successors(current.left.as_deref(), |node| {
                node.right.as_deref()
            }));
        if std::ptr::eq(current, *self.stack.last().unwrap()) {
            self.stack.clear();
            self.rstack.clear();
        }
        Some(&current.value)
    }
}

/// [`AvlTree`] の要素を前から順にすべて走査するイテレータです。
pub struct IntoIter<T> {
    stack: Vec<Box<Node<T>>>,
}
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let mut current = self.stack.pop()?;
        if let Some(mut current) = current.right.take() {
            while let Some(next) = current.left.take() {
                self.stack.push(current);
                current = next;
            }
            self.stack.push(current);
        }
        Some(current.value)
    }
}

#[derive(Clone)]
struct Node<T> {
    left: Option<Box<Self>>,
    right: Option<Box<Self>>,
    value: T,
    len: usize,
    ht: u8,
}
fn new<T>(value: T) -> Box<Node<T>> {
    Box::new(Node {
        left: None,
        right: None,
        value,
        len: 1,
        ht: 1,
    })
}
impl<T> Node<T> {
    fn update(&mut self) {
        self.len = len(self.left.as_deref()) + 1 + len(self.right.as_deref());
        self.ht = 1 + ht(self.left.as_deref()).max(ht(self.right.as_deref()));
    }
}
fn len<T>(tree: Option<&Node<T>>) -> usize {
    tree.as_ref().map_or(0, |node| node.len)
}
fn ht<T>(tree: Option<&Node<T>>) -> u8 {
    tree.as_ref().map_or(0, |node| node.ht)
}
fn balance<T>(node: &mut Box<Node<T>>) {
    fn rotate_left<T>(node: &mut Box<Node<T>>) {
        let mut x = node.left.take().unwrap();
        let y = x.right.take();
        swap(node, &mut x);
        x.left = y;
        x.update();
        node.right = Some(x);
        node.update();
    }
    fn rotate_right<T>(node: &mut Box<Node<T>>) {
        let mut x = node.right.take().unwrap();
        let y = x.left.take();
        swap(node, &mut x);
        x.right = y;
        x.update();
        node.left = Some(x);
        node.update();
    }
    if ht(node.left.as_deref()) > 1 + ht(node.right.as_deref()) {
        let left = node.left.as_mut().unwrap();
        if ht(left.left.as_deref()) < ht(left.right.as_deref()) {
            rotate_right(left);
        }
        rotate_left(node);
    } else if ht(node.left.as_deref()) + 1 < ht(node.right.as_deref()) {
        let right = node.right.as_mut().unwrap();
        if ht(right.left.as_deref()) > ht(right.right.as_deref()) {
            rotate_left(right);
        }
        rotate_right(node);
    } else {
        node.update();
    }
}
fn merge_with_root<T>(
    mut left: Option<Box<Node<T>>>,
    mut center: Box<Node<T>>,
    mut right: Option<Box<Node<T>>>,
) -> Box<Node<T>> {
    match ht(left.as_deref()).cmp(&ht(right.as_deref())) {
        Ordering::Less => {
            let mut root = right.take().unwrap();
            root.left = Some(merge_with_root(left, center, root.left.take()));
            balance(&mut root);
            root
        }
        Ordering::Equal => {
            center.left = left;
            center.right = right;
            center.update();
            center
        }
        Ordering::Greater => {
            let mut root = left.take().unwrap();
            root.right = Some(merge_with_root(root.right.take(), center, right));
            balance(&mut root);
            root
        }
    }
}
fn merge<T>(left: Option<Box<Node<T>>>, mut right: Option<Box<Node<T>>>) -> Option<Box<Node<T>>> {
    match right.take() {
        None => left,
        Some(right) => {
            let (_none, center, rhs) = split_delete(right, 0);
            Some(merge_with_root(left, center, rhs))
        }
    }
}
#[allow(clippy::type_complexity)]
fn split_delete<T>(
    mut root: Box<Node<T>>,
    index: usize,
) -> (Option<Box<Node<T>>>, Box<Node<T>>, Option<Box<Node<T>>>) {
    debug_assert!((0..root.len).contains(&index));
    let left = root.left.take();
    let right = root.right.take();
    let lsize = len(left.as_deref());
    match lsize.cmp(&index) {
        Ordering::Less => {
            let mut res = split_delete(right.unwrap(), index - lsize - 1);
            res.0 = Some(merge_with_root(left, root, res.0));
            res
        }
        Ordering::Equal => (left, root, right),
        Ordering::Greater => {
            let mut res = split_delete(left.unwrap(), index);
            res.2 = Some(merge_with_root(res.2, root, right));
            res
        }
    }
}
#[allow(clippy::type_complexity)]
fn split<T>(
    tree: Option<Box<Node<T>>>,
    index: usize,
) -> (Option<Box<Node<T>>>, Option<Box<Node<T>>>) {
    match tree {
        Some(root) => {
            if root.len == index {
                (Some(root), None)
            } else {
                let (left, center, right) = split_delete(root, index);
                (left, Some(merge_with_root(None, center, right)))
            }
        }
        None => (None, None),
    }
}
fn binary_search_by<T>(
    tree: Option<&Node<T>>,
    mut f: impl FnMut(&T) -> Ordering,
) -> Result<usize, usize> {
    let node = match tree {
        None => return Err(0),
        Some(node) => node,
    };
    let lsize = len(node.left.as_deref());
    match f(&node.value) {
        Ordering::Less => binary_search_by(node.right.as_deref(), f)
            .map(|index| lsize + 1 + index)
            .map_err(|index| lsize + 1 + index),
        Ordering::Equal => Ok(lsize),
        Ordering::Greater => binary_search_by(node.left.as_deref(), f),
    }
}
fn partition_point<T>(tree: Option<&Node<T>>, mut is_right: impl FnMut(&Node<T>) -> bool) -> usize {
    let node = match tree {
        None => return 0,
        Some(node) => node,
    };
    let lsize = len(node.left.as_deref());
    if is_right(node) {
        partition_point(node.left.as_deref(), is_right)
    } else {
        lsize + 1 + partition_point(node.right.as_deref(), is_right)
    }
}
fn get<T>(node: &Node<T>, index: usize) -> &Node<T> {
    let lsize = len(node.left.as_deref());
    match lsize.cmp(&index) {
        Ordering::Less => get(node.right.as_ref().unwrap(), index - lsize - 1),
        Ordering::Equal => node,
        Ordering::Greater => get(node.left.as_ref().unwrap(), index),
    }
}
fn get_mut<T>(node: &mut Node<T>, index: usize) -> &mut Node<T> {
    let lsize = len(node.left.as_deref());
    match lsize.cmp(&index) {
        Ordering::Less => get_mut(node.right.as_mut().unwrap(), index - lsize - 1),
        Ordering::Equal => node,
        Ordering::Greater => get_mut(node.left.as_mut().unwrap(), index),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_iter() {
        for n in 0..=10 {
            let result = (0..n)
                .collect::<AvlTree<_>>()
                .iter()
                .copied()
                .collect::<Vec<_>>();
            let expected = (0..n).collect::<Vec<_>>();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_push_back() {
        let mut result = AvlTree::new();
        let mut expected = Vec::new();
        for i in 0..10 {
            result.push_back(i);
            expected.push(i);
            assert_eq!(&result.iter().copied().collect::<Vec<_>>(), &expected);
        }
    }

    #[test]
    fn test_push_front() {
        let mut result = AvlTree::new();
        let mut expected = Vec::new();
        for i in 0..10 {
            result.push_front(i);
            expected.insert(0, i);
            assert_eq!(&result.iter().copied().collect::<Vec<_>>(), &expected);
        }
    }

    #[test]
    fn test_pop_back() {
        for n in 0..10 {
            let mut result = (0..n).collect::<AvlTree<_>>();
            let mut expected = (0..n).collect::<Vec<_>>();
            assert_eq!(result.pop_back(), expected.pop());
            assert_eq!(&result.iter().copied().collect::<Vec<_>>(), &expected);
        }
    }

    #[test]
    fn test_pop_front() {
        for n in 0..10 {
            let mut result = (0..n).collect::<AvlTree<_>>();
            let mut expected = (0..n).collect::<Vec<_>>();
            assert_eq!(
                result.pop_front(),
                if n == 0 {
                    None
                } else {
                    Some(expected.remove(0))
                }
            );
            assert_eq!(&result.iter().copied().collect::<Vec<_>>(), &expected);
        }
    }

    #[test]
    fn test_append() {
        for l in 0..=10 {
            for r in 0..=10 {
                let mut result = (0..l).collect::<AvlTree<_>>();
                result.append(&mut (l..l + r).collect::<AvlTree<_>>());
                let result = result.iter().copied().collect::<Vec<_>>();
                let expected = (0..l + r).collect::<Vec<_>>();
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_split_off() {
        for n in 0..=10 {
            for i in 0..=n {
                let mut result0 = (0..n).collect::<AvlTree<_>>();
                let result1 = result0.split_off(i);
                let expected0 = (0..i).collect::<Vec<_>>();
                let expected1 = (i..n).collect::<Vec<_>>();
                assert_eq!(result0.iter().copied().collect::<Vec<_>>(), expected0);
                assert_eq!(result1.iter().copied().collect::<Vec<_>>(), expected1);
            }
        }
    }

    #[test]
    fn test_insert() {
        for n in 0..=10 {
            for i in 0..=n {
                let mut result = (0..n).collect::<AvlTree<_>>();
                let mut expected = (0..n).collect::<Vec<_>>();
                result.insert(i, n);
                expected.insert(i, n);
                assert_eq!(result.iter().copied().collect::<Vec<_>>(), expected);
            }
        }
    }

    #[test]
    fn test_remove() {
        for n in 0..=10 {
            for i in 0..n {
                let mut result = (0..n).collect::<AvlTree<_>>();
                let mut expected = (0..n).collect::<Vec<_>>();
                result.remove(i);
                expected.remove(i);
                assert_eq!(result.iter().copied().collect::<Vec<_>>(), expected);
            }
        }
    }

    #[test]
    fn test_get() {
        for n in 0..=10 {
            for i in 0..=n {
                let result = (0..n).collect::<AvlTree<_>>();
                let expected = (0..n).collect::<Vec<_>>();
                let result = result.get(i);
                let expected = expected.get(i);
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_get_mut() {
        for n in 0..=10 {
            for i in 0..=n {
                let mut result = (0..n).collect::<AvlTree<_>>();
                let mut expected = (0..n).collect::<Vec<_>>();
                let _: Option<()> = result.get_mut(i).map(|x| *x = n);
                let _: Option<()> = expected.get_mut(i).map(|x| *x = n);
                assert_eq!(result.iter().copied().collect::<Vec<_>>(), expected);
            }
        }
    }

    #[test]
    fn test_binary_search() {
        for n in 0..=10 {
            for i in 0..=2 * n + 1 {
                let result = (1..=2 * n).step_by(2).collect::<AvlTree<_>>();
                let expected = (1..=2 * n).step_by(2).collect::<Vec<_>>();
                let result = result.binary_search(&i);
                let expected = expected.binary_search(&i);
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_binary_search_by_key() {
        for n in 0..=10 {
            for i in 0..=2 * n + 1 {
                let result = (1..=2 * n).step_by(2).collect::<AvlTree<_>>();
                let expected = (1..=2 * n).step_by(2).collect::<Vec<_>>();
                let result = result.binary_search_by_key(&(i * 10), |x| x * 10);
                let expected = expected.binary_search_by_key(&(i * 10), |x| x * 10);
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_lower_bound() {
        for n in 0..=10 {
            for i in 0..=2 * n + 1 {
                let result = (1..=2 * n).step_by(2).collect::<AvlTree<_>>();
                let expected = (1..=2 * n).step_by(2).collect::<Vec<_>>();
                let result = result.lower_bound(&i);
                let expected = expected.iter().position(|&x| i <= x).unwrap_or(n);
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_upper_bound() {
        for n in 0..=10 {
            for i in 0..=2 * n + 1 {
                let result = (1..=2 * n).step_by(2).collect::<AvlTree<_>>();
                let expected = (1..=2 * n).step_by(2).collect::<Vec<_>>();
                let result = result.upper_bound(&i);
                let expected = expected.iter().position(|&x| i < x).unwrap_or(n);
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_index() {
        for n in 0..=10 {
            for i in 0..n {
                let result = (0..n).collect::<AvlTree<_>>();
                let expected = (0..n).collect::<Vec<_>>();
                let result = result[i];
                let expected = expected[i];
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_clone() {
        for n in 0..=10 {
            let result = (0..n).collect::<AvlTree<_>>();
            let expected = (0..n).collect::<Vec<_>>();
            assert_eq!(&result.iter().copied().collect::<Vec<_>>(), &expected);

            let cloned = result.clone();
            assert_eq!(&result.iter().copied().collect::<Vec<_>>(), &expected);
            assert_eq!(&cloned.iter().copied().collect::<Vec<_>>(), &expected);
        }
    }

    #[test]
    fn test_debug() {
        for n in 0..=10 {
            let result = (0..n).collect::<AvlTree<_>>();
            let expected = (0..n).collect::<Vec<_>>();
            let result = format!("{:?}", &result);
            let expected = format!("{:?}", &expected);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_next() {
        for n in 0..=10 {
            let result = (0..n).collect::<AvlTree<_>>();
            let expected = (0..n).collect::<Vec<_>>();
            assert!(result.iter().eq(&expected));
        }
    }

    #[test]
    fn test_next_back() {
        for n in (0..=10).rev() {
            let result = (0..n).collect::<AvlTree<_>>();
            let expected = (0..n).collect::<Vec<_>>();
            assert!(result.iter().rev().eq(expected.iter().rev()));
        }
    }

    #[test]
    fn test_into_iter() {
        for n in 0..=10 {
            let result = (0..n).collect::<AvlTree<_>>();
            let expected = (0..n).collect::<Vec<_>>();
            assert_eq!(result.into_iter().collect::<Vec<_>>(), expected);
        }
    }

    #[test]
    fn test_next_next_back() {
        for n in (0..=8).rev() {
            let result = (0..n).collect::<AvlTree<_>>();
            let expected = (0..n).collect::<Vec<_>>();
            let mut result = result.iter();
            let mut expected = expected.iter();
            for bs in 0..1 << (n + 1) {
                for i in 0..=n {
                    if bs >> i & 1 == 0 {
                        assert_eq!(result.next(), expected.next());
                    } else {
                        assert_eq!(result.next_back(), expected.next_back());
                    }
                }
            }
        }
    }
}
