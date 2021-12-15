use std::{borrow::Borrow, cmp::Ordering, fmt::Debug, iter::successors, mem::swap, ops::Index};

#[derive(Clone)]
pub struct AvlTree<T> {
    root: Option<Box<Node<T>>>,
}
impl<T> AvlTree<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    pub fn len(&self) -> usize {
        len(&self.root)
    }
    pub fn push_back(&mut self, value: T) {
        self.append(&mut Self {
            root: Some(new(value)),
        })
    }
    pub fn push_front(&mut self, value: T) {
        self.prepend(&mut Self {
            root: Some(new(value)),
        })
    }
    pub fn pop_back(&mut self) -> Option<T> {
        let root = self.root.take()?;
        let last_index = root.len - 1;
        let (left, center, _right) = split_delete(root, last_index);
        self.root = left;
        Some(center.value)
    }
    pub fn pop_front(&mut self) -> Option<T> {
        let (_left, center, right) = split_delete(self.root.take()?, 0);
        self.root = right;
        Some(center.value)
    }
    pub fn append(&mut self, other: &mut Self) {
        self.root = merge(self.root.take(), other.root.take());
    }
    pub fn prepend(&mut self, other: &mut Self) {
        self.root = merge(other.root.take(), self.root.take());
    }
    pub fn split_off(&mut self, index: usize) -> Self {
        assert!(index <= self.len());
        let (left, right) = split(self.root.take(), index);
        self.root = left;
        Self { root: right }
    }
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.len());
        let other = self.split_off(index);
        self.root = Some(merge_with_root(self.root.take(), new(value), other.root));
    }
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len());
        let (left, center, right) = split_delete(self.root.take().unwrap(), index);
        self.root = merge(left, right);
        center.value
    }
    pub fn get(&self, index: usize) -> Option<&T> {
        get(&self.root, index).map(|node| &node.value)
    }
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        get_mut(&mut self.root, index).map(|node| &mut node.value)
    }
    pub fn binary_search_by(&self, mut f: impl FnMut(&T) -> Ordering) -> Result<usize, usize> {
        binary_search_by(&self.root, |node| f(&node.value))
    }
    pub fn binary_search_by_key<B: Ord>(
        &self,
        b: &B,
        mut f: impl FnMut(&T) -> B,
    ) -> Result<usize, usize> {
        self.binary_search_by(|x| f(x).cmp(&b))
    }
    pub fn binary_search<Q>(&self, value: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.binary_search_by(|x| x.borrow().cmp(&value))
    }
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            stack: successors(self.root.as_ref().map(|node| &**node), |prev| {
                prev.left.as_ref().map(|node| &**node)
            })
            .collect(),
        }
    }
}

impl<T> Default for AvlTree<T> {
    fn default() -> Self {
        Self { root: None }
    }
}
impl<T: Debug> Debug for AvlTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self).finish()
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

pub struct Iter<'a, T> {
    stack: Vec<&'a Node<T>>,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        let last = self.stack.pop()?;
        if let Some(mut crr) = last.right.as_ref() {
            self.stack.push(crr);
            while let Some(next) = crr.left.as_ref() {
                self.stack.push(next);
                crr = next;
            }
        }
        Some(&last.value)
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
        self.len = len(&self.left) + 1 + len(&self.right);
        self.ht = 1 + ht(&self.left).max(ht(&self.right));
    }
}
fn len<T>(tree: &Option<Box<Node<T>>>) -> usize {
    tree.as_ref().map_or(0, |node| node.len)
}
fn ht<T>(tree: &Option<Box<Node<T>>>) -> u8 {
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
    if ht(&node.left) > 1 + ht(&node.right) {
        let left = node.left.as_mut().unwrap();
        if ht(&left.left) < ht(&left.right) {
            rotate_right(left);
        }
        rotate_left(node);
    } else if ht(&node.left) + 1 < ht(&node.right) {
        let right = node.right.as_mut().unwrap();
        if ht(&right.left) > ht(&right.right) {
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
    if ht(&left) > ht(&right) {
        let mut root = left.take().unwrap();
        root.right = Some(merge_with_root(root.right.take(), center, right));
        balance(&mut root);
        root
    } else if ht(&left) < ht(&right) {
        let mut root = right.take().unwrap();
        root.left = Some(merge_with_root(left, center, root.left.take()));
        balance(&mut root);
        root
    } else {
        center.left = left;
        center.right = right;
        center.update();
        center
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
fn split_delete<T>(
    mut root: Box<Node<T>>,
    index: usize,
) -> (Option<Box<Node<T>>>, Box<Node<T>>, Option<Box<Node<T>>>) {
    debug_assert!((0..root.len).contains(&index));
    let left = root.left.take();
    let right = root.right.take();
    let lsize = len(&left);
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
    tree: &Option<Box<Node<T>>>,
    mut f: impl FnMut(&Node<T>) -> Ordering,
) -> Result<usize, usize> {
    let node = match tree.as_ref() {
        None => return Err(0),
        Some(node) => node,
    };
    let lsize = len(&node.left);
    match f(&*node) {
        Ordering::Less => binary_search_by(&node.right, f)
            .map(|index| lsize + 1 + index)
            .map_err(|index| lsize + 1 + index),
        Ordering::Equal => Ok(lsize),
        Ordering::Greater => binary_search_by(&node.left, f),
    }
}
fn get<T>(tree: &Option<Box<Node<T>>>, index: usize) -> Option<&Node<T>> {
    let node = tree.as_ref()?;
    let lsize = len(&node.left);
    match lsize.cmp(&index) {
        Ordering::Less => get(&node.right, index - lsize - 1),
        Ordering::Equal => Some(node),
        Ordering::Greater => get(&node.left, index),
    }
}
fn get_mut<T>(tree: &mut Option<Box<Node<T>>>, index: usize) -> Option<&mut Node<T>> {
    let node = tree.as_mut()?;
    let lsize = len(&node.left);
    match lsize.cmp(&index) {
        Ordering::Less => get_mut(&mut node.right, index - lsize - 1),
        Ordering::Equal => Some(node),
        Ordering::Greater => get_mut(&mut node.left, index),
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
                let _ = result.get_mut(i).map(|x| *x = n);
                let _ = expected.get_mut(i).map(|x| *x = n);
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
}
