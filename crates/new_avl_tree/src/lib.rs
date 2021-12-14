use std::{borrow::Borrow, cmp::Ordering, fmt::Debug, iter::successors, mem::swap, ops::Index};

pub struct AvlTree<T> {
    root: Option<Box<Node<T>>>,
}
impl<T: Debug> AvlTree<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        len(&self.root)
    }
    pub fn append(&mut self, other: &mut Self) {
        self.root = merge([self.root.take(), other.root.take()]);
    }
    pub fn split_off_by(&mut self, mut is_right: impl FnMut(&T) -> bool) -> Self {
        let [left, right] = split_by(self.root.take(), |node| is_right(&node.value));
        self.root = left;
        Self { root: right }
    }
    pub fn split_off_at(&mut self, index: usize) -> Self {
        assert!(index <= self.len());
        let [left, right] = split_at(self.root.take(), index);
        self.root = left;
        Self { root: right }
    }
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.len());
        let mut other = self.split_off_at(index);
        self.root = Some(merge_with_root(
            [self.root.take(), other.root.take()],
            new(value),
        ));
    }
    pub fn remove_at(&mut self, index: usize) -> T {
        assert!(index < self.len());
        let mut right = self.split_off_at(index + 1);
        let center = self.split_off_at(index);
        self.append(&mut right);
        center.root.unwrap().value
    }
    pub fn get(&self, index: usize) -> Option<&T> {
        get(&self.root, index).map(|node| &node.value)
    }
    pub fn binary_search_by(&self, mut f: impl FnMut(&T) -> Ordering) -> Result<usize, usize> {
        binary_search_by(&self.root, |node| f(&node.value)).map(|(_node, index)| index)
    }
    pub fn binary_search_by_key<B>(&self, b: &B, mut f: impl FnMut(&T) -> B) -> Result<usize, usize>
    where
        B: Ord,
    {
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
                prev.child[0].as_ref().map(|node| &**node)
            })
            .collect(),
        }
    }
}

impl<T: Debug> Default for AvlTree<T> {
    fn default() -> Self {
        Self { root: None }
    }
}
impl<T: Debug> Index<usize> for AvlTree<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}
// TODO: not using vector
impl<T: Debug> FromIterator<T> for AvlTree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        fn from_slice_of_nodes<T: Debug>(
            nodes: &mut [Option<Box<Node<T>>>],
        ) -> Option<Box<Node<T>>> {
            if nodes.is_empty() {
                None
            } else {
                let i = nodes.len() / 2;
                Some(merge_with_root(
                    [
                        from_slice_of_nodes(&mut nodes[..i]),
                        from_slice_of_nodes(&mut nodes[i + 1..]),
                    ],
                    nodes[i].take().unwrap(),
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
impl<'a, T: Debug> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        let last = self.stack.pop()?;
        if let Some(mut crr) = last.child[1].as_ref() {
            self.stack.push(crr);
            while let Some(next) = crr.child[0].as_ref() {
                self.stack.push(next);
                crr = next;
            }
        }
        Some(&last.value)
    }
}

struct Node<T> {
    child: [Option<Box<Self>>; 2],
    value: T,
    len: usize,
    ht: u8,
}
fn new<T: Debug>(value: T) -> Box<Node<T>> {
    Box::new(Node {
        child: [None, None],
        value,
        len: 1,
        ht: 1,
    })
}
impl<T: Debug> Node<T> {
    fn update(&mut self) {
        self.len = len(&self.child[0]) + 1 + len(&self.child[1]);
        self.ht = 1 + ht(&self.child[0]).max(ht(&self.child[1]));
    }
    fn diff(&self, e: usize) -> isize {
        ht(&self.child[e]) as isize - ht(&self.child[1 - e]) as isize
    }
}
fn len<T: Debug>(tree: &Option<Box<Node<T>>>) -> usize {
    tree.as_ref().map_or(0, |node| node.len)
}
fn ht<T: Debug>(tree: &Option<Box<Node<T>>>) -> u8 {
    tree.as_ref().map_or(0, |node| node.ht)
}
fn balance<T: Debug>(tree: &mut Box<Node<T>>) {
    fn rotate<T: Debug>(tree: &mut Box<Node<T>>, e: usize) {
        let mut x = tree.child[e].take().unwrap();
        let y = x.child[1 - e].take();
        swap(tree, &mut x);
        x.child[e] = y;
        x.update();
        tree.child[1 - e] = Some(x);
        tree.update();
    }
    tree.update();
    for e in 0..2 {
        if 1 < tree.diff(e) {
            if 0 < tree.child[e].as_ref().unwrap().diff(1 - e) {
                rotate(tree.child[e].as_mut().unwrap(), 1 - e);
            }
            rotate(tree, e);
            break;
        }
    }
}
fn merge_with_root<T: Debug>(
    mut sub: [Option<Box<Node<T>>>; 2],
    mut center: Box<Node<T>>,
) -> Box<Node<T>> {
    for e in 0..2 {
        if ht(&sub[e]) > ht(&sub[1 - e]) {
            let mut root = sub[e].take().unwrap();
            let mut tmp = [None, None];
            tmp[e] = root.child[1 - e].take();
            tmp[1 - e] = sub[1 - e].take();
            root.child[1 - e] = Some(merge_with_root(tmp, center));
            balance(&mut root);
            return root;
        }
    }
    center.child = sub;
    center.update();
    center
}
fn merge<T: Debug>(mut sub: [Option<Box<Node<T>>>; 2]) -> Option<Box<Node<T>>> {
    match sub[1].take() {
        None => sub[0].take(),
        Some(sub1) => {
            let ([none, rhs], center, res) = split_delete_by(sub1, |_| true);
            debug_assert!(none.is_none());
            debug_assert_eq!(res, true);
            Some(merge_with_root([sub[0].take(), rhs], center))
        }
    }
}
fn split_delete_by<T: Debug>(
    mut root: Box<Node<T>>,
    mut is_right: impl FnMut(&Node<T>) -> bool,
) -> ([Option<Box<Node<T>>>; 2], Box<Node<T>>, bool) {
    let b = is_right(&*root) as bool;
    let e = b as usize;
    if root.child[1 - e].is_none() {
        let mut sub = [None, None];
        sub[e] = root.child[e].take();
        (sub, root, b)
    } else {
        let (mut sub, center, res) = split_delete_by(root.child[1 - e].take().unwrap(), is_right);
        let mut tmp = [None, None];
        tmp[e] = root.child[e].take();
        tmp[1 - e] = sub[e].take();
        sub[e] = Some(merge_with_root(tmp, root));
        (sub, center, res)
    }
}
fn split_by<T: Debug>(
    mut tree: Option<Box<Node<T>>>,
    is_right: impl FnMut(&Node<T>) -> bool,
) -> [Option<Box<Node<T>>>; 2] {
    match tree.take() {
        Some(root) => {
            let (mut sub, center, res) = split_delete_by(root, is_right);
            let e = res as usize;
            let mut tmp = [None, None];
            tmp[e] = sub[e].take();
            tmp[1 - e] = Some(center);
            sub[e] = merge(tmp);
            sub
        }
        None => [None, None],
    }
}
fn split_at<T: Debug>(tree: Option<Box<Node<T>>>, mut index: usize) -> [Option<Box<Node<T>>>; 2] {
    split_by(tree, |node| {
        let current = len(&node.child[0]);
        let res = index <= current;
        if !res {
            index -= current + 1;
        }
        res
    })
}
fn binary_search_by<T: Debug>(
    tree: &Option<Box<Node<T>>>,
    mut f: impl FnMut(&Node<T>) -> Ordering,
) -> Result<(&Node<T>, usize), usize> {
    let node = match tree.as_ref() {
        None => return Err(0),
        Some(node) => node,
    };
    let lsize = len(&node.child[0]);
    match f(&*node) {
        Ordering::Less => binary_search_by(&node.child[1], f)
            .map(|(node, index)| (node, lsize + 1 + index))
            .map_err(|index| lsize + 1 + index),
        Ordering::Equal => Ok((&*node, lsize)),
        Ordering::Greater => binary_search_by(&node.child[0], f),
    }
}
fn get<T: Debug>(tree: &Option<Box<Node<T>>>, mut index: usize) -> Option<&Node<T>> {
    binary_search_by(tree, |node| {
        let current = len(&node.child[0]);
        let res = current.cmp(&index);
        if res == Ordering::Less {
            index -= current + 1;
        }
        res
    })
    .ok()
    .map(|(node, _index)| node)
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
    fn test_split_off_by() {
        for n in 0..=10 {
            for i in 0..=n {
                let mut result0 = (0..n).collect::<AvlTree<_>>();
                let result1 = result0.split_off_by(|&x| i <= x);
                let expected0 = (0..i).collect::<Vec<_>>();
                let expected1 = (i..n).collect::<Vec<_>>();
                assert_eq!(result0.iter().copied().collect::<Vec<_>>(), expected0);
                assert_eq!(result1.iter().copied().collect::<Vec<_>>(), expected1);
            }
        }
    }

    #[test]
    fn test_split_off_at() {
        for n in 0..=10 {
            for i in 0..=n {
                let mut result0 = (0..n).collect::<AvlTree<_>>();
                let result1 = result0.split_off_at(i);
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
    fn test_remove_at() {
        for n in 0..=10 {
            for i in 0..n {
                let mut result = (0..n).collect::<AvlTree<_>>();
                let mut expected = (0..n).collect::<Vec<_>>();
                result.remove_at(i);
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
}
