pub(crate) use crate::balance::Balance;
use crate::balance::BlackViolation;
use crate::balance::Color;
use crate::balance::Ptr;
use crate::balance::Tree;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;

pub trait MultimapOp {
    type Value;
    type Acc;

    fn to_acc(value: &Self::Value) -> Self::Acc;

    fn join(lhs: Option<&Self::Acc>, center: &Self::Value, rhs: Option<&Self::Acc>) -> Self::Acc;
}

#[allow(dead_code)]
pub struct Node<K, O: MultimapOp> {
    key: K,
    value: O::Value,
    acc: O::Acc,
    parent: Option<Ptr<Node<K, O>>>,
    left: Option<Ptr<Node<K, O>>>,
    right: Option<Ptr<Node<K, O>>>,
    len: usize,
    color: Color,
}
impl<K: Ord, O: MultimapOp> Node<K, O> {
    pub fn new(key: K, value: O::Value, color: Color) -> Self {
        Self {
            key,
            acc: O::to_acc(&value),
            value,
            parent: None,
            left: None,
            right: None,
            len: 1,
            color,
        }
    }
}
fn len<K, O: MultimapOp>(node: Option<Ptr<Node<K, O>>>) -> usize {
    node.as_ref().map_or(0, |node| node.len)
}
fn acc<K, O: MultimapOp>(node: &Option<Ptr<Node<K, O>>>) -> Option<&O::Acc> {
    node.as_ref().map(|node| &node.acc)
}
impl<K, O: MultimapOp> Balance for Node<K, O> {
    fn update(&mut self) {
        self.len = len(self.left) + 1 + len(self.right);
        self.acc = O::join(acc(&self.left), &self.value, acc(&self.right));
    }

    fn push(&mut self) {}

    fn color(&mut self) -> &mut Color {
        &mut self.color
    }

    fn parent(&mut self) -> &mut Option<Ptr<Self>> {
        &mut self.parent
    }

    fn left(&mut self) -> &mut Option<Ptr<Self>> {
        &mut self.left
    }

    fn right(&mut self) -> &mut Option<Ptr<Self>> {
        &mut self.right
    }
}
impl<K: Ord, O: MultimapOp> Ptr<Node<K, O>> {
    pub fn next(self) -> Option<Self> {
        let mut x = self;
        if let Some(r) = *x.right() {
            x = r;
            while let Some(l) = *x.left() {
                x = l;
            }
            Some(x)
        } else {
            while let Some(mut p) = *x.parent() {
                if *p.left() == Some(x) {
                    return Some(p);
                }
                x = p;
            }
            None
        }
    }

    pub fn prev(self) -> Option<Self> {
        let mut x = self;
        if let Some(l) = *x.left() {
            x = l;
            while let Some(r) = *x.right() {
                x = r;
            }
            Some(x)
        } else {
            while let Some(mut p) = *x.parent() {
                if *p.right() == Some(x) {
                    return Some(p);
                }
                x = p;
            }
            None
        }
    }
}

pub struct MultimapSeg<K, O: MultimapOp> {
    tree: Tree<Node<K, O>>,
}
impl<K: Ord, O: MultimapOp> MultimapSeg<K, O> {
    pub fn new() -> Self {
        Self { tree: Tree::new() }
    }

    pub fn len(&self) -> usize {
        len(self.tree.root)
    }

    pub fn is_empty(&self) -> bool {
        self.tree.root.is_none()
    }

    pub fn iter(&self) -> SegmapIter<'_, K, O> {
        SegmapIter {
            start: self.tree.min(),
            end: self.tree.max(),
            len: self.len(),
            marker: PhantomData,
        }
    }

    pub fn nth(&self, n: usize) -> (&K, &O::Value) {
        let x = self.nth_ptr(n).as_longlife_ref();
        (&x.key, &x.value)
    }

    pub fn nth_mut(&mut self, n: usize) -> (&K, &mut O::Value) {
        let x = self.nth_ptr(n).as_longlife_mut();
        (&x.key, &mut x.value)
    }

    pub fn binary_search<Q: ?Sized + Ord>(&self, key: &Q) -> Result<(&O::Value, usize), usize>
    where
        K: Ord + Borrow<Q>,
    {
        self.binary_search_ptr(key)
            .map(|(x, i)| (&x.as_longlife_ref().value, i))
    }

    pub fn partition_point(&self, mut f: impl FnMut(&K) -> bool) -> usize {
        let Some(mut x) = self.tree.root else { return 0 };
        let mut index = 0;
        loop {
            x = if f(&x.key) {
                index += len(x.left) + 1;
                let Some(right) = x.right else {
                    break;
                };
                right
            } else {
                let Some(left) = x.left else {
                    break;
                };
                left
            };
        }
        index
    }

    pub fn lower_bound(&self, key: &K) -> usize {
        self.partition_point(|x| x < key)
    }

    pub fn upper_bound(&self, key: &K) -> usize {
        self.partition_point(|x| x <= key)
    }

    pub fn insert(&mut self, key: K, value: O::Value) {
        let mut new = Ptr::new(Node::new(key, value, Color::Red));
        let Some(mut x) = self.tree.root else {
            new.color = Color::Black;
            self.tree.root = Some(new);
            self.tree.black_height = 1;
            return;
        };
        let key = &new.key;
        loop {
            match key.cmp(&x.key) {
                Ordering::Less | Ordering::Equal => {
                    if let Some(left) = x.left {
                        x = left;
                    } else {
                        new.parent = Some(x);
                        x.left = Some(new);
                        break;
                    }
                }
                Ordering::Greater => {
                    if let Some(right) = x.right {
                        x = right;
                    } else {
                        new.parent = Some(x);
                        x.right = Some(new);
                        break;
                    }
                }
            }
        }
        if x.color == Color::Red {
            self.tree.fix_red(new);
        } else {
            new.update_ancestors();
        }
    }

    pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<(K, O::Value)>
    where
        K: Ord + Borrow<Q>,
    {
        let x = self.binary_search_ptr(key).ok()?.0;
        self.remove_ptr(x);
        let x = x.free();
        Some((x.key, x.value))
    }

    pub fn remove_nth(&mut self, n: usize) -> (K, O::Value) {
        let x = self.nth_ptr(n);
        self.remove_ptr(x);
        let x = x.free();
        (x.key, x.value)
    }

    fn nth_ptr(&self, mut n: usize) -> Ptr<Node<K, O>> {
        assert!(
            n < self.len(),
            "Index out of range: n = {n}, while len = {}",
            self.len()
        );
        let mut x = self.tree.root.unwrap();
        loop {
            let left_len = len(x.left);
            x = match n.cmp(&left_len) {
                Ordering::Less => x.left.unwrap(),
                Ordering::Equal => break,
                Ordering::Greater => {
                    n -= left_len + 1;
                    x.right.unwrap()
                }
            };
        }
        x
    }

    pub fn binary_search_ptr<Q: ?Sized + Ord>(
        &self,
        key: &Q,
    ) -> Result<(Ptr<Node<K, O>>, usize), usize>
    where
        K: Ord + Borrow<Q>,
    {
        let mut x = self.tree.root.ok_or(0usize)?;
        let mut index = 0;
        loop {
            x = match key.cmp(x.key.borrow()) {
                Ordering::Less => x.left.ok_or(index)?,
                Ordering::Greater => {
                    index += len(x.left) + 1;
                    x.right.ok_or(index)?
                }
                Ordering::Equal => break,
            }
        }
        Ok((x, index + len(x.left)))
    }

    fn remove_ptr(&mut self, x: Ptr<Node<K, O>>) {
        let needs_fix;
        let black_vio;
        match (x.left, x.right) {
            (Some(_), Some(top)) => {
                let mut next = top;
                while let Some(left) = next.left {
                    next = left;
                }
                needs_fix = next.color == Color::Black;
                next.left = x.left;
                x.left.unwrap().parent = Some(next);
                next.color = x.color;
                if top == next {
                    black_vio = BlackViolation {
                        p: Some(next),
                        x: next.right,
                    };
                    self.tree.transplant(x, Some(next));
                } else {
                    black_vio = BlackViolation {
                        p: next.parent,
                        x: next.right,
                    };
                    self.tree.transplant(next, next.right);
                    next.right = x.right;
                    if let Some(mut r) = next.right {
                        r.parent = Some(next);
                    }
                    self.tree.transplant(x, Some(next));
                }
            }
            (None, Some(_)) => {
                needs_fix = x.color == Color::Black;
                black_vio = BlackViolation {
                    p: x.parent,
                    x: x.right,
                };
                self.tree.transplant(x, x.right);
            }
            (_, None) => {
                needs_fix = x.color == Color::Black;
                black_vio = BlackViolation {
                    p: x.parent,
                    x: x.left,
                };
                self.tree.transplant(x, x.left);
            }
        }
        if needs_fix {
            self.tree.fix_black(black_vio);
        } else if let Some(mut p) = black_vio.p {
            p.update();
            p.update_ancestors();
        }
    }
}

impl<K: Ord, O: MultimapOp> Default for MultimapSeg<K, O> {
    fn default() -> Self {
        Self::new()
    }
}
impl<'a, K: Ord, O: MultimapOp> IntoIterator for &'a MultimapSeg<K, O> {
    type IntoIter = SegmapIter<'a, K, O>;
    type Item = (&'a K, &'a O::Value);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct SegmapIter<'a, K: Ord, O: MultimapOp> {
    start: Option<Ptr<Node<K, O>>>,
    end: Option<Ptr<Node<K, O>>>,
    len: usize,
    marker: PhantomData<&'a (K, O)>,
}
impl<'a, K: Ord, O: MultimapOp> Iterator for SegmapIter<'a, K, O> {
    type Item = (&'a K, &'a O::Value);

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let x = self.start.unwrap();
        self.start = x.next();
        self.len -= 1;
        let x = x.as_longlife_ref();
        Some((&x.key, &x.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}
impl<'a, K: Ord, O: MultimapOp> DoubleEndedIterator for SegmapIter<'a, K, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let x = self.end.unwrap();
        self.end = x.prev();
        self.len -= 1;
        let x = x.as_longlife_ref();
        Some((&x.key, &x.value))
    }
}
impl<'a, K: Ord, O: MultimapOp> ExactSizeIterator for SegmapIter<'a, K, O> {}

struct Nop<T>(PhantomData<T>);
impl<T> MultimapOp for Nop<T> {
    type Acc = ();
    type Value = T;

    fn to_acc(_value: &Self::Value) -> Self::Acc {}

    fn join(
        _lhs: Option<&Self::Acc>,
        _center: &Self::Value,
        _rhs: Option<&Self::Acc>,
    ) -> Self::Acc {
    }
}

pub struct Multimap<K, V> {
    segmap: MultimapSeg<K, Nop<V>>,
}
impl<K: Ord, V> Multimap<K, V> {
    pub fn new() -> Self {
        Self {
            segmap: MultimapSeg::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.segmap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.segmap.is_empty()
    }

    pub fn iter(&self) -> MultimapIter<'_, K, V> {
        MultimapIter {
            iter: self.segmap.iter(),
        }
    }

    pub fn nth(&self, n: usize) -> (&K, &V) {
        self.segmap.nth(n)
    }

    pub fn binary_search<Q: ?Sized + Ord>(&self, key: &Q) -> Result<(&V, usize), usize>
    where
        K: Ord + Borrow<Q>,
    {
        self.segmap.binary_search(key)
    }

    pub fn partition_point(&self, f: impl FnMut(&K) -> bool) -> usize {
        self.segmap.partition_point(f)
    }

    pub fn lower_bound(&self, key: &K) -> usize {
        self.segmap.lower_bound(key)
    }

    pub fn upper_bound(&self, key: &K) -> usize {
        self.segmap.upper_bound(key)
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.segmap.insert(key, value);
    }

    pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Ord + Borrow<Q>,
    {
        self.segmap.remove(key)
    }

    pub fn remove_nth(&mut self, n: usize) -> (K, V) {
        self.segmap.remove_nth(n)
    }
}
impl<K: Ord, V> Default for Multimap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for Multimap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
impl<'a, K: Ord, V> IntoIterator for &'a Multimap<K, V> {
    type IntoIter = MultimapIter<'a, K, V>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
pub struct MultimapIter<'a, K: Ord, V> {
    iter: SegmapIter<'a, K, Nop<V>>,
}
impl<'a, K: Ord, V> Iterator for MultimapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
impl<'a, K: Ord, V> DoubleEndedIterator for MultimapIter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}
impl<'a, K: Ord, V> ExactSizeIterator for MultimapIter<'a, K, V> {}

pub struct Multiset<K> {
    map: Multimap<K, ()>,
}
impl<K: Ord> Multiset<K> {
    pub fn new() -> Self {
        Self {
            map: Multimap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn iter(&self) -> MultisetIter<'_, K> {
        MultisetIter {
            iter: self.map.iter(),
        }
    }

    pub fn nth(&self, n: usize) -> &K {
        self.map.nth(n).0
    }

    pub fn binary_search<Q: ?Sized + Ord>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Ord + Borrow<Q>,
    {
        self.map.binary_search(key).map(|((), i)| i)
    }

    pub fn partition_point(&self, f: impl FnMut(&K) -> bool) -> usize {
        self.map.partition_point(f)
    }

    pub fn lower_bound(&self, key: &K) -> usize {
        self.map.lower_bound(key)
    }

    pub fn upper_bound(&self, key: &K) -> usize {
        self.map.upper_bound(key)
    }

    pub fn insert(&mut self, key: K) {
        self.map.insert(key, ());
    }

    pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<K>
    where
        K: Ord + Borrow<Q>,
    {
        self.map.remove(key).map(|(k, ())| k)
    }

    pub fn remove_nth(&mut self, n: usize) -> K {
        self.map.remove_nth(n).0
    }
}
impl<K: Ord> Default for Multiset<K> {
    fn default() -> Self {
        Self::new()
    }
}
impl<K: Ord + fmt::Debug> fmt::Debug for Multiset<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}
impl<'a, K: Ord> IntoIterator for &'a Multiset<K> {
    type IntoIter = MultisetIter<'a, K>;
    type Item = &'a K;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
pub struct MultisetIter<'a, K: Ord> {
    iter: MultimapIter<'a, K, ()>,
}
impl<'a, K: Ord> Iterator for MultisetIter<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, ())| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
impl<'a, K: Ord> DoubleEndedIterator for MultisetIter<'a, K> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, ())| k)
    }
}
impl<'a, K: Ord> ExactSizeIterator for MultisetIter<'a, K> {}

#[cfg(test)]
mod test_multiset {
    use crate::balance::test_utils::Violations;
    use crate::balance::Ptr;
    use crate::map::len;
    use crate::map::Node;
    use crate::map::Nop;
    use crate::Multiset;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn to_vec<K: Ord + Clone>(set: &Multiset<K>) -> Vec<K> {
        set.map
            .segmap
            .tree
            .collect()
            .into_iter()
            .map(|x| x.key.clone())
            .collect()
    }

    impl Multiset<i32> {
        fn validate_len(&self) {
            fn validate_len(p: Option<Ptr<Node<i32, Nop<()>>>>) -> Result<(), String> {
                if let Some(p) = p {
                    validate_len(p.left)?;
                    let expected = len(p.left) + 1 + len(p.right);
                    (p.len == expected).then_some(()).ok_or_else(|| {
                        format!(
                            "Len is incorrect at {:?}. Expected {}, but cached {}",
                            p, expected, p.len
                        )
                    })?;
                    validate_len(p.right)?;
                }
                Ok(())
            }
            validate_len(self.map.segmap.tree.root).unwrap_or_else(|e| {
                panic!(
                    "{e}:\n Tree: {}",
                    self.map
                        .segmap
                        .tree
                        .format_by(|p| format!("<{:?}:{}>", p, p.len))
                )
            });
        }
    }

    #[test]
    fn test_insert_remove_nth() {
        const VALUE_LIM: i32 = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..10 {
            let mut set = Multiset::new();
            let mut vec = Vec::new();
            for _ in 0..200 {
                // Mutation
                match rng.gen_range(0..4) {
                    // Insert
                    0 | 1 => {
                        let key = rng.gen_range(0..VALUE_LIM);
                        set.insert(key);
                        let i = vec.binary_search(&key).unwrap_or_else(|i| i);
                        vec.insert(i, key);
                    }
                    // Remove
                    2 => {
                        let key = rng.gen_range(0..VALUE_LIM);
                        let result = set.remove(&key);
                        let expected = vec.binary_search(&key).ok().map(|i| vec.remove(i));
                        assert_eq!(result, expected);
                    }
                    // Remove nth
                    3 => {
                        if !vec.is_empty() {
                            let i = rng.gen_range(0..vec.len());
                            let result = set.remove_nth(i);
                            let expected = vec.remove(i);
                            assert_eq!(result, expected);
                        }
                    }
                    _ => unreachable!(),
                }
                assert_eq!(to_vec(&set), vec);

                set.map.segmap.tree.validate();
                assert_eq!(
                    Violations::collect(&set.map.segmap.tree),
                    Violations::default()
                );
                set.validate_len();

                // Nth query
                for (i, &expected) in vec.iter().enumerate() {
                    let result = *set.nth(i);
                    assert_eq!(result, expected);
                }

                // Binary search queries
                for x in 0..VALUE_LIM {
                    let result = set.binary_search(&x);
                    match result {
                        Ok(i) => assert_eq!(vec[i], x),
                        Err(i) => {
                            assert!(i == vec.len() || vec[i] > x);
                            assert!(i == 0 || vec[i - 1] < x);
                        }
                    }

                    assert_eq!(
                        set.lower_bound(&x),
                        vec.iter().position(|&y| y >= x).unwrap_or(vec.len())
                    );
                    assert_eq!(
                        set.upper_bound(&x),
                        vec.iter().position(|&y| y > x).unwrap_or(vec.len())
                    );
                }

                // Collect query
                assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec);
            }
        }
    }
}
