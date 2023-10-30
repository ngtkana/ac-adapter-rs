#![allow(missing_docs, dead_code, unused_variables)]
use crate::tree::Callback;
use crate::tree::Node;
use crate::tree::Ptr;
use crate::tree::Tree;
use crate::Op;
use std::borrow::Borrow;
use std::fmt;
use std::marker::PhantomData;

pub struct SegMap<K, O: Op> {
    pub(super) tree: Tree<SocCallback<K, O>>,
}
impl<K, O: Op> SegMap<K, O> {
    pub fn new() -> Self { Self { tree: Tree::new() } }

    pub fn is_empty(&self) -> bool { self.tree.is_empty() }

    pub fn len(&self) -> usize { self.tree.root.map_or(0, |root| root.data.len) }

    pub fn iter(&self) -> Iter<'_, K, O> {
        Iter {
            marker: PhantomData,
            start: self.get_nth(0),
            end: self.get_nth(self.len()),
            len: self.len(),
        }
    }

    pub fn remove_nth(&mut self, i: usize) -> (K, O::Value) {
        assert!(i < self.len(), "index out of bounds");
        let p = self.get_nth(i).unwrap();
        if let Some(b) = self.tree.remove(p) {
            // Case 1: `b.prev` -- `b` -- `p` -- `p.next`
            if b.data.next.unwrap() == p {
                let next = p.data.next;
                let mut prev = b.data.prev.unwrap();
                prev.data.next = next;
                if let Some(mut next) = next {
                    next.data.prev = Some(prev);
                }
            }
            // Case 2: `p.prev` -- `p` -- `b` -- `b.next`
            else {
                let prev = p.data.prev;
                let mut next = b.data.next.unwrap();
                next.data.prev = prev;
                if let Some(mut prev) = prev {
                    prev.data.next = Some(next);
                }
            }
            b.free();
        }
        let data = p.free();
        (data.key.unwrap(), data.value)
    }

    pub fn nth(&self, i: usize) -> (&K, &O::Value) {
        assert!(i < self.len(), "index out of bounds");
        let p = self.get_nth(i).unwrap().as_longlife_ref();
        (p.data.key.as_ref().unwrap(), &p.data.value)
    }

    /// Returns the `i`th leaf pointer if `i < self.data.len`, and the rightmost leaf pointer otherwise or `None` if the seg is empty.
    fn get_nth(&self, mut i: usize) -> Option<Ptr<SocCallback<K, O>>> {
        Some(self.tree.root?.binary_search_for_leaf(|b| {
            let left_len = b.left.unwrap().data.len;
            if left_len <= i {
                i -= left_len;
                true
            } else {
                false
            }
        }))
    }
}

impl<K, O: Op> SegMap<K, O>
where
    K: Ord,
{
    pub fn partition_point(&self, f: impl Fn(&K) -> bool) -> usize {
        let Some(root) = self.tree.root else {
            return 0;
        };
        let mut i = 0;
        let p = root.binary_search_for_leaf(|p| {
            if f(p.data.prev.as_ref().unwrap().data.key.as_ref().unwrap()) {
                i += p.left.unwrap().data.len;
                true
            } else {
                false
            }
        });
        if f(p.data.key.as_ref().unwrap()) {
            i += 1;
        }
        i
    }

    pub fn lower_bound<Q: Borrow<K>>(&self, b: &Q) -> usize {
        self.partition_point(|k| k < b.borrow())
    }

    pub fn upper_bound<Q: Borrow<K>>(&self, b: &Q) -> usize {
        self.partition_point(|k| k <= b.borrow())
    }

    /// Insert a new key-value pair at the *lower-bound* position of the key.
    pub fn insert(&mut self, key: K, value: O::Value) {
        let mut x = Ptr::<SocCallback<K, O>>::new_leaf(Data::new(key, value));
        let key = x.data.key.as_ref().unwrap();
        let Some(mut p) = self.get_lower_bound(key) else {
            self.tree.insert(None, x, Data::mul);
            return;
        };
        let result = p.data.key.as_ref().unwrap() < key;
        let mut b = self.tree.insert(Some((p, result)), x, Data::mul).unwrap();
        // Case 1: `p` -- `b` -- `x` -- `p.next`
        if result {
            x.data.next = p.data.next;
            if let Some(mut next) = p.data.next {
                next.data.prev = Some(x);
            }
            x.data.prev = Some(b);
            b.data.next = Some(x);
            b.data.prev = Some(p);
            p.data.next = Some(b);
        }
        // Case 2: `p.prev` -- `x` -- `b` -- `p`
        else {
            x.data.prev = p.data.prev;
            if let Some(mut prev) = p.data.prev {
                prev.data.next = Some(x);
            }
            x.data.next = Some(b);
            b.data.prev = Some(x);
            b.data.next = Some(p);
            p.data.prev = Some(b);
        }
    }

    fn get_lower_bound(&self, key: &K) -> Option<Ptr<SocCallback<K, O>>> {
        Some(self.tree.root?.binary_search_for_leaf(|b| {
            b.data.prev.as_ref().unwrap().data.key.as_ref().unwrap() < key
        }))
    }
}

impl<K, O: Op> Default for SegMap<K, O> {
    fn default() -> Self { Self::new() }
}

/// An iterator over the seg.
/// TODO: this is same as one in `seg.rs`.
pub struct Iter<'a, K, O: Op> {
    marker: PhantomData<&'a (K, O)>,
    start: Option<Ptr<SocCallback<K, O>>>,
    end: Option<Ptr<SocCallback<K, O>>>,
    len: usize,
}
impl<'a, K, O: Op> Iterator for Iter<'a, K, O> {
    type Item = (&'a K, &'a O::Value);

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start?;
        self.len -= 1;
        if self.len == 0 {
            self.start = None;
            self.end = None;
        } else {
            self.start = start.max_right(|_| false);
        }
        let start = start.as_longlife_ref();
        Some((start.data.key.as_ref().unwrap(), &start.data.value))
    }

    /// `advance_by` is better, but it is unstable now
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if n == 0 {
            return self.next();
        }
        if self.len <= n {
            self.start = None;
            self.end = None;
            self.len = 0;
            None
        } else {
            self.len -= n + 1;
            let mut i = n - 1;
            let start = self
                .start
                .unwrap()
                .max_right(|data| {
                    if i < data.len {
                        false
                    } else {
                        i -= data.len;
                        true
                    }
                })
                .unwrap();
            if self.len == 0 {
                self.start = None;
                self.end = None;
            } else {
                self.start = Some(start.max_right(|_| false).unwrap());
            }
            let start = start.as_longlife_ref();
            Some((start.data.key.as_ref().unwrap(), &start.data.value))
        }
    }
}
impl<'a, K, O: Op> DoubleEndedIterator for Iter<'a, K, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let end = self.end?;
        self.len -= 1;
        if self.len == 0 {
            self.start = None;
            self.end = None;
        } else {
            self.end = end.min_left(|_| false);
        }
        let end = end.as_longlife_ref();
        Some((end.data.key.as_ref().unwrap(), &end.data.value))
    }

    /// `advance_back_by` is better, but it is unstable now
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if n == 0 {
            return self.next_back();
        }
        if self.len <= n {
            self.start = None;
            self.end = None;
            self.len = 0;
            None
        } else {
            self.len -= n + 1;
            let mut i = n - 1;
            let end = self
                .end
                .unwrap()
                .min_left(|data| {
                    if i < data.len {
                        false
                    } else {
                        i -= data.len;
                        true
                    }
                })
                .unwrap();
            if self.len == 0 {
                self.start = None;
                self.end = None;
            } else {
                self.end = Some(end.min_left(|_| false).unwrap());
            }
            let end = end.as_longlife_ref();
            Some((end.data.key.as_ref().unwrap(), &end.data.value))
        }
    }
}
impl<'a, K, O: Op> ExactSizeIterator for Iter<'a, K, O> {
    fn len(&self) -> usize { self.len }
}
impl<'a, K, O: Op> IntoIterator for &'a SegMap<K, O> {
    type IntoIter = Iter<'a, K, O>;
    type Item = (&'a K, &'a O::Value);

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

impl<K, O: Op> fmt::Debug for SegMap<K, O>
where
    K: fmt::Debug,
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

pub(super) struct SocCallback<K, O> {
    marker: PhantomData<(K, O)>,
}
impl<K, O: Op> Callback for SocCallback<K, O> {
    type Data = Data<K, O>;

    fn update(x: &mut Node<Self>) {
        debug_assert!(O::is_identity(&x.data.lazy));
        x.data.len = x.left.unwrap().data.len + x.right.unwrap().data.len;
        x.data.value = O::mul(&x.left.unwrap().data.value, &x.right.unwrap().data.value);
    }

    fn push(_: &mut Node<Self>) {}
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct Data<K, O: Op> {
    // TODO: Use `LinkedList`?
    prev: Option<Ptr<SocCallback<K, O>>>,
    next: Option<Ptr<SocCallback<K, O>>>,
    len: usize,
    pub(super) key: Option<K>,
    value: O::Value,
    lazy: O::Lazy,
}
impl<K, O: Op> Data<K, O> {
    fn new(key: K, value: O::Value) -> Self {
        Self {
            prev: None,
            next: None,
            len: 1,
            key: Some(key),
            value,
            lazy: O::identity(),
        }
    }

    fn mul(left: &Self, right: &Self) -> Self {
        // TODO: set `prev` and `next`
        Self {
            prev: None,
            next: None,
            len: left.len + right.len,
            key: None,
            value: O::mul(&left.value, &right.value),
            lazy: O::identity(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::validate;
    use crate::test_util::validate_base;
    use crate::test_util::visit_nodes;
    use crate::test_util::Concat;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::fmt;

    fn validate_soc<K, O: Op>(soc: &SegMap<K, O>)
    where
        K: Clone + Ord + fmt::Debug,
        O::Value: Clone + fmt::Debug,
    {
        validate_base(&soc.tree, |p| {
            if !p.is_leaf() {
                (p.data.key.is_none()).then_some(()).ok_or_else(|| {
                    format!("key at the internal node {:?} is Some: {:?}", p, p.data.key,)
                })?;
                let prev = p
                    .data
                    .prev
                    .ok_or_else(|| format!("prev at internal node {:?} is None", p,))?;
                let next = p
                    .data
                    .next
                    .ok_or_else(|| format!("next at internal node {:?} is None", p,))?;
                (prev.is_leaf())
                    .then_some(())
                    .ok_or_else(|| format!("prev at internal node {:?} is not a leaf", p,))?;
                (next.is_leaf())
                    .then_some(())
                    .ok_or_else(|| format!("next at internal node {:?} is not a leaf", p,))?;
                (prev.data.next == Some(p)).then_some(()).ok_or_else(|| {
                    format!(
                        "next {:?} of prev {:?} at internal node {:?} is not the node itself",
                        prev.data.next, prev, p,
                    )
                })?;
                (next.data.prev == Some(p)).then_some(()).ok_or_else(|| {
                    format!(
                        "prev {:?} of next {:?} at internal node {:?} is not the node itself",
                        next.data.prev, next, p,
                    )
                })?;
                (prev.data.key.as_ref().unwrap() <= next.data.key.as_ref().unwrap())
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "{:?}'s prev {:?}({:?}) is less than next {:?}({:?}):\n{:?}",
                            p,
                            prev,
                            prev.data.key.as_ref().unwrap(),
                            next,
                            next.data.key.as_ref().unwrap(),
                            &soc,
                        )
                    })?;
            }
            Ok(())
        })
    }

    fn to_vec<K, O: Op>(soc: &SegMap<K, O>) -> Vec<(K, O::Value)>
    where
        K: Clone,
        O::Value: Clone,
    {
        let mut result = Vec::new();
        visit_nodes(&soc.tree, |p| {
            if p.is_leaf() {
                result.push((p.data.key.clone().unwrap(), p.data.value.clone()));
            }
        });
        result
    }

    #[test]
    fn test_insert_lower_bound_upper_bound() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut map = SegMap::<u64, Concat>::new();
            let mut vec = Vec::new();

            for _ in 0..20 {
                match rng.gen_range(0..4) {
                    // Insert
                    0 => {
                        let key = rng.gen_range(0..20);
                        let value = vec![rng.gen_range(0..20)];
                        let i = vec.partition_point(|&(k, _)| k < key);
                        vec.insert(i, (key, value.clone()));
                        map.insert(key, value);
                    }
                    // Remove nth
                    1 => {
                        if vec.is_empty() {
                            continue;
                        }
                        let i = rng.gen_range(0..vec.len());
                        assert_eq!(vec.remove(i), map.remove_nth(i));
                    }
                    // Lower bound
                    2 => {
                        let key = rng.gen_range(0..20);
                        let i = vec.partition_point(|&(k, _)| k < key);
                        let result = map.lower_bound(&key);
                        assert_eq!(
                            i, result,
                            "lower_bound({:?}, {}) is expected to be {}, but actually {}",
                            &vec, key, i, result,
                        );
                    }
                    // Upper bound
                    3 => {
                        let value = rng.gen_range(0..20);
                        let i = vec.partition_point(|&(v, _)| v <= value);
                        let result = map.upper_bound(&value);
                        assert_eq!(
                            i, result,
                            "upper_bound({:?}, {}) is expected to be {}, but actually {}",
                            &vec, value, i, result,
                        );
                    }
                    _ => unreachable!(),
                }
                assert_eq!(vec, to_vec(&map));
                validate(&map.tree);
            }
        }
    }
}
