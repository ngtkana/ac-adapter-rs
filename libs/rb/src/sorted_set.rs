#![allow(dead_code, missing_docs, unused_imports, unused_variables)]
use crate::Op;
use crate::SegMap;
use std::borrow::Borrow;
use std::fmt;

pub struct SortedList<K> {
    map: SegMap<K, Nop>,
}
enum Nop {}
impl Op for Nop {
    type Lazy = ();
    type Value = ();

    fn mul(_: &Self::Value, _: &Self::Value) -> Self::Value {}

    fn apply(_: &mut Self::Value, _: &Self::Lazy) {}

    fn compose(_: &mut Self::Lazy, _: &Self::Lazy) {}

    fn identity() -> Self::Lazy {}
}
impl<K> SortedList<K> {
    pub fn new() -> Self { Self { map: SegMap::new() } }

    pub fn len(&self) -> usize { self.map.len() }

    pub fn is_empty(&self) -> bool { self.map.is_empty() }

    pub fn iter(&self) -> Iter<'_, K> {
        Iter {
            iter: self.map.iter(),
        }
    }

    pub fn nth(&self, n: usize) -> &K { self.map.nth(n).0 }

    pub fn remove_nth(&mut self, n: usize) -> K { self.map.remove_nth(n).0 }
}
impl<K: Ord> SortedList<K> {
    pub fn partition_point(&self, f: impl Fn(&K) -> bool) -> usize { self.map.partition_point(f) }

    pub fn lower_bound<Q: Borrow<K>>(&self, key: &Q) -> usize { self.map.lower_bound(key) }

    pub fn upper_bound<Q: Borrow<K>>(&self, key: &Q) -> usize { self.map.upper_bound(key) }

    pub fn insert(&mut self, key: K) { self.map.insert(key, ()); }
}

pub struct Iter<'a, K> {
    iter: crate::seg_map::Iter<'a, K, Nop>,
}
impl<'a, K> Iterator for Iter<'a, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> { self.iter.next().map(|(k, _)| k) }

    fn nth(&mut self, n: usize) -> Option<Self::Item> { self.iter.nth(n).map(|(k, _)| k) }
}
impl<'a, K> DoubleEndedIterator for Iter<'a, K> {
    fn next_back(&mut self) -> Option<Self::Item> { self.iter.next_back().map(|(k, _)| k) }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> { self.iter.nth_back(n).map(|(k, _)| k) }
}
impl<'a, K> ExactSizeIterator for Iter<'a, K> {
    fn len(&self) -> usize { self.iter.len() }
}
impl<'a, K> IntoIterator for &'a SortedList<K> {
    type IntoIter = Iter<'a, K>;
    type Item = &'a K;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

impl<K> fmt::Debug for SortedList<K>
where
    K: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::validate;
    use crate::test_util::visit_nodes;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn to_vec<K>(list: &SortedList<K>) -> Vec<K>
    where
        K: Clone,
    {
        let mut result = Vec::new();
        visit_nodes(&list.map.tree, |p| {
            if p.is_leaf() {
                result.push(p.data.key.clone().unwrap())
            }
        });
        result
    }

    #[test]
    fn test_insert_remove_lower_bound_upper_bound() {
        let mut rng = StdRng::seed_from_u64(43);
        for _ in 0..20 {
            let mut vec = Vec::new();
            let mut list = SortedList::new();
            for _ in 0..200 {
                match rng.gen_range(0..4) {
                    // Insert
                    0 => {
                        let value = rng.gen_range(0..20);
                        let i = vec.partition_point(|&v| v < value);
                        vec.insert(i, value);
                        list.insert(value);
                    }
                    // Remove nth
                    1 => {
                        if vec.is_empty() {
                            continue;
                        }
                        let i = rng.gen_range(0..vec.len());
                        assert_eq!(vec.remove(i), list.remove_nth(i));
                    }
                    // Lower bound
                    2 => {
                        let value = rng.gen_range(0..20);
                        let i = vec.partition_point(|&v| v < value);
                        assert_eq!(i, list.lower_bound(&value));
                    }
                    // Upper bound
                    3 => {
                        let value = rng.gen_range(0..20);
                        let i = vec.partition_point(|&v| v <= value);
                        assert_eq!(i, list.upper_bound(&value));
                    }
                    _ => unreachable!(),
                }
                assert_eq!(vec, to_vec(&list));
                validate(&list.map.tree);
            }
        }
    }
}
