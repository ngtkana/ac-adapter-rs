//! v1では未対応: entry, range/range_mut, append, split_off, retain, values_mut, into_iter

use std::borrow::Borrow;
use std::cell::Cell;
use std::fmt;
use std::ptr::NonNull;

pub struct OrderStatisticMap<K, V> {
    root: Cell<Option<NonNull<Node<K, V>>>>,
}

impl<K: Ord, V> OrderStatisticMap<K, V> {
    // Group A: Core API
    pub fn new() -> Self {
        Self {
            root: Cell::new(None),
        }
    }

    pub fn len(&self) -> usize {
        self.root.get().map_or(0, |r| unsafe { (*r.as_ptr()).len })
    }

    pub fn is_empty(&self) -> bool {
        self.root.get().is_none()
    }

    pub fn clear(&mut self) {
        free_subtree(self.root.get());
        self.root.set(None);
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.root.get() {
            None => {
                let node = Box::into_raw(Box::new(Node {
                    key,
                    value,
                    parent: None,
                    left: None,
                    right: None,
                    len: 1,
                }));
                self.root.set(Some(NonNull::new(node).unwrap()));
                None
            }
            Some(root) => unsafe {
                let mut current = root;
                loop {
                    let key_cmp = key.cmp(&(*current.as_ptr()).key);
                    match key_cmp {
                        std::cmp::Ordering::Less => {
                            if let Some(left) = (*current.as_ptr()).left {
                                current = left;
                            } else {
                                let new_node = Box::into_raw(Box::new(Node {
                                    key,
                                    value,
                                    parent: Some(current),
                                    left: None,
                                    right: None,
                                    len: 1,
                                }));
                                (*current.as_ptr()).left = Some(NonNull::new(new_node).unwrap());
                                current = NonNull::new(new_node).unwrap();
                                break;
                            }
                        }
                        std::cmp::Ordering::Greater => {
                            if let Some(right) = (*current.as_ptr()).right {
                                current = right;
                            } else {
                                let new_node = Box::into_raw(Box::new(Node {
                                    key,
                                    value,
                                    parent: Some(current),
                                    left: None,
                                    right: None,
                                    len: 1,
                                }));
                                (*current.as_ptr()).right = Some(NonNull::new(new_node).unwrap());
                                current = NonNull::new(new_node).unwrap();
                                break;
                            }
                        }
                        std::cmp::Ordering::Equal => {
                            let old_value =
                                std::mem::replace(&mut (*current.as_ptr()).value, value);
                            current = splay(current);
                            self.root.set(Some(current));
                            return Some(old_value);
                        }
                    }
                }
                current = splay(current);
                self.root.set(Some(current));
                None
            },
        }
    }

    pub fn remove<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|_| detach_root(self).1)
    }

    pub fn get<Q: Ord + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|node| unsafe { &(*node.as_ptr()).value })
    }

    pub fn contains_key<Q: Ord + ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).is_some()
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        let mut stack = Vec::new();
        if let Some(root) = self.root.get() {
            let mut current = Some(root);
            while let Some(c) = current {
                stack.push(c);
                current = unsafe { (*c.as_ptr()).left };
            }
        }
        Iter {
            stack,
            _phantom: std::marker::PhantomData,
        }
    }

    // Group B: Frequently used
    pub fn get_mut<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|node| unsafe { &mut (*node.as_ptr()).value })
    }

    pub fn get_key_value<Q: Ord + ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key)
            .map(|node| unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) })
    }

    pub fn remove_entry<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|_| detach_root(self))
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        leftmost_and_splay(self)
            .map(|node| unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) })
    }

    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        rightmost_and_splay(self)
            .map(|node| unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) })
    }

    pub fn pop_first(&mut self) -> Option<(K, V)> {
        leftmost_and_splay(self).map(|_| detach_root(self))
    }

    pub fn pop_last(&mut self) -> Option<(K, V)> {
        rightmost_and_splay(self).map(|_| detach_root(self))
    }

    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            inner: self.iter(),
        }
    }

    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            inner: self.iter(),
        }
    }

    // Group C: Order statistic
    pub fn nth(&self, n: usize) -> (&K, &V) {
        let node = nth_and_splay(self, n);
        unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) }
    }

    pub fn remove_nth(&mut self, n: usize) -> (K, V) {
        nth_and_splay(self, n);
        detach_root(self)
    }

    pub fn binary_search<Q: Ord + ?Sized>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
    {
        let (pos, found) = locate_and_splay(self, key, false);
        match found {
            Some(_) => Ok(pos),
            None => Err(pos),
        }
    }

    pub fn lower_bound<Q: Ord + ?Sized>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
    {
        locate_and_splay(self, key, false).0
    }

    pub fn upper_bound<Q: Ord + ?Sized>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
    {
        locate_and_splay(self, key, true).0
    }
}

impl<K: Ord, V> Default for OrderStatisticMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for OrderStatisticMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a, K: Ord, V> IntoIterator for &'a OrderStatisticMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for OrderStatisticMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = Self::new();
        map.extend(iter);
        map
    }
}

impl<K: Ord, V> Extend<(K, V)> for OrderStatisticMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K, V> Drop for OrderStatisticMap<K, V> {
    fn drop(&mut self) {
        free_subtree(self.root.get());
    }
}

pub struct Iter<'a, K, V> {
    stack: Vec<NonNull<Node<K, V>>>,
    _phantom: std::marker::PhantomData<&'a Node<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        unsafe {
            if let Some(right) = (*node.as_ptr()).right {
                let mut current = Some(right);
                while let Some(c) = current {
                    self.stack.push(c);
                    current = (*c.as_ptr()).left;
                }
            }
            Some((&(*node.as_ptr()).key, &(*node.as_ptr()).value))
        }
    }
}

pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

struct Node<K, V> {
    key: K,
    value: V,
    parent: Option<NonNull<Self>>,
    left: Option<NonNull<Self>>,
    right: Option<NonNull<Self>>,
    len: usize,
}

impl<K, V> Node<K, V> {
    fn update(&mut self) {
        unsafe {
            self.len = self.left.map_or(0, |left| (*left.as_ptr()).len)
                + 1
                + self.right.map_or(0, |rigth| (*rigth.as_ptr()).len);
        }
    }
}

fn splay<K, V>(x: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
    unsafe {
        while let Some(p) = (*x.as_ptr()).parent {
            if let Some(q) = (*p.as_ptr()).parent {
                if (*q.as_ptr()).left == Some(p) && (*p.as_ptr()).left == Some(x) {
                    // zig-zig: left-left
                    rotate_right(q);
                    rotate_right(p);
                } else if (*q.as_ptr()).right == Some(p) && (*p.as_ptr()).right == Some(x) {
                    // zig-zig: right-right
                    rotate_left(q);
                    rotate_left(p);
                } else {
                    // zig-zag
                    if (*p.as_ptr()).left == Some(x) {
                        rotate_right(p);
                    } else {
                        rotate_left(p);
                    }
                    if (*q.as_ptr()).left == Some(x) {
                        rotate_right(q);
                    } else {
                        rotate_left(q);
                    }
                }
            } else {
                // zig: parent is root
                if (*p.as_ptr()).left == Some(x) {
                    rotate_right(p);
                } else if (*p.as_ptr()).right == Some(x) {
                    rotate_left(p);
                } else {
                    unreachable!()
                }
            }
        }
        x
    }
}

fn rotate_left<K, V>(x: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
    unsafe {
        let y = (*x.as_ptr()).right.unwrap();
        let c = (*y.as_ptr()).left;

        (*x.as_ptr()).right = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).left = Some(x);

        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);

        (*x.as_ptr()).update();
        (*y.as_ptr()).update();

        y
    }
}

fn rotate_right<K, V>(x: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
    unsafe {
        let y = (*x.as_ptr()).left.unwrap();
        let c = (*y.as_ptr()).right;

        (*x.as_ptr()).left = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).right = Some(x);

        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);

        (*x.as_ptr()).update();
        (*y.as_ptr()).update();

        y
    }
}

fn free_subtree<K, V>(root: Option<NonNull<Node<K, V>>>) {
    let mut stack = Vec::new();
    if let Some(r) = root {
        stack.push(r);
    }
    while let Some(node) = stack.pop() {
        unsafe {
            if let Some(left) = (*node.as_ptr()).left {
                stack.push(left);
            }
            if let Some(right) = (*node.as_ptr()).right {
                stack.push(right);
            }
            drop(Box::from_raw(node.as_ptr()));
        }
    }
}

fn find_and_splay<K, Q: Ord + ?Sized, V>(
    map: &OrderStatisticMap<K, V>,
    key: &Q,
) -> Option<NonNull<Node<K, V>>>
where
    K: Ord + Borrow<Q>,
{
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            let mut found = false;
            loop {
                let key_cmp = key.cmp((*current.as_ptr()).key.borrow());
                match key_cmp {
                    std::cmp::Ordering::Less => {
                        if let Some(left) = (*current.as_ptr()).left {
                            current = left;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        if let Some(right) = (*current.as_ptr()).right {
                            current = right;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        found = true;
                        break;
                    }
                }
            }
            current = splay(current);
            map.root.set(Some(current));
            if found { Some(current) } else { None }
        },
    }
}

fn nth_and_splay<K, V>(map: &OrderStatisticMap<K, V>, mut n: usize) -> NonNull<Node<K, V>> {
    let root = map.root.get().unwrap();
    unsafe {
        let mut current = root;
        loop {
            let left_len = (*current.as_ptr()).left.map_or(0, |l| (*l.as_ptr()).len);
            match n.cmp(&left_len) {
                std::cmp::Ordering::Less => {
                    current = (*current.as_ptr()).left.unwrap();
                }
                std::cmp::Ordering::Greater => {
                    n -= left_len + 1;
                    current = (*current.as_ptr()).right.unwrap();
                }
                std::cmp::Ordering::Equal => {
                    break;
                }
            }
        }
        current = splay(current);
        map.root.set(Some(current));
        current
    }
}

fn locate_and_splay<K, Q: Ord + ?Sized, V>(
    map: &OrderStatisticMap<K, V>,
    key: &Q,
    include_equal: bool,
) -> (usize, Option<NonNull<Node<K, V>>>)
where
    K: Ord + Borrow<Q>,
{
    match map.root.get() {
        None => (0, None),
        Some(root) => unsafe {
            let mut current = root;
            let mut pos = 0;
            let mut found_node = None;

            loop {
                let left_len = (*current.as_ptr()).left.map_or(0, |l| (*l.as_ptr()).len);
                let key_cmp = key.cmp((*current.as_ptr()).key.borrow());
                match key_cmp {
                    std::cmp::Ordering::Less => {
                        if let Some(left) = (*current.as_ptr()).left {
                            current = left;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        pos += left_len + 1;
                        if let Some(right) = (*current.as_ptr()).right {
                            current = right;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        pos += left_len;
                        found_node = Some(current);
                        if include_equal {
                            pos += 1;
                            if let Some(right) = (*current.as_ptr()).right {
                                current = right;
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
            current = splay(current);
            map.root.set(Some(current));
            (pos, found_node)
        },
    }
}

fn leftmost_and_splay<K, V>(map: &OrderStatisticMap<K, V>) -> Option<NonNull<Node<K, V>>> {
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            while let Some(left) = (*current.as_ptr()).left {
                current = left;
            }
            current = splay(current);
            map.root.set(Some(current));
            Some(current)
        },
    }
}

fn rightmost_and_splay<K, V>(map: &OrderStatisticMap<K, V>) -> Option<NonNull<Node<K, V>>> {
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            while let Some(right) = (*current.as_ptr()).right {
                current = right;
            }
            current = splay(current);
            map.root.set(Some(current));
            Some(current)
        },
    }
}

fn detach_root<K, V>(map: &mut OrderStatisticMap<K, V>) -> (K, V) {
    let root = map.root.get().unwrap();
    unsafe {
        let (key, value) = (
            std::ptr::read(&raw const (*root.as_ptr()).key),
            std::ptr::read(&raw const (*root.as_ptr()).value),
        );

        let left = (*root.as_ptr()).left;
        let right = (*root.as_ptr()).right;

        // Merge left and right subtrees
        let new_root = match (left, right) {
            (None, None) => None,
            (Some(l), None) => {
                (*l.as_ptr()).parent = None;
                Some(l)
            }
            (None, Some(r)) => {
                (*r.as_ptr()).parent = None;
                Some(r)
            }
            (Some(l), Some(r)) => {
                // Find the maximum of left and make it connect to right
                // Walk to the rightmost node of l (which should have no right child)
                let mut curr = l;
                while let Some(next) = (*curr.as_ptr()).right {
                    curr = next;
                }
                // curr is the maximum of the left subtree
                // Attach right as its right child
                (*curr.as_ptr()).right = Some(r);
                (*r.as_ptr()).parent = Some(curr);
                (*curr.as_ptr()).update();

                // Make l the new root
                (*l.as_ptr()).parent = None;
                Some(l)
            }
        };

        drop(Box::from_raw(root.as_ptr()));
        map.root.set(new_root);
        (key, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_insert_remove_nth_random() {
        const VALUE_LIM: i32 = 200;
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..200 {
            let n = rng.gen_range(1..=200);
            let q = rng.gen_range(0..=200);

            let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
            let mut vec: Vec<(i32, i32)> = Vec::new();

            for _ in 0..q {
                let op_type = rng.gen_range(0..5);
                match op_type {
                    0 | 1 => {
                        // insert
                        let key = rng.gen_range(0..n);
                        let value = rng.gen_range(0..VALUE_LIM);
                        map.insert(key, value);
                        if let Some(pos) = vec.iter().position(|(k, _)| k == &key) {
                            vec[pos] = (key, value);
                        } else {
                            let idx = vec.iter().position(|(k, _)| k > &key).unwrap_or(vec.len());
                            vec.insert(idx, (key, value));
                        }
                    }
                    2 => {
                        // remove or remove_entry
                        let key = rng.gen_range(0..n);
                        if rng.gen_bool(0.5) {
                            map.remove(&key);
                            vec.retain(|(k, _)| k != &key);
                        } else {
                            map.remove_entry(&key);
                            vec.retain(|(k, _)| k != &key);
                        }
                    }
                    3 => {
                        // remove_nth
                        if !vec.is_empty() {
                            let idx = rng.gen_range(0..vec.len());
                            map.remove_nth(idx);
                            vec.remove(idx);
                        }
                    }
                    4 => {
                        // pop_first or pop_last
                        if !vec.is_empty() {
                            if rng.gen_bool(0.5) {
                                map.pop_first();
                                vec.remove(0);
                            } else {
                                map.pop_last();
                                vec.pop();
                            }
                        }
                    }
                    _ => unreachable!(),
                }

                // Verify invariants
                assert_eq!(map.len(), vec.len(), "Length mismatch");
                assert_eq!(map.is_empty(), vec.is_empty(), "Empty mismatch");

                if vec.is_empty() {
                    assert_eq!(map.first_key_value(), None);
                    assert_eq!(map.last_key_value(), None);
                } else {
                    assert_eq!(
                        map.first_key_value(),
                        Some((&vec[0].0, &vec[0].1)),
                        "First key-value mismatch"
                    );
                    assert_eq!(
                        map.last_key_value(),
                        Some((&vec[vec.len() - 1].0, &vec[vec.len() - 1].1)),
                        "Last key-value mismatch"
                    );
                }

                let collected: Vec<_> = map.iter().collect();
                let expected: Vec<_> = vec.iter().map(|(k, v)| (k, v)).collect();
                assert_eq!(collected, expected, "iter() mismatch");

                for (i, expected_kv) in vec.iter().enumerate() {
                    assert_eq!(map.nth(i), (&expected_kv.0, &expected_kv.1), "nth({i}) mismatch");
                }

                // Query: get, get_key_value, contains_key, binary_search, lower_bound, upper_bound
                for key in 0..n {
                    let expected_get = vec.iter().find(|(k, _)| k == &key).map(|(_, v)| v);
                    assert_eq!(map.get(&key), expected_get, "get({key}) mismatch");

                    let expected_get_key_value =
                        vec.iter().find(|(k, _)| k == &key).map(|(k, v)| (k, v));
                    assert_eq!(
                        map.get_key_value(&key),
                        expected_get_key_value,
                        "get_key_value({key}) mismatch"
                    );

                    let expected_contains = vec.iter().any(|(k, _)| k == &key);
                    assert_eq!(
                        map.contains_key(&key),
                        expected_contains,
                        "contains_key({key}) mismatch"
                    );

                    let expected_binary_search = vec
                        .iter()
                        .position(|(k, _)| k == &key)
                        .ok_or_else(|| vec.iter().position(|(k, _)| k > &key).unwrap_or(vec.len()));
                    assert_eq!(
                        map.binary_search(&key),
                        expected_binary_search,
                        "binary_search({key}) mismatch"
                    );

                    let expected_lower_bound =
                        vec.iter().position(|(k, _)| k >= &key).unwrap_or(vec.len());
                    assert_eq!(
                        map.lower_bound(&key),
                        expected_lower_bound,
                        "lower_bound({key}) mismatch"
                    );

                    let expected_upper_bound =
                        vec.iter().position(|(k, _)| k > &key).unwrap_or(vec.len());
                    assert_eq!(
                        map.upper_bound(&key),
                        expected_upper_bound,
                        "upper_bound({key}) mismatch"
                    );
                }
            }
        }
    }

    #[test]
    fn test_default_clear_from_extend() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::default();
        assert!(map.is_empty());

        let data = vec![(1, 10), (2, 20), (3, 30)];
        map.extend(data.clone());
        assert_eq!(map.len(), 3);

        map.clear();
        assert!(map.is_empty());

        let map2: OrderStatisticMap<i32, i32> = data.into_iter().collect();
        assert_eq!(map2.len(), 3);
    }

    #[test]
    fn test_get_mut() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        map.insert(1, 10);
        map.insert(2, 20);

        if let Some(v) = map.get_mut(&1) {
            *v = 100;
        }

        assert_eq!(map.get(&1), Some(&100));
        assert_eq!(map.get(&2), Some(&20));
    }

    #[test]
    fn test_keys_values() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);

        let keys: Vec<_> = map.keys().collect();
        assert_eq!(keys.len(), 3);

        let values: Vec<_> = map.values().collect();
        assert_eq!(values.len(), 3);
    }

    #[test]
    fn test_simple_operations() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        assert_eq!(map.len(), 0);

        map.insert(2, 20);
        assert_eq!(map.len(), 1, "After insert 2");

        map.insert(1, 10);
        assert_eq!(map.len(), 2, "After insert 1");

        map.insert(3, 30);
        assert_eq!(map.len(), 3, "After insert 3");

        // Insert duplicate
        map.insert(2, 25);
        assert_eq!(map.len(), 3, "After duplicate insert");

        // Remove
        map.remove(&2);
        assert_eq!(map.len(), 2, "After remove");

        // Check iteration
        let collected: Vec<_> = map.iter().collect();
        assert_eq!(collected.len(), 2);
    }
}
