use super::tree::node;
use super::tree::Ptr;
use super::tree::Tree;
use super::Len;
use core::fmt;
use std::cmp::Ordering;
use std::hash::Hash;
use std::marker::PhantomData;

/// A list based on a red-black tree.
pub struct Rblist<T>(Tree<T, Len>);
impl<T> Rblist<T> {
    /// Creates a new empty list.
    pub fn new() -> Self { Self::default() }

    /// Returns the length of the list.
    // TODO: Stop accessing the root node directly.
    pub fn len(&self) -> usize { unsafe { self.0.root.as_ref().map_or(0, |n| n.cache) } }

    /// Returns `true` if the list is empty.
    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    /// Iterates over the list.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            __marker: PhantomData,
            ptr: self.0.front(),
        }
    }

    /// Provides a reference to the front element, or None if the list is empty.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let mut list = Rblist::new();
    /// assert_eq!(list.front(), None);
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// assert_eq!(list.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> { unsafe { Some(&(*self.0.front()?.inner()).value) } }

    /// Provides a mutable reference to the front element, or None if the list is empty.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let mut list = Rblist::new();
    /// assert_eq!(list.front(), None);
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// match list.front_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    ///
    /// assert_eq!(list.front(), Some(&9));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        unsafe { Some(&mut (*self.0.front()?.inner()).value) }
    }

    /// Provides a reference to the back element, or None if the list is empty.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let mut list = Rblist::new();
    /// assert_eq!(list.back(), None);
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// assert_eq!(list.back(), Some(&2));
    /// ```
    pub fn back(&self) -> Option<&T> { unsafe { Some(&(*self.0.back()?.inner()).value) } }

    /// Provides a mutable reference to the back element, or None if the list is empty.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let mut list = Rblist::new();
    /// assert_eq!(list.back(), None);
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// match list.back_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(list.back(), Some(&9));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        unsafe { Some(&mut (*self.0.back()?.inner()).value) }
    }

    /// Appends an element to the front of the list.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let mut list = Rblist::new();
    /// list.push_front(1);
    /// list.push_front(2);
    /// assert_eq!(list.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, element: T) {
        self.0.partition_point_insert(node(element, 1), |_| false);
    }

    /// Appends an element to the back of the list.
    pub fn push_back(&mut self, element: T) {
        self.0.partition_point_insert(node(element, 1), |_| true);
    }

    /// Removes the first element from the list and returns it, or None if it is empty.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let mut list = Rblist::new();
    /// list.push_back(1);
    /// list.push_back(2);
    /// assert_eq!(list.pop_front(), Some(1));
    /// assert_eq!(list.pop_front(), Some(2));
    /// assert_eq!(list.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        // TODO: Implement this to `Tree`.
        let removed = self.0.binary_search_remove(|n| {
            if n.left.is_null() {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        });
        unsafe { removed.as_mut().map(|n| Box::from_raw(n).value) }
    }

    /// Removes the last element from the list and returns it, or None if it is empty.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    /// let mut list = Rblist::new();
    /// list.push_back(1);
    /// list.push_back(2);
    /// assert_eq!(list.pop_back(), Some(2));
    /// assert_eq!(list.pop_back(), Some(1));
    /// assert_eq!(list.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        // TODO: Implement this to `Tree`.
        let removed = self.0.binary_search_remove(|n| {
            if n.right.is_null() {
                Ordering::Equal
            } else {
                Ordering::Less
            }
        });
        unsafe { removed.as_mut().map(|n| Box::from_raw(n).value) }
    }

    /// Inserts an element at position index within the vector, shifting all elements after it to the right.
    ///
    /// # Panics
    /// Panics if `index > len`.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let mut list: Rblist<_> = [0, 1, 2].into();
    /// list.insert(1, 9);
    ///
    /// assert_eq!(list, [0, 9, 1, 2].into());
    /// ```
    pub fn insert(&mut self, mut index: usize, element: T)
    where
        T: std::fmt::Display,
    {
        assert!(index <= self.len());
        self.0.partition_point_insert(node(element, 1), |n| {
            let len = unsafe { n.left.as_ref().map_or(0, |n| n.cache) };
            // Go to the left subtree.
            if index <= len {
                false
            }
            // Go to the right subtree.
            else {
                index -= len + 1;
                true
            }
        });
    }

    /// Removes and returns the element at position index within the vector, shifting all elements after it to the left.
    ///
    /// Note: Because this shifts over the remaining elements, it has a worst-case performance of O(n). If you don’t need the order of elements to be preserved, use swap_remove instead. If you’d like to remove elements from the beginning of the Vec, consider using VecDeque::pop_front instead.
    ///
    /// # Panics
    /// Panics if index is out of bounds.
    ///
    /// # Examples
    /// ```
    /// ```
    pub fn remove(&mut self, mut index: usize) -> T {
        assert!(index < self.len());
        let removed = self.0.binary_search_remove(|n| {
            let len = unsafe { n.left.as_ref().map_or(0, |n| n.cache) };
            match index.cmp(&len) {
                // Go to the left subtree.
                Ordering::Less => Ordering::Greater,
                // Remove the current node.
                Ordering::Equal => Ordering::Equal,
                // Go to the right subtree.
                Ordering::Greater => {
                    index -= len + 1;
                    Ordering::Less
                }
            }
        });
        unsafe { Box::from_raw(removed).value }
    }

    /// Binary searches this list with a comparator function.
    ///
    /// # Examples
    /// ```
    /// use rb::Rblist;
    ///
    /// let list: Rblist<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
    ///
    /// assert_eq!(list.binary_search_by(|x| x.cmp(&13)), Ok(9));
    /// assert_eq!(list.binary_search_by(|x| x.cmp(&4)), Err(7));
    /// assert_eq!(list.binary_search_by(|x| x.cmp(&100)), Err(13));
    /// let r = list.binary_search_by(|x| x.cmp(&1));
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        unsafe {
            let mut index = 0;
            let found = self.0.binary_search(|n| match f(&n.value) {
                Ordering::Less => {
                    index += 1 + n.left.as_ref().map_or(0, |n| n.cache);
                    Ordering::Less
                }
                Ordering::Equal => Ordering::Equal,
                Ordering::Greater => Ordering::Greater,
            });
            if found.is_none() {
                Err(index)
            } else {
                Ok(index
                    + (*found.unwrap().inner())
                        .left
                        .as_ref()
                        .map_or(0, |n| n.cache))
            }
        }
    }

    /// Binary searches this list with a key extraction function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rb::Rblist;
    ///
    /// let list: Rblist<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
    ///
    /// assert_eq!(list.binary_search(&13), Ok(9));
    /// assert_eq!(list.binary_search(&4), Err(7));
    /// assert_eq!(list.binary_search(&100), Err(13));
    /// let r = list.binary_search(&1);
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    pub fn binary_search_by_key<'a, F, B>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> B,
        B: Ord,
    {
        self.binary_search_by(|k| f(k).cmp(b))
    }

    /// Binary searches this list for a given element.
    ///
    /// # Examples
    ///
    /// ```
    /// use rb::Rblist;
    ///
    /// let list: Rblist<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
    ///
    /// assert_eq!(list.binary_search(&13), Ok(9));
    /// assert_eq!(list.binary_search(&4), Err(7));
    /// assert_eq!(list.binary_search(&100), Err(13));
    /// let r = list.binary_search(&1);
    /// assert!(matches!(r, Ok(1..=4)));
    /// ```
    pub fn binary_search(&self, x: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|k| k.cmp(x))
    }
}

impl<T> Default for Rblist<T> {
    fn default() -> Self { Self(Tree::new()) }
}
impl<T: fmt::Debug> fmt::Debug for Rblist<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl<T: PartialEq> PartialEq for Rblist<T> {
    fn eq(&self, other: &Self) -> bool { self.len() == other.len() && self.iter().eq(other) }
}
impl<T: Eq> Eq for Rblist<T> {}
impl<T: PartialOrd> PartialOrd for Rblist<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { self.iter().partial_cmp(other) }
}
impl<T: Ord> Ord for Rblist<T> {
    fn cmp(&self, other: &Self) -> Ordering { self.iter().cmp(other) }
}
impl<T: Hash> Hash for Rblist<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.iter().for_each(|x| x.hash(state)) }
}
// TODO: Rewire with `merge`
impl<T> FromIterator<T> for Rblist<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        for element in iter {
            list.push_back(element);
        }
        list
    }
}
impl<'a, T> IntoIterator for &'a Rblist<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}
// TODO: Rewire with `merge`
impl<T> Extend<T> for Rblist<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(|x| self.push_back(x))
    }
}
impl<'a, T: 'a + Copy> Extend<&'a T> for Rblist<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied())
    }
}
impl<T, const N: usize> From<[T; N]> for Rblist<T> {
    fn from(array: [T; N]) -> Self { array.into_iter().collect() }
}
impl<T> From<Vec<T>> for Rblist<T> {
    fn from(vec: Vec<T>) -> Self { vec.into_iter().collect() }
}

/// An iterator over the elements of a list.
pub struct Iter<'a, T> {
    __marker: PhantomData<&'a T>,
    ptr: Option<Ptr<T, Len>>,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let ptr = self.ptr?;
        unsafe {
            let output = &(*ptr.inner()).value;
            self.ptr = ptr.next();
            Some(output)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[allow(dead_code)]
    fn assert_covariance() {
        // TODO: make `Iter` covariant
        // fn b<'i, 'a>(x: Iter<'i, &'static str>) -> Iter<'i, &'a str> { x }
    }

    fn random_vec_and_list(len: usize, rng: &mut StdRng) -> (Vec<i32>, Rblist<i32>) {
        let mut vec = Vec::new();
        let mut list = Rblist::new();
        for _ in 0..len {
            let value = rng.gen_range(0..100);
            let index = rng.gen_range(0..=vec.len());
            list.insert(index, value);
            vec.insert(index, value);
        }
        (vec, list)
    }

    #[test]
    fn test_insert_remove_push_pop_random() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut list = Rblist::new();
        let mut vec = Vec::new();
        for _ in 0..100 {
            let value = rng.gen_range(0..100);
            match rng.gen_range(0..10) {
                0 => {
                    list.push_front(value);
                    vec.insert(0, value);
                }
                1 => {
                    list.push_back(value);
                    vec.push(value);
                }
                2 => {
                    if !vec.is_empty() {
                        assert_eq!(list.pop_front(), Some(vec.remove(0)));
                    }
                }
                3 => {
                    if !vec.is_empty() {
                        assert_eq!(list.pop_back(), vec.pop());
                    }
                }
                4..=6 => {
                    let index = rng.gen_range(0..=vec.len());
                    list.insert(index, value);
                    vec.insert(index, value);
                }
                7..=9 => {
                    if !vec.is_empty() {
                        let index = rng.gen_range(0..vec.len());
                        assert_eq!(list.remove(index), vec.remove(index));
                    }
                }
                _ => unreachable!(),
            }
            assert_eq!(list.iter().copied().collect::<Vec<_>>(), vec);
        }
    }

    #[test]
    fn test_iter_random() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let len = rng.gen_range(0..20);
            let (vec, list) = random_vec_and_list(len, &mut rng);
            assert_eq!(list.iter().copied().collect::<Vec<_>>(), vec);
        }
    }

    #[test]
    fn test_attributes_random() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let len = rng.gen_range(0..20);
            let (vec, list) = random_vec_and_list(len, &mut rng);
            assert_eq!(vec.is_empty(), list.is_empty());
            assert_eq!(vec.len(), list.len());
            assert_eq!(vec.first(), list.front());
            assert_eq!(vec.last(), list.back());
        }
    }
}
