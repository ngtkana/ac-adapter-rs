use super::tree::node;
use super::tree::Cursor;
use super::tree::Tree;
use super::Len;
use core::fmt;
use std::cmp::Ordering;
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
            cursor: self.0.front(),
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
    pub fn front(&self) -> Option<&T> { unsafe { Some(&self.0.front().0.as_ref()?.value) } }

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
        unsafe { Some(&mut self.0.front().0.as_mut()?.value) }
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
    pub fn back(&self) -> Option<&T> { unsafe { Some(&self.0.back().0.as_ref()?.value) } }

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
        unsafe { Some(&mut self.0.back().0.as_mut()?.value) }
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

    /// Inserts an element at position index within the vector, shifting all elements after it to the right.
    ///
    /// # Panics
    /// Panics if `index > len`.
    ///
    /// # Examples
    /// ```
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
}

impl<T> Default for Rblist<T> {
    fn default() -> Self { Self(Tree::new()) }
}
impl<T: fmt::Debug> fmt::Debug for Rblist<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An iterator over the elements of a list.
pub struct Iter<'a, T> {
    __marker: PhantomData<&'a T>,
    cursor: Cursor<T, Len>,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor.is_null() {
            return None;
        }
        unsafe {
            let output = &(*self.cursor.0).value;
            self.cursor.move_next();
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
    fn test_insert_remove_random() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut list = Rblist::new();
        let mut vec = Vec::new();
        for _ in 0..100 {
            let value = rng.gen_range(0..100);
            let index = rng.gen_range(0..=vec.len());
            if rng.gen_bool(0.5) {
                list.insert(index, value);
                vec.insert(index, value);
            } else if !vec.is_empty() {
                let index = rng.gen_range(0..vec.len());
                assert_eq!(list.remove(index), vec.remove(index));
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
