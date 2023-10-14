use super::tree::Tree;
use super::Len;
use crate::tree::node;
use std::cmp::Ordering;

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
            // Go to the left subtree.
            if index < len {
                Ordering::Greater
            }
            // Remove the current node.
            else if index == len {
                Ordering::Equal
            }
            // Go to the right subtree.
            else {
                index -= len + 1;
                Ordering::Less
            }
        });
        unsafe { Box::from_raw(removed).value }
    }
}

impl<T> Default for Rblist<T> {
    fn default() -> Self { Self(Tree::new()) }
}

#[cfg(test)]
mod tests {
    use super::super::Node;
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn to_vec(list: &Rblist<i32>) -> Vec<i32> {
        unsafe fn node_to_vec(node: *const Node<i32, Len>, vec: &mut Vec<i32>) {
            if let Some(node) = node.as_ref() {
                node_to_vec(node.left, vec);
                vec.push(node.value);
                node_to_vec(node.right, vec);
            }
        }
        let mut vec = Vec::new();
        unsafe {
            if let Some(root) = list.0.root.as_ref() {
                node_to_vec(root, &mut vec);
            }
        }
        vec
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
            assert_eq!(to_vec(&list), vec);
        }
    }
}
