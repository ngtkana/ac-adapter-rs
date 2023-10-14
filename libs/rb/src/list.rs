use super::tree::Tree;
use super::Len;
use crate::tree::node;

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

    /// Inserts a value into the list.
    pub fn insert(&mut self, mut index: usize, element: T)
    where
        T: std::fmt::Display,
    {
        self.0.partition_point_insert(node(element, 1), |n| {
            let len = unsafe { n.left.as_ref().map_or(0, |n| n.cache) };
            if len < index {
                index -= len + 1;
                true
            } else {
                false
            }
        });
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
    fn test_insert_random() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut list = Rblist::new();
        let mut vec = Vec::new();
        for _ in 0..100 {
            let value = rng.gen_range(0..100);
            let index = rng.gen_range(0..=vec.len());
            list.insert(index, value);
            vec.insert(index, value);
            assert_eq!(to_vec(&list), vec);
        }
    }
}
