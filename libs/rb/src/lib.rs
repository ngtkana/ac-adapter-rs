#![warn(missing_docs)]
//! Containers for storing data in a red-black tree.

use std::cmp::Ordering;
use std::mem;
use std::ptr;
use std::ptr::null_mut;
use std::ptr::NonNull;

/// A node in a red-black tree.
pub trait Listen<T>: Sized {
    /// The type of the cache.
    type Cache;
    /// Callback for when the node is accessed down the tree.
    fn push(node: &mut Node<T, Self>);
    /// Callback for when the node is accessed up the tree.
    fn update(node: &mut Node<T, Self>);
}

/// A no-op callback.
pub struct Len;
impl<T> Listen<T> for Len {
    type Cache = usize;

    fn push(_node: &mut Node<T, Self>) {}

    fn update(node: &mut Node<T, Self>) {
        unsafe {
            node.cache = 1
                + node.left.as_ref().map_or(0, |n| n.cache)
                + node.right.as_ref().map_or(0, |n| n.cache);
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}
fn color<T, L: Listen<T>>(node: *const Node<T, L>) -> Color {
    unsafe { node.as_ref().map_or(Color::Black, |n| n.color) }
}

/// A node in a red-black tree.
#[allow(dead_code)]
pub struct Node<T, L: Listen<T>> {
    value: T,
    left: *mut Node<T, L>,
    right: *mut Node<T, L>,
    parent: *mut Node<T, L>,
    color: Color,
    cache: L::Cache,
}
#[allow(dead_code)]
impl<T, L: Listen<T>> Node<T, L> {
    fn push(&mut self) { L::push(self); }

    fn update(&mut self) { L::update(self); }
}

/// The most basic red-black tree.
pub struct RbTree<T, L: Listen<T>> {
    root: *mut Node<T, L>,
}
impl<T, L: Listen<T>> RbTree<T, L> {
    /// Create a new empty tree.
    pub fn new() -> Self { Self::default() }

    /// Returns true if the tree is empty.
    pub fn is_empty(&self) -> bool { self.root.is_null() }

    /// Insert a node at the partition point according to the given predicate.
    pub fn partition_point_insert(
        &mut self,
        mut node: NonNull<Node<T, L>>,
        mut pred: impl FnMut(&Node<T, L>) -> bool,
    ) {
        unsafe {
            let node = node.as_mut();
            // Check the node.
            debug_assert!(node.left.is_null());
            debug_assert!(node.right.is_null());
            debug_assert!(node.parent.is_null());
            debug_assert!(node.color == Color::Red);

            // Find the partition point.
            let mut p = null_mut();
            let mut x = self.root;
            while !x.is_null() {
                p = x;
                x = if pred(&*x) { (*x).left } else { (*x).right }
            }

            // Insert the node.
            node.parent = p;
            *(if p.is_null() {
                &mut self.root
            } else if pred(&*p) {
                &mut (*p).left
            } else {
                &mut (*p).right
            }) = node;

            // Fixup the tree.
            self.insert_fixup(node);
        }
    }

    /// Binary searches for a node according to the given predicate and removes it.
    pub fn binary_search_remove(
        &mut self,
        mut f: impl FnMut(&Node<T, L>) -> Ordering,
    ) -> *mut Node<T, L> {
        unsafe {
            // Find the node.
            let mut z = self.root;
            while !z.is_null() {
                match f(&*z) {
                    Ordering::Less => z = (*z).left,
                    Ordering::Greater => z = (*z).right,
                    Ordering::Equal => break,
                }
            }
            let Some(mut y) = z.as_mut() else {
                return null_mut();
            };
            let z = z.as_mut().unwrap();

            // Find the replacement node.
            let mut y_original_color = color(y);
            let x;
            if z.left.is_null() {
                x = z.right;
                self.transprant(z, x);
            } else if z.right.is_null() {
                x = z.left;
                self.transprant(z, x);
            } else {
                let subtree = &mut *z.right;
                y = &mut *z.right;
                while !y.left.is_null() {
                    y = &mut *y.left;
                }
                y_original_color = y.color;
                x = y.right;
                if !ptr::eq(y.parent, z) {
                    self.transprant(y, x);
                    // Connect `y` and `subtree`.
                    subtree.parent = y;
                    y.right = subtree;
                }
                self.transprant(z, y);
                // Connect `z` and `y`.
                y.left = z.left;
                (*y.left).parent = y;
                y.color = z.color;
            }
            if y_original_color == Color::Black {
                self.remove_fixup(x);
            }
            z
        }
    }

    /// Split the tree into two trees according to the given predicate.
    pub fn partition_point_split(&mut self, _pred: impl FnMut(&T) -> bool) -> Self { todo!() }

    /// Merge two trees together.
    pub fn append(&mut self, _other: &mut Self) { todo!() }

    unsafe fn left_rotate(&mut self, node: *mut Node<T, L>) {
        // Get the nodes.
        let p = (*node).parent;
        let l = node;
        let r = (*l).right;
        let c = (*r).left;

        // Connect l and c.
        (*l).right = c;
        if !c.is_null() {
            (*c).parent = l;
        }

        // Connect p and r.
        if p.is_null() {
            self.root = r;
        } else if l == (*p).left {
            (*p).left = r;
        } else {
            (*p).right = r;
        }
        (*r).parent = p;

        // Connect l and r.
        (*r).left = l;
        (*l).parent = r;

        // Update
        (*l).update();
        (*r).update();
    }

    unsafe fn right_rotate(&mut self, node: *mut Node<T, L>) {
        // Get the nodes.
        let p = (*node).parent;
        let l = (*node).left;
        let r = node;
        let c = (*l).right;

        // Connect r and c.
        (*r).left = c;
        if !c.is_null() {
            (*c).parent = r;
        }

        // Connect p and l.
        if p.is_null() {
            self.root = l;
        } else if r == (*p).left {
            (*p).left = l;
        } else {
            (*p).right = l;
        }
        (*l).parent = p;

        // Connect l and r.
        (*l).right = r;
        (*r).parent = l;

        // Update
        (*r).update();
        (*l).update();
    }

    unsafe fn transprant(&mut self, position: &mut Node<T, L>, node: *mut Node<T, L>) {
        if position.parent.is_null() {
            self.root = node;
        } else if ptr::eq(position, (*position.parent).left) {
            (*position.parent).left = node;
        } else {
            (*position.parent).right = node;
        }
        (*node).parent = (*position).parent;
    }

    unsafe fn insert_fixup(&mut self, node: &mut Node<T, L>) {
        let mut x = node;
        while color(x.parent) == Color::Red {
            debug_assert!(x.color == Color::Red);
            let mut p = &mut (*x.parent);
            let pp = &mut (*p.parent);
            // Case 1: p is the left child of pp.
            if ptr::eq(p, pp.left) {
                // Case 1.1: p's sibling is red: split the 5-node.
                if color(pp.right) == Color::Red {
                    p.color = Color::Black;
                    (*pp.right).color = Color::Black;
                    pp.color = Color::Red;
                    p.update();
                    pp.update();
                    x = pp;
                }
                // Case 1.2: p's sibling is black: balance the leaning 4-node.
                else {
                    if ptr::eq(x, p.right) {
                        mem::swap(&mut x, &mut p);
                        self.left_rotate(x);
                    }
                    self.right_rotate(pp);
                    p.color = Color::Black;
                    pp.color = Color::Red;
                }
            }
            // Case 2: p is the right child of pp.
            else {
                // Case 2.1: p's sibling is red: split the 5-node.
                if color(pp.left) == Color::Red {
                    p.color = Color::Black;
                    (*pp.left).color = Color::Black;
                    pp.color = Color::Red;
                    p.update();
                    pp.update();
                    x = pp;
                }
                // Case 2.2: p's sibling is black: balance the leaning 4-node.
                else {
                    if ptr::eq(x, p.left) {
                        mem::swap(&mut x, &mut p);
                        self.right_rotate(x);
                    }
                    self.left_rotate(pp);
                    p.color = Color::Black;
                    pp.color = Color::Red;
                }
            }
        }

        // Update the remaining nodes.
        while let Some(p) = x.parent.as_mut() {
            x = p;
            x.update();
        }

        // Set the root to black.
        (*self.root).color = Color::Black;
    }

    unsafe fn remove_fixup(&mut self, _node: *mut Node<T, L>) { todo!() }
}
impl<T, L: Listen<T>> Default for RbTree<T, L> {
    fn default() -> Self { Self { root: null_mut() } }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn node(value: i32) -> NonNull<Node<i32, Len>> {
        NonNull::from(Box::leak(Box::new(Node {
            value,
            left: null_mut(),
            right: null_mut(),
            parent: null_mut(),
            color: Color::Red,
            cache: 1,
        })))
    }

    fn len(tree: &RbTree<i32, Len>) -> usize {
        unsafe { tree.root.as_ref().map_or(0, |n| n.cache) }
    }

    #[allow(dead_code)]
    fn print(tree: &RbTree<i32, Len>) {
        unsafe fn node_to_string(node: *const Node<i32, Len>) {
            let colour = match color(node) {
                Color::Red => ansi_term::Colour::Red,
                Color::Black => ansi_term::Colour::Black,
            };
            if let Some(node) = node.as_ref() {
                print!("{}", colour.paint("("));
                node_to_string(node.left);
                print!("{}", colour.paint(&node.value.to_string()));
                node_to_string(node.right);
                print!("{}", colour.paint(")"));
            }
        }
        unsafe {
            if let Some(root) = tree.root.as_ref() {
                node_to_string(root);
            }
        }
        println!();
    }

    fn validate(tree: &RbTree<i32, Len>) {
        unsafe fn validate_node(node: &Node<i32, Len>) {
            if let Some(left) = node.left.as_ref() {
                validate_node(left);
                if node.color == Color::Red {
                    assert_eq!(left.color, Color::Black);
                }
            }
            if let Some(right) = node.right.as_ref() {
                validate_node(right);
                if node.color == Color::Red {
                    assert_eq!(right.color, Color::Black);
                }
            }
        }
        unsafe {
            if let Some(root) = tree.root.as_ref() {
                assert_eq!(root.color, Color::Black);
                validate_node(root);
            }
        }
    }

    #[test]
    fn test_partition_point_insert() {
        let mut tree = RbTree::<i32, Len>::new();
        validate(&tree);
        assert_eq!(len(&tree), 0);
        let mut expected_len = 0;
        for _ in 0..20 {
            expected_len += 1;
            tree.partition_point_insert(node(42), |_| true);
            validate(&tree);
            assert_eq!(len(&tree), expected_len);
        }
    }

    #[test]
    fn test_random() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut tree = RbTree::<i32, Len>::new();
        for _ in 0..20 {
            let value = rng.gen_range(0..100);
            tree.partition_point_insert(node(value), |n| value < n.value);
            validate(&tree);
        }
    }
}
