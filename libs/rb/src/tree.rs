#![warn(missing_docs)]
#![allow(dead_code)]

use super::Color;
use super::Listen;
use super::Node;
use std::cmp::Ordering;
use std::mem;
use std::ptr;
use std::ptr::null_mut;
use std::ptr::NonNull;

fn color<T, L: Listen<T>>(node: *const Node<T, L>) -> Color {
    unsafe { node.as_ref().map_or(Color::Black, |n| n.color) }
}

fn update_up<T, L: Listen<T>>(mut node: *mut Node<T, L>) {
    unsafe {
        while let Some(x) = node.as_mut() {
            x.update();
            node = x.parent;
        }
    }
}

/// Create a new node.
pub fn node<T, L: Listen<T>>(value: T, cache: L::Cache) -> NonNull<Node<T, L>> {
    NonNull::from(Box::leak(Box::new(Node {
        value,
        left: null_mut(),
        right: null_mut(),
        parent: null_mut(),
        color: Color::Red,
        cache,
    })))
}

/// The most basic red-black tree.
pub struct Tree<T, L: Listen<T>> {
    pub root: *mut Node<T, L>, // TODO: Make this private, by providing `fold` method.
}
impl<T, L: Listen<T>> Tree<T, L> {
    /// Create a new empty tree.
    pub fn new() -> Self { Self::default() }

    /// Returns true if the tree is empty.
    pub fn is_empty(&self) -> bool { self.root.is_null() }

    /// Returns the cursor pointing to the front of the tree.
    /// If the tree is empty, the cursor is set to a null pointer.
    pub fn front(&self) -> Cursor<T, L> {
        unsafe {
            if self.root.is_null() {
                return Cursor(null_mut());
            }
            let mut node = self.root;
            while !(*node).left.is_null() {
                node = (*node).left;
            }
            Cursor(node)
        }
    }

    /// Returns the cursor pointing to the back of the tree.
    /// If the tree is empty, the cursor is set to a null pointer.
    pub fn back(&self) -> Cursor<T, L> {
        unsafe {
            if self.root.is_null() {
                return Cursor(null_mut());
            }
            let mut node = self.root;
            while !(*node).right.is_null() {
                node = (*node).right;
            }
            Cursor(node)
        }
    }

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

            // Insert the node as the root.
            if self.root.is_null() {
                self.root = node;
                (*self.root).color = Color::Black;
                return;
            }

            // Find the partition point.
            let mut p = self.root;
            let mut x = if pred(&*p) { &mut (*p).right } else { &mut (*p).left };
            while !x.is_null() {
                p = *x;
                x = if pred(&**x) { &mut (**x).right } else { &mut (**x).left };
            }

            // Insert the node.
            node.parent = p;
            *x = node;

            // Fixup the tree.
            self.insert_fixup(node);
        }
    }

    /// Binary searches for a node according to the given predicate and removes it.
    pub fn binary_search<'a, F>(&'a self, mut f: F) -> Cursor<T, L>
    where
        F: FnMut(&'a Node<T, L>) -> Ordering,
    {
        unsafe {
            let mut z = self.root;
            while !z.is_null() {
                match f(&*z) {
                    Ordering::Less => z = (*z).right,
                    Ordering::Greater => z = (*z).left,
                    Ordering::Equal => break,
                }
            }
            Cursor(z)
        }
    }

    /// Binary searches for a node according to the given predicate and removes it.
    pub fn binary_search_remove(
        &mut self,
        f: impl FnMut(&Node<T, L>) -> Ordering,
    ) -> *mut Node<T, L> {
        unsafe {
            // Find the node `z` to remove.
            let z = self.binary_search(f).0;
            let Some(z) = z.as_mut() else {
                return null_mut();
            };

            // Swap-and-remove the node `z`.
            let removed_color; // The color of the removed node.
            let x; // The superblack node.
            let p; // The parent of the superblack node.
            if z.left.is_null() {
                x = z.right;
                p = z.parent;
                removed_color = z.color;
                self.transprant(z, x);
            } else if z.right.is_null() {
                x = z.left;
                p = z.parent;
                removed_color = z.color;
                self.transprant(z, x);
            } else {
                // Find the replacement node `y`.
                let y = {
                    let mut y = &mut *z.right;
                    while !y.left.is_null() {
                        y = &mut *y.left;
                    }
                    y
                };
                removed_color = y.color;
                x = y.right;
                if ptr::eq(y.parent, z) {
                    p = y;
                } else {
                    p = y.parent;
                    self.transprant(y, x);
                    let subtree = &mut *z.right;
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
            if removed_color == Color::Black {
                self.remove_fixup(p, x);
            } else {
                update_up(p);
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
        if !node.is_null() {
            (*node).parent = position.parent;
        }
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
        update_up(x.parent);

        // Set the root to black.
        (*self.root).color = Color::Black;
    }

    unsafe fn remove_fixup(&mut self, parent: *mut Node<T, L>, node: *mut Node<T, L>) {
        let mut x = node;
        let mut p = parent;
        while !p.is_null() && color(x) == Color::Black {
            // Case 1: `x` is the left child of `p`.
            if ptr::eq(x, (*p).left) {
                let mut s = (*p).right;
                // Lean the 3-node.
                if color(s) == Color::Red {
                    (*s).color = Color::Black;
                    (*p).color = Color::Red;
                    self.left_rotate(p);
                    s = (*p).right;
                }
                // Case 1.1: `s` is a 2-node: join with it.
                if color((*s).left) == Color::Black && color((*s).right) == Color::Black {
                    (*s).color = Color::Red;
                    x = p;
                    (*x).update();
                }
                // Case 1.2: `s` is a 3-node or a 4-node: adopt one or two children from it.
                else {
                    // Lean the 3-node.
                    if color((*s).right) == Color::Black {
                        (*s).color = Color::Red;
                        (*(*s).left).color = Color::Black;
                        self.right_rotate(s);
                        s = (*p).right;
                    }
                    (*s).color = (*p).color;
                    (*p).color = Color::Black;
                    (*(*s).right).color = Color::Black;
                    self.left_rotate(p);
                    update_up((*p).parent);
                    x = self.root;
                }
            }
            // Case 2: `x` is the right child of `p`.
            else {
                let mut s = (*p).left;
                // Lean the 3-node.
                if color(s) == Color::Red {
                    (*s).color = Color::Black;
                    (*p).color = Color::Red;
                    self.right_rotate(p);
                    s = (*p).left;
                }
                // Case 2.1: `s` is a 2-node: join with it.
                if color((*s).left) == Color::Black && color((*s).right) == Color::Black {
                    (*s).color = Color::Red;
                    x = p;
                    (*x).update();
                }
                // Case 2.2: `s` is a 3-node or a 4-node: adopt one or two children from it.
                else {
                    // Lean the 3-node.
                    if color((*s).left) == Color::Black {
                        (*s).color = Color::Red;
                        (*(*s).right).color = Color::Black;
                        self.left_rotate(s);
                        s = (*p).left;
                    }
                    (*s).color = (*p).color;
                    (*p).color = Color::Black;
                    (*(*s).left).color = Color::Black;
                    self.right_rotate(p);
                    update_up((*p).parent);
                    x = self.root;
                }
            }
            p = (*x).parent;
        }
        if !x.is_null() {
            (*x).color = Color::Black;
        }
        update_up(x);
    }

    #[allow(dead_code)]
    #[cfg(test)]
    pub fn eprint(&self, fg: &[(&'static str, *const Node<T, L>, ansi_term::Color)])
    where
        T: std::fmt::Display,
    {
        unsafe fn print_node<T, L: Listen<T>>(
            node: *const Node<T, L>,
            fg: &[(&'static str, *const Node<T, L>, ansi_term::Color)],
        ) where
            T: std::fmt::Display,
        {
            let colour = match color(node) {
                Color::Red => ansi_term::Colour::Red,
                Color::Black => ansi_term::Colour::Black,
            };
            if let Some(node) = node.as_ref() {
                eprint!("{}", colour.paint("("));
                print_node(node.left, fg);
                let mut style = ansi_term::Style::new();
                for (_name, ptr, colour) in fg {
                    if ptr::eq(node, *ptr) {
                        style = style.on(*colour);
                    }
                }
                style = style.fg(colour);
                eprint!("{}", style.paint(&node.value.to_string()));
                print_node(node.right, fg);
                eprint!("{}", colour.paint(")"));
            }
        }
        if !fg.is_empty() {
            let mut i = 0;
            for &(name, _ptr, colour) in fg {
                if i > 0 {
                    eprint!(", ");
                }
                eprint!("{}", ansi_term::Style::new().on(colour).paint(name));
                i += 1;
            }
            eprint!(": ");
        }
        unsafe {
            if let Some(root) = self.root.as_ref() {
                print_node(root, fg);
            }
        }
        eprintln!();
    }
}
impl<T, L: Listen<T>> Default for Tree<T, L> {
    fn default() -> Self { Self { root: null_mut() } }
}

/// A cursor pointing to a node in a tree, or a null pointer.
pub struct Cursor<T, L: Listen<T>>(pub *mut Node<T, L>);
impl<T, L: Listen<T>> Cursor<T, L> {
    /// Returns true if the cursor is a null pointer.
    pub fn is_null(&self) -> bool { self.0.is_null() }

    /// Advance the cursor to the next node.
    /// If there is no next node, the cursor is set to a null pointer.
    pub fn move_next(&mut self) {
        unsafe {
            debug_assert!(!self.0.is_null());
            let mut output;
            if (*self.0).right.is_null() {
                let mut child = self.0;
                output = (*child).parent;
                while !output.is_null() && ptr::eq(child, (*output).right) {
                    child = output;
                    output = (*output).parent;
                }
            } else {
                output = (*self.0).right;
                while !(*output).left.is_null() {
                    output = (*output).left;
                }
            }
            self.0 = output;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;

    struct Test;
    impl<T> Listen<T> for Test {
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

    fn len(tree: &Tree<i32, Test>) -> usize { unsafe { tree.root.as_ref().map_or(0, |n| n.cache) } }

    fn to_vec(tree: &Tree<i32, Test>) -> Vec<i32> {
        unsafe fn node_to_vec(node: *const Node<i32, Test>, vec: &mut Vec<i32>) {
            if let Some(node) = node.as_ref() {
                node_to_vec(node.left, vec);
                vec.push(node.value);
                node_to_vec(node.right, vec);
            }
        }
        let mut vec = Vec::new();
        unsafe {
            if let Some(root) = tree.root.as_ref() {
                node_to_vec(root, &mut vec);
            }
        }
        vec
    }

    fn validate(tree: &Tree<i32, Test>) {
        unsafe fn validate_node(node: &Node<i32, Test>) -> usize {
            let mut left_black_height = 0;
            if let Some(left) = node.left.as_ref() {
                left_black_height = validate_node(left);
                if node.color == Color::Red {
                    assert_eq!(left.color, Color::Black);
                }
            }
            let mut right_black_height = 0;
            if let Some(right) = node.right.as_ref() {
                right_black_height = validate_node(right);
                if node.color == Color::Red {
                    assert_eq!(right.color, Color::Black);
                }
            }
            assert_eq!(left_black_height, right_black_height);
            if node.color == Color::Black {
                left_black_height += 1;
            }
            left_black_height
        }
        unsafe {
            if let Some(root) = tree.root.as_ref() {
                assert_eq!(root.color, Color::Black);
                validate_node(root);
            }
        }
    }

    #[rstest]
    #[case(0.1)]
    #[case(0.5)]
    #[case(0.9)]
    fn test_insert_remove_random(#[case] remove_prob: f64) {
        const VALUE_LIM: i32 = 100;
        let mut rng = StdRng::seed_from_u64(42);
        let mut tree = Tree::<i32, Test>::new();
        let mut expected = Vec::new();
        for _ in 0..200 {
            let value = rng.gen_range(0..VALUE_LIM);
            if rng.gen_bool(remove_prob) {
                let expected_output = expected
                    .iter()
                    .position(|&v| v == value)
                    .map(|i| expected.remove(i));
                let output = tree.binary_search_remove(|n| n.value.cmp(&value));
                let output = unsafe { output.as_mut().map(|n| Box::from_raw(n).value) };
                assert_eq!(output, expected_output);
            } else {
                let lower_bound = expected
                    .iter()
                    .position(|&v| value <= v)
                    .unwrap_or(expected.len());
                expected.insert(lower_bound, value);
                tree.partition_point_insert(node(value, 1), |n| n.value < value);
            }
            assert_eq!(to_vec(&tree), expected);
            assert_eq!(len(&tree), expected.len());
            validate(&tree);
        }
    }

    #[test]
    fn test_cursor_random() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let len = rng.gen_range(0..20);
            let mut tree = Tree::<i32, Test>::new();
            let mut expected = Vec::new();
            for _ in 0..len {
                let value = rng.gen_range(0..100);
                let lower_bound = expected
                    .iter()
                    .position(|&v| value <= v)
                    .unwrap_or(expected.len());
                expected.insert(lower_bound, value);
                tree.partition_point_insert(node(value, 1), |n| n.value < value);
            }
            let mut cursor = tree.front();
            for index in 0..len {
                let value = unsafe { (*cursor.0).value };
                assert_eq!(value, expected[index]);
                cursor.move_next();
            }
            assert!(cursor.0.is_null());
        }
    }
}
