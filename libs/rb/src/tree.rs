//! A red-black tree with `NonNull` and `Callback`.
use crate::as_ptr;
use crate::color;
use crate::Callback;
use crate::Color;
use crate::Ptr;
use std::cmp::Ordering;
use std::mem;
use std::ptr;

// TODO: implmement `Drop` for `Tree`, and think about the ownership of the nodes.

/// A red-black tree.
#[allow(dead_code)]
pub(super) struct Tree<C: Callback> {
    root: Option<Ptr<C>>,
    black_height: u8,
}
#[allow(dead_code)]
impl<C: Callback> Tree<C> {
    /// Create a new empty tree.
    pub(super) fn new() -> Self { Self::default() }

    /// Returns `true` if the tree is empty.
    pub(super) fn is_empty(&self) -> bool { self.root.is_none() }

    /// Returns the parent `p` of the partition point according to the given predicate, and `pred(p)`.
    pub(super) fn partition_point<P>(&self, mut pred: P) -> Option<(Ptr<C>, bool)>
    where
        P: FnMut(Ptr<C>) -> bool,
    {
        let mut p = self.root?;
        let mut result = pred(p);
        let mut option_x = if result { p.as_ref().right } else { p.as_ref().left };
        while let Some(x) = option_x {
            p = x;
            result = pred(p);
            option_x = if result { p.as_ref().right } else { p.as_ref().left };
        }
        Some((p, result))
    }

    /// Binary search the tree.
    pub(super) fn binary_search<F>(&self, mut f: F) -> Option<Ptr<C>>
    where
        F: FnMut(Ptr<C>) -> Ordering,
    {
        let mut p = self.root;
        while let Some(p0) = p {
            p = match f(p0) {
                Ordering::Less => p0.right,
                Ordering::Greater => p0.left,
                Ordering::Equal => return Some(p0),
            };
        }
        None
    }

    /// Find the leftmost node.
    pub(super) fn front(&self) -> Option<Ptr<C>> {
        let mut x = self.root?;
        while let Some(y) = x.left {
            x = y;
        }
        Some(x)
    }

    /// Find the rightmost node.
    pub(super) fn back(&self) -> Option<Ptr<C>> {
        let mut x = self.root?;
        while let Some(y) = x.right {
            x = y;
        }
        Some(x)
    }

    /// Insert a new node at the position specified by `position`.
    ///
    /// If `position` is `None`, the new node is inserted as the root.
    /// Otherwise, the new node is inserted as the child of `position.0`.
    ///
    /// If `position.1` is:
    /// - `true`: the new node is inserted as the right child.
    /// - `false`: the new node is inserted as the left child.
    ///
    /// For example:
    /// - `(tree.front(), false)`: insert the new node as the leftmost child.
    /// - `(tree.back(), true)`: insert the new node as the rightmost child.
    ///
    /// # Precondition
    /// `new` must be isolated and red.
    pub(super) fn insert(&mut self, mut new: Ptr<C>, position: Option<(Ptr<C>, bool)>) {
        debug_assert!(new.is_isolated_and_red());

        // Handle the empty tree case.
        let Some((mut p, result)) = position else {
            debug_assert!(self.root.is_none());
            self.black_height = 1;
            new.color = Color::Black;
            self.root = Some(new);
            return;
        };

        // Insert the new node.
        *(if result { &mut p.as_mut().right } else { &mut p.as_mut().left }) = Some(new);
        new.as_mut().parent = Some(p);

        // Fixup the red-red violation.
        self.fix_red(p, new);
    }

    /// Pop the leftmost node.
    pub(super) fn pop_front(&mut self) -> Option<Ptr<C>> {
        let front = self.front()?;
        self.remove(front);
        Some(front)
    }

    /// Pop the rightmost node.
    pub(super) fn pop_back(&mut self) -> Option<Ptr<C>> {
        let back = self.back()?;
        self.remove(back);
        Some(back)
    }

    /// Push a new node to the leftmost position.
    pub(super) fn push_front(&mut self, new: Ptr<C>) {
        self.insert(new, self.front().map(|p| (p, false)));
    }

    /// Push a new node to the rightmost position.
    pub(super) fn push_back(&mut self, new: Ptr<C>) {
        self.insert(new, self.back().map(|p| (p, true)));
    }

    /// Remove the given node from the tree.
    ///
    /// # Precondition
    /// `z` must be in the tree.
    pub(super) fn remove(&mut self, mut z: Ptr<C>) {
        struct Removed<C: Callback> {
            color: Color,
            upper: Option<Ptr<C>>,
            lower: Option<Ptr<C>>,
        }
        let removed;

        // Case 1: the left child is empty.
        if z.left.is_none() {
            removed = Removed {
                color: z.color,
                upper: z.parent,
                lower: z.right,
            };
            self.transplant(z, removed.lower);
        }
        // Case 2: the right child is empty.
        else if z.right.is_none() {
            removed = Removed {
                color: z.color,
                upper: z.parent,
                lower: z.left,
            };
            self.transplant(z, removed.lower);
        }
        // Case 3: both children are non-empty.
        else {
            // Find the successor.
            let mut succ = z.right.unwrap();
            while let Some(left) = succ.left {
                succ = left;
            }

            // Case 3.1: the successor is the right child of `z`.
            if ptr::eq(as_ptr(succ.parent), &*z) {
                removed = Removed {
                    color: succ.color,
                    upper: Some(succ),
                    lower: succ.right,
                };
            }
            // Case 3.2: the successor is not the right child of `z`.
            else {
                removed = Removed {
                    color: succ.color,
                    upper: succ.parent,
                    lower: succ.right,
                };
                self.transplant(succ, removed.lower);
                succ.right = z.right;
                succ.right.unwrap().parent = Some(succ);
            }

            // Substitute `z` with `succ`.
            self.transplant(z, Some(succ));
            succ.left = z.left;
            succ.left.unwrap().parent = Some(succ);
            succ.color = z.color;
        }

        // Cut the removed node from the tree.
        z.isolate_and_red();

        // Fixup the black-height violation.
        if removed.color == Color::Black {
            self.fix_black(removed.upper, removed.lower);
        } else {
            // Update the remaining node.
            if let Some(mut x) = removed.upper {
                x.update();
                while let Some(mut p) = x.parent {
                    p.update();
                    x = p;
                }
            }
        }
    }

    /// Move all nodes from `other` to `self`.
    pub(super) fn append(&mut self, other: &mut Self) {
        // Handle the empty tree case.
        if other.is_empty() {
            return;
        }
        if self.is_empty() {
            *self = std::mem::take(other);
            return;
        }

        // Pop the leftmost node from `other`.
        let c = other.pop_front().unwrap();

        // Handle the case where `c` was the only node in `other`.
        if other.is_empty() {
            self.push_back(c);
            return;
        }

        // Now `l` and `r` are non-empty.
        let l = mem::take(self);
        let r = mem::take(other);
        *self = join(l, c, r);
    }

    /// Split the tree into two trees at the position specified by `position`.
    ///
    /// If `position` is `None`, the tree is originally empty, and the two trees are empty.
    /// If `position.1` is:
    /// - `true`: `position.0` is contained in `self`
    /// - `false`: `position.0` is contained in the returned tree.
    ///
    ///
    /// # Precondition
    /// - `position.0` must be in a leaf node of the 2-3-4 tree.
    pub(super) fn split_off(&mut self, position: Option<(Ptr<C>, bool)>) -> Tree<C> {
        // Handle the empty tree case.
        let Some((p, result)) = position else {
            debug_assert!(self.root.is_none());
            return Tree::new();
        };

        // Split the tree.
        let (mut l, mut r) = unjoin(self, p);
        if result {
            l.push_back(p);
        } else {
            r.push_front(p);
        }
        *self = l;
        r
    }

    /// Fixup the red-red violation between `x` and `p` and non-updated property of `x`.
    ///
    /// # Precondition
    ///
    /// - `x` must be red.
    /// - `x` must be a child of `p`.
    /// - The red-black property holds except for the possible red-red violation between `x` and `p`.
    /// - The updated property holds except for the closed path `[root, x]`.
    ///
    /// # Postcondition
    /// - The red-black property holds.
    /// - The updated property holds.
    fn fix_red(&mut self, mut p: Ptr<C>, mut x: Ptr<C>) {
        while p.color == Color::Red {
            let mut pp = p.parent.unwrap();
            // Case 1: `p` is a left child.
            if ptr::eq(as_ptr(pp.left), &*p) {
                let s = pp.as_ref().right;
                // Case 1.1: Split the 5-node.
                if color(s) == Color::Red {
                    pp.color = Color::Red;
                    p.color = Color::Black;
                    pp.right.unwrap().color = Color::Black;
                    x.update();
                    p.update();
                    x = pp;
                    p = match x.parent {
                        None => {
                            x.color = Color::Black;
                            self.black_height += 1;
                            break;
                        }
                        Some(p) => p,
                    };
                }
                // Case 1.2: Balance the 4-node
                else {
                    // Handle the splayed 4-node case.
                    if ptr::eq(as_ptr(p.right), &*x) {
                        self.left_rotate(p);
                        p = x;
                        x = p.left.unwrap();
                    }
                    p.color = Color::Black;
                    pp.color = Color::Red;
                    self.right_rotate(pp);
                    pp.update();
                }
            }
            // Case 2: `p` is a right child.
            else {
                let s = pp.as_ref().left;
                // Case 2.1: Split the 5-node.
                if color(s) == Color::Red {
                    pp.color = Color::Red;
                    p.color = Color::Black;
                    pp.left.unwrap().color = Color::Black;
                    x.update();
                    p.update();
                    x = pp;
                    p = match x.parent {
                        None => {
                            x.color = Color::Black;
                            self.black_height += 1;
                            break;
                        }
                        Some(p) => p,
                    };
                }
                // Case 2.2: Balance the 4-node
                else {
                    // Handle the splayed 4-node case.
                    if ptr::eq(as_ptr(p.left), &*x) {
                        self.right_rotate(p);
                        p = x;
                        x = p.right.unwrap();
                    }
                    p.color = Color::Black;
                    pp.color = Color::Red;
                    self.left_rotate(pp);
                    pp.update();
                }
            }
        }
        x.update();
        while let Some(mut p) = x.parent {
            p.update();
            x = p;
        }
    }

    /// Fixup the black-height violation between `x` and `p` and non-updated property of `x`.
    ///
    /// # Precondition
    /// - The black height of `x` is missing one.
    /// - `x` must be a child of `p`.
    /// - The red-black property holds except for the black-height violation between `x` and `p`.
    /// - The updated property holds except for the half-open path `[root, x[`.
    ///
    /// # Postcondition
    /// - The red-black property holds.
    /// - The updated property holds.
    #[allow(clippy::too_many_lines)]
    fn fix_black(&mut self, p: Option<Ptr<C>>, mut x: Option<Ptr<C>>) {
        // Handle the case where `x` is the root (or the tree is empty).
        let Some(mut p) = p else {
            if color(x) == Color::Red {
                x.unwrap().color = Color::Black;
            } else {
                self.black_height -= 1;
            }
            return;
        };

        while color(x) == Color::Black {
            // Case 1: `x` is a left child.
            if ptr::eq(as_ptr(p.left), as_ptr(x)) {
                let mut s = p.right;

                // Handle the case where `p` is a right-leaning 3-node.
                if color(s) == Color::Red {
                    p.color = Color::Red;
                    s.unwrap().color = Color::Black;
                    self.left_rotate(p);
                    s = p.right;
                }

                let mut s = s.unwrap();

                // Case 1.1: `s` is a 2-node.
                if color(s.left) == Color::Black && color(s.right) == Color::Black {
                    s.color = Color::Red;
                    if let Some(mut x) = x {
                        x.update();
                    }
                    p.update();
                    x = Some(p);
                    p = match p.parent {
                        None => {
                            match color(x) {
                                Color::Red => x.unwrap().color = Color::Black,
                                Color::Black => self.black_height -= 1,
                            }
                            break;
                        }
                        Some(p) => p,
                    };
                }
                // Case 1.2: `s` is a 3 or 4-node.
                else {
                    // Handle the case where `s` is a left-leaning 3-node.
                    if color(s.right) == Color::Black {
                        let mut new_s = s.left.unwrap();
                        s.color = Color::Red;
                        new_s.color = Color::Black;
                        self.right_rotate(s);
                        s.update();
                        new_s.update();
                        s = new_s;
                    }
                    s.color = p.color;
                    p.color = Color::Black;
                    s.right.unwrap().color = Color::Black;
                    self.left_rotate(p);
                    if let Some(mut x) = x {
                        x.update();
                    }
                    x = Some(p);
                    break;
                }
            }
            // Caes 2: `x` is a right child.
            else {
                let mut s = p.left;

                // Handle the case where `p` is a left-leaning 3-node.
                if color(s) == Color::Red {
                    p.color = Color::Red;
                    s.unwrap().color = Color::Black;
                    self.right_rotate(p);
                    s = p.left;
                }

                let mut s = s.unwrap();

                // Case 2.1: `s` is a 2-node.
                if color(s.left) == Color::Black && color(s.right) == Color::Black {
                    s.color = Color::Red;
                    if let Some(mut x) = x {
                        x.update();
                    }
                    p.update();
                    x = Some(p);
                    p = match p.parent {
                        None => {
                            match color(x) {
                                Color::Red => x.unwrap().color = Color::Black,
                                Color::Black => self.black_height -= 1,
                            }
                            break;
                        }
                        Some(p) => p,
                    };
                }
                // Case 2.2: `s` is a 3 or 4-node.
                else {
                    // Handle the case where `s` is a right-leaning 3-node.
                    if color(s.left) == Color::Black {
                        let mut new_s = s.right.unwrap();
                        s.color = Color::Red;
                        new_s.color = Color::Black;
                        self.left_rotate(s);
                        s.update();
                        new_s.update();
                        s = new_s;
                    }
                    s.color = p.color;
                    p.color = Color::Black;
                    s.left.unwrap().color = Color::Black;
                    self.right_rotate(p);
                    if let Some(mut x) = x {
                        x.update();
                    }
                    x = Some(p);
                    break;
                }
            }
        }

        // Cancel the black-height violation.
        x.unwrap().color = Color::Black;

        // Update the remaining node.
        if let Some(mut x) = x {
            x.update();
            while let Some(mut p) = x.parent {
                p.update();
                x = p;
            }
        }
    }

    /// Change the root of the subtree rooted at `x` to `y = x.right.unwrap()`.
    ///
    /// # Precondition
    /// `x.right` must be some.
    fn left_rotate(&mut self, mut x: Ptr<C>) {
        // Get nodes.
        let mut p = x.parent;
        let mut y = x.right.unwrap();
        let mut c = y.left;

        // Connect `x` and `c`.
        x.right = c;
        if let Some(ref mut c) = c {
            c.parent = Some(x);
        }

        // Connect `p` and `y`.
        y.parent = p;
        *(if let Some(ref mut p) = p {
            if ptr::eq(as_ptr(p.left), &*x) {
                &mut p.left
            } else {
                &mut p.right
            }
        } else {
            &mut self.root
        }) = Some(y);

        // Connect `x` and `y`.
        y.left = Some(x);
        x.parent = Some(y);
    }

    /// Change the root of the subtree rooted at `x` to `y = x.left.unwrap()`.
    ///
    /// # Precondition
    /// `x.left` must be some.
    fn right_rotate(&mut self, mut x: Ptr<C>) {
        // Get nodes.
        let mut p = x.parent;
        let mut y = x.left.unwrap();
        let mut c = y.right;

        // Connect `x` and `c`.
        x.left = c;
        if let Some(ref mut c) = c {
            c.parent = Some(x);
        }

        // Connect `p` and `y`.
        y.parent = p;
        *(if let Some(ref mut p) = p {
            if ptr::eq(as_ptr(p.left), &*x) {
                &mut p.left
            } else {
                &mut p.right
            }
        } else {
            &mut self.root
        }) = Some(y);

        // Connect `x` and `y`.
        y.right = Some(x);
        x.parent = Some(y);
    }

    /// Replace the subtree rooted at `u` with the subtree rooted at `v`.
    pub(super) fn transplant(&mut self, u: Ptr<C>, v: Option<Ptr<C>>) {
        if let Some(mut p) = u.parent {
            if ptr::eq(as_ptr(p.left), &*u) {
                p.left = v;
            } else {
                p.right = v;
            }
        } else {
            self.root = v;
        }
        if let Some(mut v) = v {
            v.parent = u.parent;
        }
    }
}
impl<C: Callback> Default for Tree<C> {
    fn default() -> Self {
        Tree {
            root: None,
            black_height: 0,
        }
    }
}

#[allow(dead_code)]
impl<C: Callback> Ptr<C> {
    /// Get the next node in the tree.
    pub fn next(&self) -> Option<Self> {
        let mut x = *self;
        if let Some(mut x) = x.right {
            while let Some(l) = x.left {
                x = l;
            }
            return Some(x);
        }
        while let Some(p) = x.parent {
            if ptr::eq(as_ptr(p.left), &*x) {
                return Some(p);
            }
            x = p;
        }
        None
    }

    /// Get the previous node in the tree.
    pub fn prev(&self) -> Option<Self> {
        let mut x = *self;
        if let Some(mut x) = x.left {
            while let Some(r) = x.right {
                x = r;
            }
            return Some(x);
        }
        while let Some(p) = x.parent {
            if ptr::eq(as_ptr(p.right), &*x) {
                return Some(p);
            }
            x = p;
        }
        None
    }
}

/// Join two trees with a node `c`.
///
/// # Precondition
/// - `l` and `r` must be non-empty.
/// - `c` must be isolated and red.
fn join<C: Callback>(mut l: Tree<C>, mut c: Ptr<C>, mut r: Tree<C>) -> Tree<C> {
    debug_assert!(c.is_isolated_and_red());
    debug_assert!(l.root.is_some());
    debug_assert!(r.root.is_some());
    debug_assert!(l.root.unwrap().color == Color::Black);
    debug_assert!(r.root.unwrap().color == Color::Black);

    // Merge three trees.
    match l.black_height.cmp(&r.black_height) {
        // When `l` and `r` are of the same height.
        Ordering::Equal => {
            c.left = Some(l.root.unwrap());
            c.right = Some(r.root.unwrap());
            c.color = Color::Black;
            l.root.unwrap().parent = Some(c);
            r.root.unwrap().parent = Some(c);
            c.update();
            Tree {
                root: Some(c),
                black_height: l.black_height + 1,
            }
        }
        // When `l` is taller than `r`.
        Ordering::Greater => {
            // Find the merge point.
            let (mut p, mut x) = {
                let mut diff = l.black_height - r.black_height - 1;
                let mut p = l.root.unwrap();
                let mut x = p.right.unwrap();
                loop {
                    if x.color == Color::Black {
                        if diff == 0 {
                            break;
                        }
                        diff -= 1;
                    }
                    p = x;
                    x = p.right.unwrap();
                }
                (p, x)
            };

            // Merge `x`, `c` and `r`, and set `p` as the parent.
            p.right = Some(c);
            c.parent = Some(p);
            c.left = Some(x);
            x.parent = Some(c);
            c.right = Some(r.root.unwrap());
            r.root.unwrap().parent = Some(c);
            c.update();

            // Fixup the red-red violation.
            l.fix_red(p, c);

            l
        }
        Ordering::Less => {
            // Find the merge point.
            let (mut p, mut x) = {
                let mut diff = r.black_height - l.black_height - 1;
                let mut p = r.root.unwrap();
                let mut x = p.left.unwrap();
                loop {
                    if x.color == Color::Black {
                        if diff == 0 {
                            break;
                        }
                        diff -= 1;
                    }
                    p = x;
                    x = p.left.unwrap();
                }
                (p, x)
            };

            // Merge `l`, `c` and `x`, and set `p` as the parent.
            p.left = Some(c);
            c.parent = Some(p);
            c.right = Some(x);
            x.parent = Some(c);
            c.left = Some(l.root.unwrap());
            l.root.unwrap().parent = Some(c);
            c.update();

            // Fixup the red-red violation.
            r.fix_red(p, c);

            r
        }
    }
}

/// Split a tree into two trees with a node `c`.
///
/// `black_height` is the black-height of `z`.
///
/// # Precondition
/// - `z` must be in a leaf node of the 2-3-4 tree.
#[allow(unused_variables)]
#[allow(unused_mut)]
#[allow(dead_code)]
fn unjoin<C: Callback>(tree: &mut Tree<C>, mut z: Ptr<C>) -> (Tree<C>, Tree<C>) {
    // Initialize two trees.
    let mut l = Tree::new();
    let mut r = Tree::new();
    if let Some(mut zl) = z.left.take() {
        zl.parent = None;
        debug_assert!(zl.is_isolated_and_red());
        l.insert(zl, None);
    }
    if let Some(mut zr) = z.right.take() {
        zr.parent = None;
        debug_assert!(zr.is_isolated_and_red());
        r.insert(zr, None);
    }
    let mut black_height = u8::from(z.color == Color::Black);
    while let Some(mut p) = z.parent {
        let p_original_color = p.color;
        // Case 1: `z` is a left child: `r <- join(r, p, p.right)`.
        if ptr::eq(&*z, as_ptr(p.left)) {
            // Get the right child of `p`.
            let mut x = Tree {
                root: p.right,
                black_height,
            };

            // Transplant `p` with `z`.
            tree.transplant(p, Some(z));
            if let Some(mut x) = x.root {
                x.parent = None;
            }
            p.isolate_and_red();

            // Fix the red-root violation.
            if color(x.root) == Color::Red {
                x.root.unwrap().color = Color::Black;
                x.black_height += 1;
            }

            // Join `r` and `x`.
            if r.is_empty() {
                x.push_front(p);
                r = x;
            } else if x.is_empty() {
                r.push_back(p);
            } else {
                r = join(r, p, x);
            }
        }
        // Case 2: `z` is a right child: `l <- join(p.left, p, l)`.
        else {
            // Get the left child of `p`.
            let mut x = Tree {
                root: p.left,
                black_height,
            };

            // Transplant `p` with `z`.
            tree.transplant(p, Some(z));
            if let Some(mut x) = x.root {
                x.parent = None;
            }
            p.isolate_and_red();

            // Fix the red-root violation.
            if color(x.root) == Color::Red {
                x.root.unwrap().color = Color::Black;
                x.black_height += 1;
            }

            // Join `x` and `l`.
            if l.is_empty() {
                x.push_back(p);
                l = x;
            } else if x.is_empty() {
                l.push_front(p);
            } else {
                l = join(x, p, l);
            }
        }
        // Update the black-height.
        if p_original_color == Color::Black {
            black_height += 1;
        }
    }
    debug_assert!(ptr::eq(as_ptr(tree.root), &*z));
    *tree = Tree::new();
    z.color = Color::Red;
    debug_assert!(z.is_isolated_and_red());
    (l, r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;
    use std::borrow::Cow;
    use std::ops::Range;

    const MODULO: u64 = 998244353;

    #[derive(Debug)]
    struct RollingHash {
        hash: u64,
        base: u64,
    }
    impl RollingHash {
        fn new(value: u64) -> Self {
            Self {
                hash: value,
                base: 100,
            }
        }

        fn empty() -> Self { Self { hash: 0, base: 1 } }

        fn append(&mut self, other: &Self) {
            self.hash = (self.hash * other.base + other.hash) % MODULO;
            self.base = self.base * other.base % MODULO;
        }
    }

    #[derive(Debug)]
    struct Data {
        len: usize,
        value: u64,
        hash: RollingHash,
    }
    impl Data {
        fn new(value: u64) -> Self {
            Self {
                len: 1,
                value,
                hash: RollingHash::new(value),
            }
        }
    }

    struct TestCallback;
    impl Callback for TestCallback {
        type Data = Data;

        fn push(_node: Ptr<Self>) {}

        fn update(mut node: Ptr<Self>) {
            let value = node.data.value;

            // Handle the left child.
            node.data.len = 0;
            node.data.hash = RollingHash::empty();
            if let Some(left) = node.left {
                node.data.len += left.data.len;
                node.data.hash.append(&left.data.hash);
            }

            // Handle the current node.
            node.data.len += 1;
            node.data.hash.append(&RollingHash::new(value));

            // Handle the right child.
            if let Some(right) = node.right {
                node.data.len += right.data.len;
                node.data.hash.append(&right.data.hash);
            }
        }
    }

    fn validate(tree: &Tree<TestCallback>) {
        fn validate_ptr(ptr: Ptr<TestCallback>) -> Result<u8, String> {
            let node = ptr.as_ref();
            let mut left_black_height = 0;
            let mut length = 0;
            let mut hash = RollingHash::empty();

            // Handle the left child.
            if let Some(left) = node.left {
                length += left.data.len;
                hash.append(&left.data.hash);
                left_black_height = validate_ptr(left)?;
                // Check the red-red property.
                (ptr.color == Color::Black || left.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "Red-red violation: {:?} and {:?}",
                            ptr.data.value, left.data.value
                        )
                    })?;
            }

            // Handle the current node.
            length += 1;
            hash.append(&RollingHash::new(node.data.value));

            // Handle the right child.
            let mut right_black_height = 0;
            if let Some(right) = node.right {
                hash.append(&right.data.hash);
                length += right.data.len;
                right_black_height = validate_ptr(right)?;
                // Check the red-red property.
                (ptr.color == Color::Black || right.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "Red-red violation: {:?} and {:?}",
                            ptr.data.value, right.data.value
                        )
                    })?;
            }

            // Make sure the black-height is equal.
            (left_black_height == right_black_height)
                .then_some(())
                .ok_or_else(|| {
                    format!(
                        "Black-height violation: {:?} and {:?}",
                        ptr.data.value, ptr.data.value
                    )
                })?;

            // Make sure the length is correct.
            (length == node.data.len).then_some(()).ok_or_else(|| {
                format!(
                    "Length violation at {}. Expected {}, got {}",
                    ptr.data.value, length, node.data.len
                )
            })?;

            // Make sure the hash is correct.
            (hash.hash == node.data.hash.hash)
                .then_some(())
                .ok_or_else(|| {
                    format!(
                        "Hash violation at {}. Expected {}, got {}",
                        ptr.data.value, hash.hash, node.data.hash.hash
                    )
                })?;

            Ok(left_black_height + u8::from(ptr.color == Color::Black))
        }
        || -> Result<(), String> {
            if let Some(root) = tree.root {
                let black_height = validate_ptr(root)?;
                // Make sure the root is black.
                (root.color == Color::Black).then_some(()).ok_or_else(|| {
                    format!(
                        "Root violation: expected {:?}, got {:?}",
                        Color::Black,
                        root.color
                    )
                })?;

                // Make sure the black-height is correct.
                (black_height == tree.black_height)
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "Black-height violation: expected {}, got {}",
                            black_height, tree.black_height,
                        )
                    })?;
            }
            Ok(())
        }()
        .unwrap_or_else(|e| {
            panic!(
                "{}\n{}",
                e,
                format(tree, |data| data.value.to_string(), &[])
            )
        })
    }

    fn to_vec(tree: &Tree<TestCallback>) -> Vec<u64> {
        fn extend(node: Ptr<TestCallback>, vec: &mut Vec<u64>) {
            if let Some(left) = node.left {
                extend(left, vec);
            }
            vec.push(node.data.value);
            if let Some(right) = node.right {
                extend(right, vec);
            }
        }
        let mut vec = Vec::new();
        if let Some(root) = tree.root {
            extend(root, &mut vec);
        }
        vec
    }

    pub(super) fn write<'a, C: Callback, F, S>(
        w: &mut impl std::io::Write,
        tree: &Tree<C>,
        mut to_string: F,
        fg: &[(&'static str, Ptr<C>, ansi_term::Color)],
    ) -> std::io::Result<()>
    where
        F: FnMut(&C::Data) -> S,
        S: Into<Cow<'a, str>>,
    {
        unsafe fn write_ptr<'a, C: Callback, F, S>(
            w: &mut impl std::io::Write,
            current: Ptr<C>,
            to_string: &mut F,
            fg: &[(&'static str, Ptr<C>, ansi_term::Color)],
        ) -> std::io::Result<()>
        where
            F: FnMut(&C::Data) -> S,
            S: Into<Cow<'a, str>>,
        {
            let colour = match current.color {
                Color::Red => ansi_term::Colour::Red,
                Color::Black => ansi_term::Colour::Black,
            };
            write!(w, "{}", colour.paint("("))?;
            if let Some(left) = current.left {
                write_ptr(w, left, to_string, fg)?;
            }
            let mut style = ansi_term::Style::new();
            for &(_name, ptr, colour) in fg {
                if ptr::eq(&*current, &*ptr) {
                    style = style.on(colour);
                }
            }
            style = style.fg(colour);
            write!(w, "{}", style.paint(to_string(&current.data)))?;
            if let Some(right) = current.right {
                write_ptr(w, right, to_string, fg)?;
            }
            write!(w, "{}", colour.paint(")"))?;
            Ok(())
        }
        if !fg.is_empty() {
            for (i, &(name, _ptr, colour)) in fg.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{}", ansi_term::Style::new().on(colour).paint(name))?;
            }
            write!(w, ": ")?;
        }
        unsafe {
            if let Some(root) = tree.root {
                write_ptr(w, root, &mut to_string, fg)?;
            }
        }
        Ok(())
    }

    pub(super) fn format<'a, C: Callback, F, S>(
        tree: &Tree<C>,
        to_string: F,
        fg: &[(&'static str, Ptr<C>, ansi_term::Color)],
    ) -> String
    where
        F: FnMut(&C::Data) -> S,
        S: Into<Cow<'a, str>>,
    {
        let mut buf = Vec::new();
        write(&mut buf, tree, to_string, fg).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn test_insert() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut tree = Tree::<TestCallback>::new();
        let mut vec = Vec::new();
        for _ in 0..200 {
            let value = rng.gen_range(0..20);
            let index = vec.partition_point(|&x| x < value);
            vec.insert(index, value);
            let insert_position = tree.partition_point(|p| p.data.value < value);
            tree.insert(Ptr::new(Data::new(value)), insert_position);
            assert_eq!(
                to_vec(&tree),
                vec,
                "{}",
                format(&tree, |data| data.value.to_string(), &[])
            );
            validate(&tree)
        }
    }

    #[rstest]
    #[case(0.1)]
    #[case(0.5)]
    #[case(0.9)]
    fn test_insert_remove_random(#[case] remove_prob: f64) {
        const VALUE_LIM: u64 = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut tree = Tree::<TestCallback>::new();
            let mut expected = Vec::new();
            for _ in 0..200 {
                let value = rng.gen_range(0..VALUE_LIM);
                if rng.gen_bool(remove_prob) {
                    let expected_output = expected
                        .iter()
                        .position(|&v| v == value)
                        .map(|i| expected.remove(i));
                    let output = tree.binary_search(|n| n.data.value.cmp(&value));
                    if let Some(output) = output {
                        tree.remove(output);
                    }
                    let output = output.map(|ptr| ptr.into_box().data.value);
                    assert_eq!(output, expected_output);
                } else {
                    let lower_bound = expected
                        .iter()
                        .position(|&v| value <= v)
                        .unwrap_or(expected.len());
                    expected.insert(lower_bound, value);
                    let insert_position = tree.partition_point(|n| n.data.value < value);
                    tree.insert(Ptr::new(Data::new(value)), insert_position);
                }
                assert_eq!(to_vec(&tree), expected);
                validate(&tree);
            }
        }
    }

    #[test]
    fn test_append_split_off_random() {
        fn random_tree(rng: &mut StdRng, range: Range<u64>) -> (Tree<TestCallback>, Vec<u64>) {
            const QUERY_LIM: usize = 20;
            let query_number = rng.gen_range(0..QUERY_LIM);
            let mut tree = Tree::<TestCallback>::new();
            for _ in 0..query_number {
                let value = rng.gen_range(range.clone());
                if rng.gen_bool(0.5) {
                    let insert_position = tree.partition_point(|n| n.data.value < value);
                    tree.insert(Ptr::new(Data::new(value)), insert_position);
                } else {
                    let output = tree.binary_search(|n| n.data.value.cmp(&value));
                    if let Some(output) = output {
                        tree.remove(output);
                    }
                }
            }
            let vec = to_vec(&tree);
            (tree, vec)
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let (mut tree1, mut vec1) = random_tree(&mut rng, 0..20);
            let (mut tree2, mut vec2) = random_tree(&mut rng, 21..40);

            // Test append.
            tree1.append(&mut tree2);
            vec1.append(&mut vec2);
            assert!(tree2.is_empty());
            assert_eq!(to_vec(&tree1), vec1);
            validate(&tree1);
            validate(&tree2);

            // Test split_off.
            let lb_value = rng.gen_range(0..=40);
            let split_index = vec1.partition_point(|&v| v < lb_value);
            let split_position = tree1.partition_point(|n| n.data.value < lb_value);
            let tree2 = tree1.split_off(split_position);
            let vec2 = vec1.split_off(split_index);
            assert_eq!(to_vec(&tree1), vec1);
            assert_eq!(to_vec(&tree2), vec2);
        }
    }

    #[test]
    fn test_next_prev_random() {
        fn random_tree(rng: &mut StdRng) -> (Tree<TestCallback>, Vec<u64>) {
            const VALUE_LIM: u64 = 40;
            const QUERY_LIM: usize = 20;
            let query_number = rng.gen_range(0..QUERY_LIM);
            let mut tree = Tree::<TestCallback>::new();
            for _ in 0..query_number {
                let value = rng.gen_range(0..VALUE_LIM);
                if rng.gen_bool(0.5) {
                    let insert_position = tree.partition_point(|n| n.data.value < value);
                    tree.insert(Ptr::new(Data::new(value)), insert_position);
                } else {
                    let output = tree.binary_search(|n| n.data.value.cmp(&value));
                    if let Some(output) = output {
                        tree.remove(output);
                    }
                }
            }
            let vec = to_vec(&tree);
            (tree, vec)
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let (tree, vec) = random_tree(&mut rng);

            // Test next.
            let mut values = Vec::new();
            let mut ptr = tree.front();
            while let Some(p) = ptr {
                values.push(p.data.value);
                ptr = p.next();
            }
            assert_eq!(values, vec);

            // Test prev.
            let mut values = Vec::new();
            let mut ptr = tree.back();
            while let Some(p) = ptr {
                values.push(p.data.value);
                ptr = p.prev();
            }
            assert_eq!(values, vec.into_iter().rev().collect::<Vec<_>>());
        }
    }
}
