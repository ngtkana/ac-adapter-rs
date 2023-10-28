#![allow(dead_code)]
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ptr::NonNull;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}
pub trait Callback: Sized {
    type Data;
    fn push(_: &mut Node<Self>);
    fn update(_: &mut Node<Self>);
}

pub struct Tree<C: Callback> {
    pub root: Option<Ptr<C>>,
    pub black_height: u8,
}
impl<C: Callback> Tree<C> {
    /// Create a new empty red-black tree.
    fn new() -> Self {
        Self {
            root: None,
            black_height: 0,
        }
    }

    fn is_empty(&self) -> bool { self.root.is_none() }

    /// Insert a leaf node.
    ///
    /// # Abount `position`
    ///
    /// `position` is `None` if and only if the tree is empty.
    /// If `position` is `Some((leaf, true))`, the new leaf will be inserted to the left of `leaf`.
    pub fn insert(
        &mut self,
        position: Option<(Ptr<C>, bool)>,
        mut new: Ptr<C>,
        mul: impl FnOnce(&C::Data, &C::Data) -> C::Data,
    ) {
        // Handle the case where the tree is empty.
        let Some((mut s, result)) = position else {
            self.root = Some(new);
            self.black_height = 1;
            return;
        };

        // Join `leaf` and `s` with `b`, and transplant `b` at the original position of `s`.
        let b = if result {
            Ptr::join_new(mul, Color::Red, new, s)
        } else {
            Ptr::join_new(mul, Color::Red, s, new)
        };
        self.transplant(s, b);
        s.parent = Some(b);
        new.parent = Some(b);

        // Fix the red-red violation.
        self.fix_red(b);
    }

    pub fn append(&mut self, other: &mut Self, mul: impl FnOnce(&C::Data, &C::Data) -> C::Data) {
        if self.is_empty() {
            std::mem::swap(self, other);
            return;
        };
        if other.is_empty() {
            return;
        };
        *self = merge(
            mem::take(self),
            mem::take(other),
            |color, mut left, mut right| {
                let p = Ptr::join_new(mul, color, left, right);
                left.parent = Some(p);
                right.parent = Some(p);
                p
            },
        );
    }

    /// Split at the given position.
    ///
    /// `position` is not freed or destructed in this function, so you need to free it manually.
    ///
    /// # Precondition
    ///
    /// - `position` is not a leaf node.
    /// - `black_height` is the black-height at *the child of* `at`.
    pub fn split_off(
        &mut self,
        at: Ptr<C>,
        black_height: u8,
        mut mul: impl FnMut(&C::Data, &C::Data) -> C::Data,
    ) -> Self {
        let mut x = at;
        let mut h = black_height;
        let mut left = Tree {
            root: Some(x.left.take().unwrap()),
            black_height: h,
        };
        left.fix_root();
        let mut right = Tree {
            root: Some(x.right.take().unwrap()),
            black_height: h,
        };
        right.fix_root();
        h += u8::from(x.color == Color::Black);
        // Loop invariant: `black_height` is the black-height at `p`.
        // NOTE: `x` behaves as a marker to remember the original position of `join(left, x, right)`.
        while let Some(p) = x.parent {
            h += u8::from(p.color == Color::Black);
            // Connect `p.parent` and `x` to remember the original position of `join(left, x, right)`.
            if let Some(mut pp) = p.parent {
                if pp.left.unwrap() == p {
                    *pp.left.as_mut().unwrap() = x;
                } else {
                    *pp.right.as_mut().unwrap() = x;
                }
            }
            x.parent = p.parent;
            // Join `{left,right}` and `s` with `p`.
            if p.left.unwrap() == x {
                let mut s = Tree {
                    root: Some(p.right.unwrap()),
                    black_height: h - u8::from(p.color == Color::Black),
                };
                s.fix_root();
                right = merge(right, s, |color, left, right| {
                    Ptr::join(p, &mut mul, color, left, right)
                });
            } else {
                let mut s = Tree {
                    root: Some(p.left.unwrap()),
                    black_height: h - u8::from(p.color == Color::Black),
                };
                s.fix_root();
                left = merge(s, left, |color, left, right| {
                    Ptr::join(p, &mut mul, color, left, right)
                });
            }
        }
        left.root.unwrap().parent = None;
        right.root.unwrap().parent = None;
        *self = left;
        right
    }

    /// Remove a leaf node `position`.
    ///
    /// `position` is not freed or destructed in this function.
    pub fn remove(&mut self, mut position: Ptr<C>) {
        // Handle the case where the tree has only one node.
        let Some(p) = position.parent else {
            self.root = None;
            self.black_height = 0;
            return;
        };
        // Transplant `s` at the original position of `p`.
        let mut s = if position == p.left.unwrap() { p.right.unwrap() } else { p.left.unwrap() };
        self.transplant(p, s);

        // We will remove the beaf `p`, so if `p` is black, we need to fix the black-height violation.
        if p.color == Color::Black {
            self.fix_black(s);
        } else {
            s.update_ancestors();
        }

        // Remove `p` from the tree.
        position.parent = None;

        // Catch the no longer needed "join" node.
        p.free();
    }

    /// It is only for `split_off`
    fn fix_root(&mut self) {
        let mut root = self.root.unwrap();
        root.parent = None;
        if root.color == Color::Red {
            root.color = Color::Black;
            self.black_height += 1;
        }
    }

    /// Fix the red-red violation.
    ///
    /// # Precondition
    ///
    /// - `x` and its parent may be a red-red pair, but this is the only violation.
    /// - `x`'s proper ancestors may not be fully-updatated, but other nodes are fully-updated.
    fn fix_red(&mut self, mut x: Ptr<C>) {
        while x.color == Color::Red {
            // Handle the case where `x` is the root.
            let Some(mut p) = x.parent else {
                x.color = Color::Black;
                x.update();
                self.black_height += 1;
                return;
            };
            if p.color == Color::Black {
                break;
            }
            let mut pp = p.parent.unwrap();
            // Case 1: `p` is a left child.
            if p == pp.left.unwrap() {
                // Case 1.1: `pp` is a 5-node.
                // Split the 5-node and continue.
                if pp.right.unwrap().color == Color::Red {
                    let mut s = pp.right.unwrap();
                    p.color = Color::Black;
                    s.color = Color::Black;
                    pp.color = Color::Red;
                    x.update();
                    p.update();
                    x = pp;
                }
                // Case 1.2: `pp` is a splayed left-leaning 4-node.
                // Finish by fixing this node.
                else if x == p.right.unwrap() {
                    self.rotate_left(p);
                    self.rotate_right(pp);
                    x.color = Color::Black;
                    pp.color = Color::Red;
                    pp.update();
                    p.update();
                    break;
                }
                // Case 1.3: `pp` is a straight left-leaning 4-node.
                // Finish by fixing this.
                else {
                    p.color = Color::Black;
                    pp.color = Color::Red;
                    self.rotate_right(pp);
                    pp.update();
                    break;
                }
            }
            // Case 2: `p` is the right child.
            else {
                // Case 2.1: `pp` is a 5-node.
                // Split the 5-node and continue.
                if pp.left.unwrap().color == Color::Red {
                    let mut s = pp.left.unwrap();
                    p.color = Color::Black;
                    s.color = Color::Black;
                    pp.color = Color::Red;
                    x.update();
                    p.update();
                    x = pp;
                }
                // Case 2.2: `pp` is a splayed right-leaning 4-node.
                // Finish by fixing this node.
                else if x == p.left.unwrap() {
                    self.rotate_right(p);
                    self.rotate_left(pp);
                    x.color = Color::Black;
                    pp.color = Color::Red;
                    pp.update();
                    p.update();
                    break;
                }
                // Case 2.3: `pp` is a straight right-leaning 4-node.
                // Finish by fixing this.
                else {
                    p.color = Color::Black;
                    pp.color = Color::Red;
                    self.rotate_left(pp);
                    pp.update();
                    break;
                }
            }
        }
        // Update the remaining nodes.
        x.update();
        x.update_ancestors();
    }

    /// Fix the black-height violation.
    ///
    /// # Precondition
    /// - `x` is a black node.
    /// - `x`'s black-height is one less than the one of its sibling, but this is the only violation.
    /// - `x`'s proper ancestors may not be fully-updated, but other nodes are not fully-updated.
    fn fix_black(&mut self, mut x: Ptr<C>) {
        // `x` is always a leaf when this function is called by `remove`.
        while x.color == Color::Black {
            // Handle the case where `x` is the root.
            let Some(mut p) = x.parent else {
                self.black_height -= 1;
                return;
            };
            // Case 1: `x` is a left child.
            if p.left.unwrap() == x {
                let mut s = p.right.unwrap();
                // If `p` is a right-leaning 3-node, lean it to the left.
                if s.color == Color::Red {
                    s.color = Color::Black;
                    p.color = Color::Red;
                    self.rotate_left(p);
                    s = p.right.unwrap();
                }
                match (s.left.unwrap().color, s.right.unwrap().color) {
                    // Case 1.1: `s` is a 2-node.
                    // Join two 2-nodes `x` and `s` and continue.
                    (Color::Black, Color::Black) => {
                        s.color = Color::Red;
                        x = p;
                        x.update();
                    }
                    // Case 1.2: `s` is a left-leaning 3-node.
                    // Adpot a child from `s` and now the violation is fixed.
                    (Color::Red, Color::Black) => {
                        let mut c = s.left.unwrap();
                        c.color = p.color;
                        p.color = Color::Black;
                        self.rotate_right(s);
                        self.rotate_left(p);
                        s.update();
                        break;
                    }
                    // Case 1.3: `s` is a right-leaning 3-node or a 4-node.
                    // Adpot a child from `s` and now the violation is fixed.
                    (_, Color::Red) => {
                        s.color = p.color;
                        p.color = Color::Black;
                        s.right.as_mut().unwrap().color = Color::Black;
                        self.rotate_left(p);
                        p.update();
                        break;
                    }
                }
            }
            // Case2: `x` is a right child.
            else {
                let mut s = p.left.unwrap();
                // If `p` is a left-leaning 3-node, lean it to the right.
                if s.color == Color::Red {
                    s.color = Color::Black;
                    p.color = Color::Red;
                    self.rotate_right(p);
                    s = p.left.unwrap();
                }
                match (s.left.unwrap().color, s.right.unwrap().color) {
                    // Case 2.1: `s` is a 2-node.
                    // Join two 2-nodes `x` and `s` and continue.
                    (Color::Black, Color::Black) => {
                        s.color = Color::Red;
                        x = p;
                        x.update();
                    }
                    // Case 2.2: `s` is a right-leaning 3-node.
                    // Adpot a child from `s` and now the violation is fixed.
                    (Color::Black, Color::Red) => {
                        let mut c = s.right.unwrap();
                        c.color = p.color;
                        p.color = Color::Black;
                        self.rotate_left(s);
                        self.rotate_right(p);
                        s.update();
                        break;
                    }
                    // Case 2.3: `s` is a left-leaning 3-node or a 4-node.
                    // Adpot a child from `s` and now the violation is fixed.
                    (Color::Red, _) => {
                        s.color = p.color;
                        p.color = Color::Black;
                        s.left.as_mut().unwrap().color = Color::Black;
                        self.rotate_right(p);
                        p.update();
                        break;
                    }
                }
            }
        }
        // Fix the black-height violation if needed.
        // 1. Broke the loop by breaking the loop condition means that `x` is a red node.
        // 2. On the other hand, `x` is a black node when the loop is broken by `break`.
        x.color = Color::Black;
        // Update the remaining nodes.
        x.update_ancestors();
    }

    /// Rotate the tree to the left.
    fn rotate_left(&mut self, mut l: Ptr<C>) {
        // Get the nodes
        let mut r = l.right.unwrap();
        let mut c = r.left.unwrap();

        // Connect `p` and `r`
        self.transplant(l, r);

        // Connect `r` and `l`
        *r.left.as_mut().unwrap() = l;
        l.parent = Some(r);

        // Connect `l` and `c`
        *l.right.as_mut().unwrap() = c;
        c.parent = Some(l);
    }

    /// Rotate the tree to the right.
    fn rotate_right(&mut self, mut r: Ptr<C>) {
        // Get the nodes
        let mut l = r.left.unwrap();
        let mut c = l.right.unwrap();

        // Connect `p` and `l`
        self.transplant(r, l);

        // Connect `l` and `r`
        *l.right.as_mut().unwrap() = r;
        r.parent = Some(l);

        // Connect `r` and `c`
        *r.left.as_mut().unwrap() = c;
        c.parent = Some(r);
    }

    fn transplant(&mut self, position: Ptr<C>, mut new: Ptr<C>) {
        new.parent = position.parent;
        if let Some(mut p) = position.parent {
            if position == p.left.unwrap() {
                *p.left.as_mut().unwrap() = new;
            } else {
                *p.right.as_mut().unwrap() = new;
            }
        } else {
            self.root = Some(new);
        }
    }

    pub fn from_slice_of_leaves<F>(leaves: &mut [Ptr<C>], mut mul: F) -> Self
    where
        F: FnMut(&C::Data, &C::Data) -> C::Data,
    {
        fn from_slice_of_leaves<C: Callback, F>(leaves: &mut [Ptr<C>], mul: &mut F) -> (Ptr<C>, u8)
        where
            F: FnMut(&C::Data, &C::Data) -> C::Data,
        {
            let mut black_height = 1;
            let mut n = leaves.len();
            while n != 1 {
                for i in 0..n / 2 {
                    if 2 * i + 3 == n {
                        let mut left = leaves[2 * i];
                        let mut center = leaves[2 * i + 1];
                        let mut right = leaves[2 * i + 2];
                        let mut b0 = Ptr::join_new(&mut *mul, Color::Red, left, center);
                        left.parent = Some(b0);
                        center.parent = Some(b0);
                        let b1 = Ptr::join_new(&mut *mul, Color::Black, b0, right);
                        b0.parent = Some(b1);
                        right.parent = Some(b1);
                        leaves[i] = b1;
                    } else {
                        let mut left = leaves[2 * i];
                        let mut right = leaves[2 * i + 1];
                        let b = Ptr::join_new(&mut *mul, Color::Black, left, right);
                        left.parent = Some(b);
                        right.parent = Some(b);
                        leaves[i] = b;
                    }
                }
                black_height += 1;
                n /= 2;
            }
            (leaves[0], black_height)
        }
        if leaves.is_empty() {
            return Self::new();
        }
        let (root, black_height) = from_slice_of_leaves(leaves, &mut mul);
        Self {
            root: Some(root),
            black_height,
        }
    }
}

impl<C: Callback> Default for Tree<C> {
    fn default() -> Self { Self::new() }
}

/// Merge two trees.
///
/// NOTE: `join` is expected to overwrite the parent pointers of its arguments.
fn merge<C: Callback>(
    mut left: Tree<C>,
    mut right: Tree<C>,
    join: impl FnOnce(Color, Ptr<C>, Ptr<C>) -> Ptr<C>,
) -> Tree<C> {
    let l = left.root.unwrap();
    let r = right.root.unwrap();
    debug_assert_eq!(l.color, Color::Black);
    debug_assert_eq!(r.color, Color::Black);
    match left.black_height.cmp(&right.black_height) {
        // Case 1: Two trees have the same black height.
        // Join the roots.
        Ordering::Equal => Tree {
            root: Some(join(Color::Black, l, r)),
            black_height: left.black_height + 1,
        },
        // Case 2: The l tree has a smaller black height.
        // Slide down along the l spine of the r tree, join, and fix the red-red violation.
        Ordering::Less => {
            let mut h = right.black_height;
            let mut r = r;
            loop {
                if r.color == Color::Black {
                    if h == left.black_height {
                        break;
                    }
                    h -= 1;
                }
                r = r.left.unwrap();
            }
            let mut p = r.parent.unwrap();
            let mut b = join(Color::Red, l, r);
            *p.left.as_mut().unwrap() = b;
            b.parent = Some(p);
            right.fix_red(b);
            right
        }
        // Case 3: The r tree has a smaller black height.
        // Slide down along the r spine of the l tree, join, and fix the red-red violation.
        Ordering::Greater => {
            let mut h = left.black_height;
            let mut l = l;
            loop {
                if l.color == Color::Black {
                    if h == right.black_height {
                        break;
                    }
                    h -= 1;
                }
                l = l.right.unwrap();
            }
            let mut p = l.parent.unwrap();
            let mut b = join(Color::Red, l, r);
            *p.right.as_mut().unwrap() = b;
            b.parent = Some(p);
            left.fix_red(b);
            left
        }
    }
}

pub struct Node<C: Callback> {
    pub parent: Option<Ptr<C>>,
    pub color: Color,
    pub left: Option<Ptr<C>>,
    pub right: Option<Ptr<C>>,
    pub data: C::Data,
}
impl<C: Callback> Node<C> {
    pub fn is_leaf(&self) -> bool {
        debug_assert_eq!(self.left.is_none(), self.right.is_none());
        self.left.is_none()
    }

    fn update(&mut self) {
        debug_assert!(!self.is_leaf());
        C::update(self);
    }

    fn update_ancestors(&mut self) {
        let mut p = self.parent;
        while let Some(mut x) = p {
            x.update();
            p = x.parent;
        }
    }
}
pub struct Ptr<C: Callback>(NonNull<Node<C>>);
impl<C: Callback> Ptr<C> {
    pub fn new_leaf(data: C::Data) -> Self {
        Self(NonNull::from(Box::leak(Box::new(Node {
            parent: None,
            color: Color::Black,
            left: None,
            right: None,
            data,
        }))))
    }

    pub fn as_longlife_ref<'a>(self) -> &'a Node<C> { unsafe { self.0.as_ref() } }

    /// NOTE: do not overwrite `{left, right}.parent`.
    /// It will delete the information that is needed to transplant the new node.
    pub fn join_new(
        mul: impl FnOnce(&C::Data, &C::Data) -> C::Data,
        color: Color,
        left: Self,
        right: Self,
    ) -> Self {
        let data = mul(&left.data, &right.data);
        Self(NonNull::from(Box::leak(Box::new(Node {
            parent: None,
            color,
            left: Some(left),
            right: Some(right),
            data,
        }))))
    }

    /// NOTE: It overwrites `{left, right, p}.parent`.
    /// This information is not needed for all the current use cases.
    pub fn join(
        mut p: Ptr<C>,
        mul: impl FnOnce(&C::Data, &C::Data) -> C::Data,
        color: Color,
        mut left: Self,
        mut right: Self,
    ) -> Self {
        p.data = mul(&left.data, &right.data);
        p.color = color;
        p.left = Some(left);
        p.right = Some(right);
        left.parent = Some(p);
        right.parent = Some(p);
        p.parent = None;
        p
    }

    pub fn free(self) -> C::Data { unsafe { Box::from_raw(self.0.as_ptr()).data } }

    /// Binary search for a leaf node.
    ///
    /// # About `f`
    ///
    /// - `true`: too small, go to the right.
    /// - `false`: too large, go to the left.
    pub fn binary_search_for_leaf<F: FnMut(Ptr<C>) -> bool>(self, mut f: F) -> Self {
        let mut x = self;
        while !x.is_leaf() {
            x = if f(x) { x.left.unwrap() } else { x.right.unwrap() }
        }
        x
    }

    /// Start with the singleton interval of `self`, and extend to the right as long as `f` is true.
    ///
    /// The return value is the first leaf that `f` is false.
    /// If `f` is true even if the interval is extended to the rightmost, return `None`.
    pub fn max_right<F>(self, mut f: F) -> Option<Self>
    where
        F: FnMut(&C::Data) -> bool,
    {
        let mut x = self;

        // Phase 1: Go up.
        loop {
            let Some(p) = x.parent else {
                return None;
            };
            if p.left.unwrap() == x {
                let s = p.right.unwrap();
                if !f(&s.data) {
                    x = s;
                    break;
                }
            }
            x = p;
        }

        // Phase 2: Go down.
        while !x.is_leaf() {
            let left = x.left.unwrap();
            let right = x.right.unwrap();
            x = if f(&left.data) { right } else { left };
        }
        Some(x)
    }

    /// Start with the singleton interval of `self`, and extend to the left as long as `f` is true.
    ///
    /// The return value is the first leaf that `f` is false.
    /// If `f` is true even if the interval is extended to the leftmost, return `None`.
    pub fn min_left<F>(self, mut f: F) -> Option<Self>
    where
        F: FnMut(&C::Data) -> bool,
    {
        let mut x = self;

        // Phase 1: Go up.
        loop {
            let Some(p) = x.parent else {
                return None;
            };
            if p.right.unwrap() == x {
                let s = p.left.unwrap();
                if !f(&s.data) {
                    x = s;
                    break;
                }
            }
            x = p;
        }

        // Phase 2: Go down.
        while !x.is_leaf() {
            let left = x.left.unwrap();
            let right = x.right.unwrap();
            x = if f(&right.data) { left } else { right };
        }
        Some(x)
    }
}
impl<C: Callback> Deref for Ptr<C> {
    type Target = Node<C>;

    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}
impl<C: Callback> DerefMut for Ptr<C> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}
impl<C: Callback> Clone for Ptr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for Ptr<C> {}
impl<C: Callback> fmt::Debug for Ptr<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:02x}", self.0.as_ptr() as usize % 0x1000 / 0x10)
    }
}
impl<C: Callback> PartialEq for Ptr<C> {
    fn eq(&self, other: &Self) -> bool { self.0.as_ptr() == other.0.as_ptr() }
}
impl<C: Callback> Eq for Ptr<C> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size() {
        use std::mem::size_of;
        enum O {}
        impl Callback for O {
            type Data = ();

            fn push(_: &mut Node<Self>) {}

            fn update(_: &mut Node<Self>) {}
        }
        assert_eq!(size_of::<Node<O>>(), 32);
        assert_eq!(size_of::<Ptr<O>>(), 8);
        assert_eq!(size_of::<Tree<O>>(), 16);
    }
}

#[cfg(test)]
pub mod test_util {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;

    pub fn write<C: Callback, W: fmt::Write>(w: &mut W, tree: &Tree<C>) -> fmt::Result {
        pub fn write<C: Callback, W: fmt::Write>(w: &mut W, p: Ptr<C>) -> fmt::Result {
            if p.is_leaf() {
                write!(w, "{:?}", p)?;
            } else {
                write!(w, "(")?;
                write(w, p.left.unwrap())?;
                match p.color {
                    Color::Red => write!(w, " \x1b[31m{:?}\x1b[0m ", p)?,
                    Color::Black => write!(w, " {:?} ", p)?,
                }
                write(w, p.right.unwrap())?;
                write!(w, ")")?;
            }
            Ok(())
        }
        write!(w, "[")?;
        if let Some(root) = tree.root {
            write(w, root)?;
        }
        write!(w, "]")?;
        Ok(())
    }

    pub fn format<C: Callback>(tree: &Tree<C>) -> String {
        let mut result = String::new();
        write(&mut result, tree).unwrap();
        result
    }

    pub fn validate_except_for_data<C: Callback>(tree: &Tree<C>) {
        fn validate_except_for_data<C: Callback>(p: Ptr<C>) -> Result<u8, String> {
            if p.is_leaf() {
                (p.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| format!("Red leaf node: {:?}", p))?;
                Ok(1)
            } else {
                let left = p.left.unwrap();
                let right = p.right.unwrap();
                let left_height = validate_except_for_data(left)?;
                let right_height = validate_except_for_data(right)?;
                // Check the left parent pointers.
                (left.parent == Some(p)).then_some(()).ok_or_else(|| {
                    format!(
                        "The parent of the left child is self:\n  `p`: {:?}\n  `left`: {:?}\n  \
                         `left.parent`: {:?}",
                        p, left, left.parent
                    )
                })?;
                // Check the right parent pointers.
                (right.parent == Some(p)).then_some(()).ok_or_else(|| {
                    format!(
                        "The parent of the right child is self:\n  `p`: {:?}\n  `right`: {:?}\n  \
                         `right.parent`: {:?}",
                        p, right, right.parent
                    )
                })?;
                // Check the black height.
                (left_height == right_height).then_some(()).ok_or_else(|| {
                    format!(
                        "Black height mismatch:\n  left: {:?} (black height: {})\n right: {:?} \
                         (black height: {})",
                        left, left_height, right, right_height
                    )
                })?;
                // Check the red-red violation.
                (p.color == Color::Black || left.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "Two consecutive red nodes:\nparent: {:?}\n child: {:?}",
                            p, left
                        )
                    })?;
                (p.color == Color::Black || right.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "Two consecutive red nodes:\nparent: {:?}\n child: {:?}",
                            p, right
                        )
                    })?;
                Ok(left_height + u8::from(p.color == Color::Black))
            }
        }
        || -> Result<(), String> {
            if let Some(root) = tree.root {
                validate_except_for_data(root)?;
                (root.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| format!("The root is not black: {}", format(tree)))?;
                (root.parent.is_none()).then_some(()).ok_or_else(|| {
                    format!(
                        "The parent of the root {:?} is not None: {:?}",
                        root,
                        root.parent.unwrap(),
                    )
                })?;
            } else {
                (tree.black_height == 0).then_some(()).ok_or_else(|| {
                    format!(
                        "The black height is not zero, but the tree is empty: {}",
                        format(tree)
                    )
                })?;
            }
            Ok(())
        }()
        .unwrap_or_else(|err| panic!("validation error: {}\nin a tree {}.", err, format(tree),));
    }

    pub fn validate<C: Callback>(tree: &Tree<C>)
    where
        C::Data: Clone + PartialEq + fmt::Debug,
    {
        fn validate<C: Callback>(p: Ptr<C>) -> Result<u8, String>
        where
            C::Data: Clone + PartialEq + fmt::Debug,
        {
            if p.is_leaf() {
                (p.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| format!("Red leaf node: {:?}", p))?;
                Ok(1)
            } else {
                let left = p.left.unwrap();
                let right = p.right.unwrap();
                let left_height = validate(left)?;
                let right_height = validate(right)?;
                // Check the left parent pointers.
                (left.parent == Some(p)).then_some(()).ok_or_else(|| {
                    format!(
                        "The parent of the left child is self:\n  `p`: {:?}\n  `left`: {:?}\n  \
                         `left.parent`: {:?}",
                        p, left, left.parent
                    )
                })?;
                // Check the right parent pointers.
                (right.parent == Some(p)).then_some(()).ok_or_else(|| {
                    format!(
                        "The parent of the right child is self:\n  `p`: {:?}\n  `right`: {:?}\n  \
                         `right.parent`: {:?}",
                        p, right, right.parent
                    )
                })?;
                // Check the black height.
                (left_height == right_height).then_some(()).ok_or_else(|| {
                    format!(
                        "Black height mismatch:\n  left: {:?} (black height: {})\n right: {:?} \
                         (black height: {})",
                        left, left_height, right, right_height
                    )
                })?;
                // Check the red-red violation.
                (p.color == Color::Black || left.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "Two consecutive red nodes:\nparent: {:?}\n child: {:?}",
                            p, left
                        )
                    })?;
                (p.color == Color::Black || right.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| {
                        format!(
                            "Two consecutive red nodes:\nparent: {:?}\n child: {:?}",
                            p, right
                        )
                    })?;
                // Check the fully-updated property.
                let mut copied_node = Node {
                    parent: p.parent,
                    color: p.color,
                    left: p.left,
                    right: p.right,
                    data: p.data.clone(),
                };
                C::update(&mut copied_node);
                (p.data == copied_node.data).then_some(()).ok_or_else(|| {
                    format!(
                        "The intenal-node data is not fully-updated at {:?}:\n    Cached: {:?} \n  \
                         Expected: {:?}",
                        p, p.data, copied_node.data
                    )
                })?;
                Ok(left_height + u8::from(p.color == Color::Black))
            }
        }
        || -> Result<(), String> {
            if let Some(root) = tree.root {
                validate(root)?;
                (root.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| format!("The root is not black: {}", format(tree)))?;
                (root.parent.is_none()).then_some(()).ok_or_else(|| {
                    format!(
                        "The parent of the root is not None: {:?}",
                        root.parent.unwrap()
                    )
                })?;
            } else {
                (tree.black_height == 0).then_some(()).ok_or_else(|| {
                    format!(
                        "The black height is not zero, but the tree is empty: {}",
                        format(tree)
                    )
                })?;
            }
            Ok(())
        }()
        .unwrap_or_else(|err| panic!("validation error: {}\nin a tree {}.", err, format(tree),));
    }

    pub fn random_tree<C: Callback>(
        rng: &mut StdRng,
        black_height: u8,
        mut value: impl FnMut(&mut StdRng) -> C::Data,
        mut mul: impl FnMut(&C::Data, &C::Data) -> C::Data,
    ) -> Tree<C> {
        pub fn random_tree<C: Callback, F>(
            rng: &mut StdRng,
            black_height: u8,
            new_value: &mut impl FnMut(&mut StdRng) -> C::Data,
            mul: &mut F,
        ) -> Ptr<C>
        where
            F: FnMut(&C::Data, &C::Data) -> C::Data,
        {
            if black_height == 1 {
                return Ptr::new_leaf(new_value(rng));
            }
            match rng.gen_range(0..4) {
                // 2-node
                0 => {
                    let mut p0 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p1 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let p01 = Ptr::join_new(&mut *mul, Color::Black, p0, p1);
                    p0.parent = Some(p01);
                    p1.parent = Some(p01);
                    p01
                }
                // Left-leaning 3-node
                1 => {
                    let mut p0 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p1 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p2 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p01 = Ptr::join_new(&mut *mul, Color::Red, p0, p1);
                    let p012 = Ptr::join_new(&mut *mul, Color::Black, p01, p2);
                    p0.parent = Some(p01);
                    p1.parent = Some(p01);
                    p2.parent = Some(p012);
                    p01.parent = Some(p012);
                    p012
                }
                // Right-leaning 3-node
                2 => {
                    let mut p0 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p1 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p2 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p12 = Ptr::join_new(&mut *mul, Color::Red, p1, p2);
                    let p012 = Ptr::join_new(&mut *mul, Color::Black, p0, p12);
                    p0.parent = Some(p012);
                    p1.parent = Some(p12);
                    p2.parent = Some(p12);
                    p12.parent = Some(p012);
                    p012
                }
                // 4-node
                3 => {
                    let mut p0 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p1 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p2 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p3 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p01 = Ptr::join_new(&mut *mul, Color::Red, p0, p1);
                    let mut p23 = Ptr::join_new(&mut *mul, Color::Red, p2, p3);
                    let p0123 = Ptr::join_new(&mut *mul, Color::Black, p01, p23);
                    p0.parent = Some(p01);
                    p1.parent = Some(p01);
                    p2.parent = Some(p23);
                    p3.parent = Some(p23);
                    p01.parent = Some(p0123);
                    p23.parent = Some(p0123);
                    p0123
                }
                _ => unreachable!(),
            }
        }
        Tree {
            root: if black_height == 0 {
                None
            } else {
                Some(random_tree(rng, black_height, &mut value, &mut mul))
            },
            black_height,
        }
    }
}
