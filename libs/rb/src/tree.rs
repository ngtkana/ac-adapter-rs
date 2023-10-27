#![allow(dead_code)]
use std::cmp::Ordering;
use std::fmt;
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
    root: Option<Ptr<C>>,
    black_height: u8,
}
impl<C: Callback> Tree<C> {
    /// Create a new empty red-black tree.
    fn new() -> Self { Self::default() }

    /// Returns the root node.
    pub fn root(&self) -> Option<Ptr<C>> { self.root }

    /// Binary search for a leaf node.
    /// Returns `None` if the tree is empty.
    ///
    /// # About `f`
    ///
    /// If `f` returns `true`, the search continues to the left child because this `beef` is too big.
    pub fn binary_search<F: FnMut(Ptr<C>) -> bool>(&self, mut f: F) -> Option<Ptr<C>> {
        let mut x = self.root?;
        while !x.is_leaf() {
            x = if f(x) { x.left.unwrap() } else { x.right.unwrap() }
        }
        Some(x)
    }

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
            Ptr::new_red_beef(mul, new, s)
        } else {
            Ptr::new_red_beef(mul, s, new)
        };
        self.transplant(s, b);
        s.parent = Some(b);
        new.parent = Some(b);

        // Fix the red-red violation.
        self.fix_red(b);
    }

    pub fn append(&mut self, other: &mut Self, mul: impl FnOnce(&C::Data, &C::Data) -> C::Data) {
        let Some(mut left) = self.root else {
            std::mem::swap(self, other);
            return;
        };
        let Some(mut right) = other.root else {
            return;
        };
        match self.black_height.cmp(&other.black_height) {
            // Case 1: Two trees have the same black height.
            // Join the roots.
            Ordering::Equal => {
                let mut b = Ptr::new_red_beef(mul, left, right);
                left.parent = Some(b);
                right.parent = Some(b);
                b.color = Color::Black;
                self.root = Some(b);
                self.black_height += 1;
            }
            // Case 2: The left tree has a smaller black height.
            // Slide down along the left spine of the right tree, join, and fix the red-red violation.
            Ordering::Less => {
                let mut h = other.black_height;
                loop {
                    if right.color == Color::Black {
                        if h == self.black_height {
                            break;
                        }
                        h -= 1;
                    }
                    right = right.left.unwrap();
                }
                let mut p = right.parent.unwrap();
                let mut b = Ptr::new_red_beef(mul, left, right);
                left.parent = Some(b);
                right.parent = Some(b);
                b.color = Color::Red;
                *p.left.as_mut().unwrap() = b;
                b.parent = Some(p);
                self.root = other.root;
                self.black_height = other.black_height;
                self.fix_red(b);
            }
            // Case 3: The right tree has a smaller black height.
            // Slide down along the right spine of the left tree, join, and fix the red-red violation.
            Ordering::Greater => {
                let mut h = self.black_height;
                loop {
                    if left.color == Color::Black {
                        if h == other.black_height {
                            break;
                        }
                        h -= 1;
                    }
                    left = left.right.unwrap();
                }
                let mut p = left.parent.unwrap();
                let mut b = Ptr::new_red_beef(mul, left, right);
                left.parent = Some(b);
                right.parent = Some(b);
                b.color = Color::Red;
                *p.right.as_mut().unwrap() = b;
                b.parent = Some(p);
                self.fix_red(b);
            }
        }
        // I don't forget to clear the other tree.
        other.root = None;
        other.black_height = 0;
    }

    /// Remove a leaf node.
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

        // Catch the no longer needed beef.
        p.free();
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

    pub fn from_slice_of_leaves<F>(leaves: &[Ptr<C>], mut feed_beef: F) -> Self
    where
        F: FnMut(Ptr<C>, Ptr<C>) -> Ptr<C>,
    {
        fn from_slice_of_leaves<C: Callback, F>(
            leaves: &[Ptr<C>],
            feed_beef: &mut F,
        ) -> (Ptr<C>, u8)
        where
            F: FnMut(Ptr<C>, Ptr<C>) -> Ptr<C>,
        {
            let mut leaves = leaves.to_vec();
            let mut black_height = 1;
            let mut n = leaves.len();
            while n != 1 {
                for i in 0..n / 2 {
                    if 2 * i + 3 == n {
                        let mut left = leaves[2 * i];
                        let mut center = leaves[2 * i + 1];
                        let mut right = leaves[2 * i + 2];
                        let mut b0 = feed_beef(left, center);
                        left.parent = Some(b0);
                        center.parent = Some(b0);
                        let mut b1 = feed_beef(b0, right);
                        b1.color = Color::Black;
                        b0.parent = Some(b1);
                        right.parent = Some(b1);
                        leaves[i] = b1;
                    } else {
                        let mut left = leaves[2 * i];
                        let mut right = leaves[2 * i + 1];
                        let mut b = feed_beef(left, right);
                        b.color = Color::Black;
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
        let (root, black_height) = from_slice_of_leaves(leaves, &mut feed_beef);
        Self {
            root: Some(root),
            black_height,
        }
    }
}
impl<C: Callback> Default for Tree<C> {
    fn default() -> Self {
        Self {
            root: None,
            black_height: 0,
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

    pub fn is_beef(&self) -> bool { !self.is_leaf() }

    fn update(&mut self) {
        debug_assert!(self.is_beef());
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

    pub fn new_red_beef(
        mul: impl FnOnce(&C::Data, &C::Data) -> C::Data,
        left: Self,
        right: Self,
    ) -> Self {
        let data = mul(&left.data, &right.data);
        // NOTE: do not update `{left, right}.parent`.
        // It will delete the information that is needed to transplant the new node.
        Self(NonNull::from(Box::leak(Box::new(Node {
            parent: None,
            color: Color::Red,
            left: Some(left),
            right: Some(right),
            data,
        }))))
    }

    pub fn free(self) -> C::Data {
        let data = unsafe { std::ptr::read(&self.data) };
        unsafe { Box::from_raw(self.0.as_ptr()) };
        data
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

    pub fn validate<C: Callback>(tree: &Tree<C>)
    where
        C::Data: Copy + PartialEq + fmt::Debug,
    {
        fn validate<C: Callback>(p: Ptr<C>) -> Result<u8, String>
        where
            C::Data: Copy + PartialEq + fmt::Debug,
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
                    data: p.data,
                };
                C::update(&mut copied_node);
                (p.data == copied_node.data).then_some(()).ok_or_else(|| {
                    format!(
                        "The beef data is not fully-updated at {:?}:\n    Cached: {:?} \n  \
                         Expected: {:?}",
                        p, p.data, copied_node.data
                    )
                })?;
                Ok(left_height + u8::from(p.color == Color::Black))
            }
        }
        if let Some(root) = tree.root {
            validate(root).unwrap_or_else(|err| {
                panic!("validation error: {}\nin a tree {}.", err, format(tree),)
            });
        }
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
                    let mut p01 = Ptr::new_red_beef(&mut *mul, p0, p1);
                    p0.parent = Some(p01);
                    p1.parent = Some(p01);
                    p01.color = Color::Black;
                    p01
                }
                // Left-leaning 3-node
                1 => {
                    let mut p0 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p1 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p2 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p01 = Ptr::new_red_beef(&mut *mul, p0, p1);
                    let mut p012 = Ptr::new_red_beef(&mut *mul, p01, p2);
                    p0.parent = Some(p01);
                    p1.parent = Some(p01);
                    p2.parent = Some(p012);
                    p01.parent = Some(p012);
                    p012.color = Color::Black;
                    p012
                }
                // Right-leaning 3-node
                2 => {
                    let mut p0 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p1 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p2 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p12 = Ptr::new_red_beef(&mut *mul, p1, p2);
                    let mut p012 = Ptr::new_red_beef(&mut *mul, p0, p12);
                    p0.parent = Some(p012);
                    p1.parent = Some(p12);
                    p2.parent = Some(p12);
                    p12.parent = Some(p012);
                    p012.color = Color::Black;
                    p012
                }
                // 4-node
                3 => {
                    let mut p0 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p1 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p2 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p3 = random_tree(rng, black_height - 1, new_value, &mut *mul);
                    let mut p01 = Ptr::new_red_beef(&mut *mul, p0, p1);
                    let mut p23 = Ptr::new_red_beef(&mut *mul, p2, p3);
                    let mut p0123 = Ptr::new_red_beef(&mut *mul, p01, p23);
                    p0.parent = Some(p01);
                    p1.parent = Some(p01);
                    p2.parent = Some(p23);
                    p3.parent = Some(p23);
                    p01.parent = Some(p0123);
                    p23.parent = Some(p0123);
                    p0123.color = Color::Black;
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
