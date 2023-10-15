//! A red-black tree with `NonNull` and `Callback`.
use std::cmp::Ordering;
use std::ops;
use std::ptr::NonNull;
use std::ptr::{self};

/// A color of a node in a red-black tree.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Color {
    Red,
    Black,
}

/// A callback for a node in a red-black tree.
pub trait Callback: Sized {
    /// The data stored in the node.
    type Data;
    /// The callback function called when it goes down the tree.
    fn push(node: Ptr<Self>);
    /// The callback function called when it goes up the tree.
    fn update(node: Ptr<Self>);
}

/// A red-black tree.
#[allow(dead_code)]
pub struct Tree<C: Callback> {
    root: Option<Ptr<C>>,
    black_height: u8,
}
#[allow(dead_code)]
impl<C: Callback> Tree<C> {
    /// Create a new empty tree.
    pub fn new() -> Self { Self::default() }

    /// Returns `true` if the tree is empty.
    pub fn is_empty(&self) -> bool { self.root.is_none() }

    /// Binary search the tree.
    fn binary_search<F>(&self, mut f: F) -> Option<Ptr<C>>
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
    pub fn front(&self) -> Option<Ptr<C>> {
        let mut p = self.root;
        while let Some(p0) = p {
            p = p0.left;
        }
        p
    }

    /// Find the rightmost node.
    pub fn back(&self) -> Option<Ptr<C>> {
        let mut p = self.root;
        while let Some(p0) = p {
            p = p0.right;
        }
        p
    }

    /// Insert a new node into the tree.
    ///
    /// # Precondition
    /// The new node must be isolated and red.
    pub fn partition_point_insert(
        &mut self,
        mut new: Ptr<C>,
        mut pred: impl FnMut(Ptr<C>) -> bool,
    ) {
        // Make sure the new node is isolated and red.
        debug_assert!(new.is_isolated_and_red());

        // Handle the empty tree case.
        let Some(root) = self.root else {
            debug_assert!(self.black_height == 0);
            self.black_height = 1;
            new.color = Color::Black;
            self.root = Some(new);
            return;
        };

        // Find the insertion point.
        let (mut p, result) = root.partition_point(&mut pred);

        // Insert the new node.
        *(if result { &mut p.as_mut().right } else { &mut p.as_mut().left }) = Some(new);
        new.as_mut().parent = Some(p);

        // Fixup the red-red violation.
        self.fix_red(p, new);
    }

    /// Remove the given node from the tree.
    ///
    /// # Precondition
    /// `remove` must be in the tree.
    pub fn remove(&mut self, mut z: Ptr<C>) {
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
    pub fn transplant(&mut self, u: Ptr<C>, v: Option<Ptr<C>>) {
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

/// Get the color of a node.
fn color<C: Callback>(p: Option<Ptr<C>>) -> Color { p.map_or(Color::Black, |p| p.as_ref().color) }

/// Get the pointer to a node.
fn as_ptr<C: Callback>(p: Option<Ptr<C>>) -> *mut Node<C> {
    p.map_or(ptr::null_mut(), |p| p.0.as_ptr())
}

/// A node in a red-black tree.
#[allow(dead_code)]
pub struct Node<C: Callback> {
    data: C::Data,
    left: Option<Ptr<C>>,
    right: Option<Ptr<C>>,
    parent: Option<Ptr<C>>,
    color: Color,
}
/// Non-dangling pointer to a node in a red-black tree.
#[allow(dead_code)]
pub struct Ptr<C: Callback>(NonNull<Node<C>>);
#[allow(dead_code)]
impl<C: Callback> Ptr<C> {
    /// Create a new isolated red [`Ptr`] from a [`C::Data`].
    pub fn new(data: C::Data) -> Self {
        Self(
            NonNull::new(Box::into_raw(Box::new(Node {
                data,
                left: None,
                right: None,
                parent: None,
                color: Color::Red,
            })))
            .unwrap(),
        )
    }

    /// Give the ownership of the node to the caller.
    pub fn into_box(self) -> Box<Node<C>> { unsafe { Box::from_raw(self.0.as_ptr()) } }

    /// Get the node as a reference.
    pub fn as_ref(&self) -> &Node<C> { unsafe { self.0.as_ref() } }

    /// Get the node as a mutable reference.
    pub fn as_mut(&mut self) -> &mut Node<C> { unsafe { self.0.as_mut() } }

    /// Update the node.
    pub fn update(&mut self) { C::update(*self); }

    /// Returns `true` if the node is isolated.
    pub fn is_isolated_and_red(&self) -> bool {
        self.as_ref().left.is_none()
            && self.as_ref().right.is_none()
            && self.as_ref().parent.is_none()
            && self.as_ref().color == Color::Red
    }

    /// Change the node to an isolated red node.
    pub fn isolate_and_red(&mut self) {
        self.as_mut().left = None;
        self.as_mut().right = None;
        self.as_mut().parent = None;
        self.as_mut().color = Color::Red;
    }

    /// Returns the parent `p` of the partition point according to the given predicate, and `pred(p)`.
    pub fn partition_point<P>(&self, mut pred: P) -> (Ptr<C>, bool)
    where
        P: FnMut(Ptr<C>) -> bool,
    {
        let mut p = *self;
        let mut result = pred(p);
        let mut option_x = if result { p.as_ref().right } else { p.as_ref().left };
        while let Some(x) = option_x {
            p = x;
            result = pred(p);
            option_x = if result { p.as_ref().right } else { p.as_ref().left };
        }
        (p, result)
    }
}
impl<C: Callback> Clone for Ptr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for Ptr<C> {}
impl<C: Callback> ops::Deref for Ptr<C> {
    type Target = Node<C>;

    fn deref(&self) -> &Self::Target { self.as_ref() }
}
impl<C: Callback> ops::DerefMut for Ptr<C> {
    fn deref_mut(&mut self) -> &mut Self::Target { self.as_mut() }
}
impl<C: Callback> PartialEq for Ptr<C> {
    fn eq(&self, other: &Self) -> bool { ptr::eq(self.as_ref(), other.as_ref()) }
}
impl<C: Callback> Eq for Ptr<C> {}

#[cfg(test)]
pub mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;
    use std::borrow::Cow;

    const MODULO: u64 = 998244353;

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

    fn validate(tree: &Tree<TestCallback>) -> Result<(), String> {
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

            Ok(left_black_height + (ptr.color == Color::Black) as u8)
        }
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

    pub fn write<'a, C: Callback, F, S>(
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
            let mut i = 0;
            for &(name, _ptr, colour) in fg {
                if i > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{}", ansi_term::Style::new().on(colour).paint(name))?;
                i += 1;
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

    pub fn format<'a, C: Callback, F, S>(
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
            tree.partition_point_insert(Ptr::new(Data::new(value)), |p| p.data.value < value);
            assert_eq!(
                to_vec(&tree),
                vec,
                "{}",
                format(&tree, |data| data.value.to_string(), &[])
            );
            validate(&tree).unwrap_or_else(|err| {
                panic!(
                    "{}\n{}",
                    err,
                    format(&tree, |data| data.value.to_string(), &[])
                )
            });
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
                    tree.partition_point_insert(Ptr::new(Data::new(value)), |n| {
                        n.data.value < value
                    });
                }
                assert_eq!(to_vec(&tree), expected);
                validate(&tree).unwrap_or_else(|err| {
                    panic!(
                        "{}\n{}",
                        err,
                        format(&tree, |data| data.value.to_string(), &[])
                    )
                });
            }
        }
    }
}
