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
        debug_assert!(new.is_isolated());
        debug_assert!(new.color == Color::Red);

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

        // Fixup the tree.
        self.insert_fixup(p, new);
    }

    /// Remove the given node from the tree.
    ///
    /// # Precondition
    /// The node must be in the tree.
    fn remove(&mut self, _node: Ptr<C>) { todo!() }

    /// Insert a new node into the tree.
    fn insert_fixup(&mut self, mut p: Ptr<C>, mut x: Ptr<C>) {
        // Invariants:
        // - `x` and `p` is red
        // - The red-black property holds except for the red-red violation between `x` and `p`.
        // - The updated property holds except for the closed path from the root to `x`.
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

    /// Get the node as a reference.
    pub fn as_ref(&self) -> &Node<C> { unsafe { self.0.as_ref() } }

    /// Get the node as a mutable reference.
    pub fn as_mut(&mut self) -> &mut Node<C> { unsafe { self.0.as_mut() } }

    /// Update the node.
    pub fn update(&mut self) { C::update(*self); }

    /// Returns `true` if the node is isolated.
    pub fn is_isolated(&self) -> bool {
        self.as_ref().left.is_none()
            && self.as_ref().right.is_none()
            && self.as_ref().parent.is_none()
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
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

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

    fn write(
        w: &mut impl std::io::Write,
        tree: &Tree<TestCallback>,
        fg: &[(&'static str, Ptr<TestCallback>, ansi_term::Color)],
    ) -> std::io::Result<()> {
        unsafe fn write_ptr(
            w: &mut impl std::io::Write,
            current: Ptr<TestCallback>,
            fg: &[(&'static str, Ptr<TestCallback>, ansi_term::Color)],
        ) -> std::io::Result<()> {
            let colour = match current.color {
                Color::Red => ansi_term::Colour::Red,
                Color::Black => ansi_term::Colour::Black,
            };
            write!(w, "{}", colour.paint("("))?;
            if let Some(left) = current.left {
                write_ptr(w, left, fg)?;
            }
            let mut style = ansi_term::Style::new();
            for &(_name, ptr, colour) in fg {
                if ptr::eq(&*current, &*ptr) {
                    style = style.on(colour);
                }
            }
            style = style.fg(colour);
            write!(w, "{}", style.paint(&current.data.value.to_string()))?;
            if let Some(right) = current.right {
                write_ptr(w, right, fg)?;
            }
            write!(w, "{}", colour.paint(")"))?;
            Ok(())
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
            write!(w, ": ")?;
        }
        unsafe {
            if let Some(root) = tree.root {
                write_ptr(w, root, fg)?;
            }
        }
        Ok(())
    }

    fn format(
        tree: &Tree<TestCallback>,
        fg: &[(&'static str, Ptr<TestCallback>, ansi_term::Color)],
    ) -> String {
        let mut buf = Vec::new();
        write(&mut buf, tree, fg).unwrap();
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
            assert_eq!(to_vec(&tree), vec, "{}", format(&tree, &[]));
            validate(&tree).unwrap_or_else(|err| panic!("{}\n{}", err, format(&tree, &[])));
        }
    }
}
