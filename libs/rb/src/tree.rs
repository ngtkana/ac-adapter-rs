#![allow(dead_code)]
use std::fmt;
use std::hint::unreachable_unchecked;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ptr::NonNull;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}
pub trait Callback: Sized {
    type LeafData;
    type BeefData;
    fn push(_: &mut BeefSteak<Self>);
    fn update(_: &mut BeefSteak<Self>);
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
    pub fn binary_search<F: FnMut(BeefPtr<C>) -> bool>(&self, mut f: F) -> Option<LeafPtr<C>> {
        let mut node = self.root?;
        while let Steak::Beef(beef) = &node.steak {
            node = if f(BeefPtr(node.0)) { beef.left } else { beef.right };
        }
        Some(LeafPtr(node.0))
    }

    /// Insert a leaf node.
    ///
    /// # Abount `position`
    ///
    /// `position` is `None` if and only if the tree is empty.
    /// If `position` is `Some((leaf, true))`, the new leaf will be inserted to the left of `leaf`.
    pub fn insert(
        &mut self,
        position: Option<(LeafPtr<C>, bool)>,
        mut new: LeafPtr<C>,
        feed_beef: impl FnOnce(LeafPtr<C>, LeafPtr<C>) -> BeefPtr<C>,
    ) {
        // Handle the case where the tree is empty.
        let Some((mut s, result)) = position else {
            self.root = Some(new.upcast());
            self.black_height = 1;
            return;
        };

        // Join `leaf` and `s` with `b`, and transplant `b` at the original position of `s`.
        let b = if result { feed_beef(new, s) } else { feed_beef(s, new) };
        self.transplant(s.upcast(), b.upcast());
        new.parent = Some(b);
        s.parent = Some(b);

        // Fix the red-red violation.
        self.fix_red(b);
    }

    /// Remove a leaf node.
    pub fn remove(&mut self, mut position: LeafPtr<C>, eat_beef: impl FnOnce(BeefPtr<C>)) {
        // Handle the case where the tree has only one node.
        let Some(p) = position.parent else {
            self.root = None;
            self.black_height = 0;
            return;
        };
        // Transplant `s` at the original position of `p`.
        let s = if position == p.left() { p.right() } else { p.left() };
        self.transplant(p.upcast(), s);

        // We will remove the beaf `p`, so if `p` is black, we need to fix the black-height violation.
        if p.color == Color::Black {
            self.fix_black(s);
        } else {
            s.update_ancestors();
        }

        // Remove `p` from the tree.
        position.parent = None;

        // Catch the no longer needed beef.
        eat_beef(p);
    }

    /// Fix the red-red violation.
    ///
    /// # Precondition
    ///
    /// - `x` and its parent may be a red-red pair, but this is the only violation.
    /// - `x` and its ancestors may not be fully-updatated, but other nodes are fully-updated.
    fn fix_red(&mut self, mut x: BeefPtr<C>) {
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
            if p == pp.left() {
                // Case 1.1: `pp` is a 5-node.
                // Split the 5-node and continue.
                if pp.right().color == Color::Red {
                    let mut s = pp.right();
                    p.color = Color::Black;
                    s.color = Color::Black;
                    pp.color = Color::Red;
                    x.update();
                    p.update();
                    x = pp;
                }
                // Case 1.2: `pp` is a splayed left-leaning 4-node.
                // Finish by fixing this node.
                else if x == p.right() {
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
                if pp.left().color == Color::Red {
                    let mut s = pp.left();
                    p.color = Color::Black;
                    s.color = Color::Black;
                    pp.color = Color::Red;
                    x.update();
                    p.update();
                    x = pp;
                }
                // Case 2.2: `pp` is a splayed right-leaning 4-node.
                // Finish by fixing this node.
                else if x == p.left() {
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
        x.upcast().update_ancestors();
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
            if p.left() == x {
                let mut s = p.right().as_beef_ptr();
                // If `p` is a right-leaning 3-node, lean it to the left.
                if s.color == Color::Red {
                    s.color = Color::Black;
                    p.color = Color::Red;
                    self.rotate_left(p);
                    s = p.right().as_beef_ptr();
                }
                match (s.left().color, s.right().color) {
                    // Case 1.1: `s` is a 2-node.
                    // Join two 2-nodes `x` and `s` and continue.
                    (Color::Black, Color::Black) => {
                        s.color = Color::Red;
                        x = p.upcast();
                        x.as_beef_ptr().update();
                    }
                    // Case 1.2: `s` is a left-leaning 3-node.
                    // Adpot a child from `s` and now the violation is fixed.
                    (Color::Red, Color::Black) => {
                        let mut c = s.left().as_beef_ptr();
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
                        s.right_mut().color = Color::Black;
                        self.rotate_left(p);
                        p.update();
                        break;
                    }
                }
            }
            // Case2: `x` is a right child.
            else {
                let mut s = p.left().as_beef_ptr();
                // If `p` is a left-leaning 3-node, lean it to the right.
                if s.color == Color::Red {
                    s.color = Color::Black;
                    p.color = Color::Red;
                    self.rotate_right(p);
                    s = p.left().as_beef_ptr();
                }
                match (s.left().color, s.right().color) {
                    // Case 2.1: `s` is a 2-node.
                    // Join two 2-nodes `x` and `s` and continue.
                    (Color::Black, Color::Black) => {
                        s.color = Color::Red;
                        x = p.upcast();
                        x.as_beef_ptr().update();
                    }
                    // Case 2.2: `s` is a right-leaning 3-node.
                    // Adpot a child from `s` and now the violation is fixed.
                    (Color::Black, Color::Red) => {
                        let mut c = s.right().as_beef_ptr();
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
                        s.left_mut().color = Color::Black;
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
    fn rotate_left(&mut self, mut l: BeefPtr<C>) {
        // Get the nodes
        let mut r = l.right().as_beef_ptr();
        let mut c = r.left();

        // Connect `p` and `r`
        self.transplant(l.upcast(), r.upcast());

        // Connect `r` and `l`
        *r.left_mut() = l.upcast();
        l.parent = Some(r);

        // Connect `l` and `c`
        *l.right_mut() = c;
        c.parent = Some(l);
    }

    /// Rotate the tree to the right.
    fn rotate_right(&mut self, mut r: BeefPtr<C>) {
        // Get the nodes
        let mut l = r.left().as_beef_ptr();
        let mut c = l.right();

        // Connect `p` and `l`
        self.transplant(r.upcast(), l.upcast());

        // Connect `l` and `r`
        *l.right_mut() = r.upcast();
        r.parent = Some(l);

        // Connect `r` and `c`
        *r.left_mut() = c;
        c.parent = Some(r);
    }

    fn transplant(&mut self, position: Ptr<C>, mut new: Ptr<C>) {
        new.parent = position.parent;
        if let Some(mut p) = position.parent {
            if position == p.left() {
                *p.left_mut() = new;
            } else {
                *p.right_mut() = new;
            }
        } else {
            self.root = Some(new);
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
    parent: Option<BeefPtr<C>>,
    color: Color,
    pub steak: Steak<C>,
}
pub struct BeefSteak<C: Callback> {
    pub data: C::BeefData,
    pub left: Ptr<C>,
    pub right: Ptr<C>,
}
pub enum Steak<C: Callback> {
    Leaf(C::LeafData),
    Beef(BeefSteak<C>),
}
pub struct Ptr<C: Callback>(NonNull<Node<C>>);
impl<C: Callback> Ptr<C> {
    fn update_ancestors(self) {
        let mut p = self.parent;
        while let Some(mut pp) = p {
            C::update(pp.steak_mut());
            p = pp.parent;
        }
    }

    /// Downcast to [`BeefPtr`].
    /// This is needed in `fix_black()`.
    fn as_beef_ptr(self) -> BeefPtr<C> {
        debug_assert!(matches!(self.steak, Steak::Beef(_)));
        BeefPtr(self.0)
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
pub struct LeafPtr<C: Callback>(NonNull<Node<C>>);
impl<C: Callback> LeafPtr<C> {
    pub fn new(data: C::LeafData) -> Self {
        Self(
            NonNull::new(Box::into_raw(Box::new(Node {
                parent: None,
                color: Color::Black,
                steak: Steak::<C>::Leaf(data),
            })))
            .unwrap(),
        )
    }

    pub fn free(self) -> C::LeafData {
        unsafe {
            match Box::from_raw(self.0.as_ptr()).steak {
                Steak::Leaf(data) => data,
                Steak::Beef(_) => unreachable_unchecked(),
            }
        }
    }

    pub fn upcast(self) -> Ptr<C> { Ptr(self.0) }

    pub fn data(&self) -> &C::LeafData {
        debug_assert!(matches!(self.steak, Steak::Leaf(_)));
        unsafe {
            match &self.steak {
                Steak::Leaf(leaf) => leaf,
                Steak::Beef(_) => unreachable_unchecked(),
            }
        }
    }

    fn data_mut(&mut self) -> &mut C::LeafData {
        debug_assert!(matches!(self.steak, Steak::Leaf(_)));
        unsafe {
            match &mut self.steak {
                Steak::Leaf(leaf) => leaf,
                Steak::Beef(_) => unreachable_unchecked(),
            }
        }
    }
}
impl<C: Callback> Deref for LeafPtr<C> {
    type Target = Node<C>;

    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}
impl<C: Callback> DerefMut for LeafPtr<C> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}
impl<C: Callback> Clone for LeafPtr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for LeafPtr<C> {}
impl<C: Callback> fmt::Debug for LeafPtr<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:02x}", self.0.as_ptr() as usize % 0x1000 / 0x10)
    }
}
impl<C: Callback> PartialEq for LeafPtr<C> {
    fn eq(&self, other: &Self) -> bool { self.0.as_ptr() == other.0.as_ptr() }
}
impl<C: Callback> Eq for LeafPtr<C> {}
impl<C: Callback> PartialEq<Ptr<C>> for LeafPtr<C> {
    fn eq(&self, other: &Ptr<C>) -> bool { self.0.as_ptr() == other.0.as_ptr() }
}
pub struct BeefPtr<C: Callback>(NonNull<Node<C>>);
impl<C: Callback> BeefPtr<C> {
    pub fn new(data: C::BeefData, left: Ptr<C>, right: Ptr<C>) -> Self {
        Self(
            NonNull::new(Box::into_raw(Box::new(Node {
                parent: None,
                color: Color::Red,
                steak: Steak::<C>::Beef(BeefSteak { data, left, right }),
            })))
            .unwrap(),
        )
    }

    pub fn free(self) { unsafe { drop(Box::from_raw(self.0.as_ptr())) }; }

    fn upcast(self) -> Ptr<C> { Ptr(self.0) }

    fn update(mut self) { C::update(self.steak_mut()); }

    pub fn data(&self) -> &C::BeefData {
        debug_assert!(matches!(self.steak, Steak::Beef(_)));
        unsafe {
            match &self.steak {
                Steak::Beef(beef) => &beef.data,
                Steak::Leaf(_) => unreachable_unchecked(),
            }
        }
    }

    pub fn data_mut(&mut self) -> &mut C::BeefData {
        debug_assert!(matches!(self.steak, Steak::Beef(_)));
        unsafe {
            match &mut self.steak {
                Steak::Beef(beef) => &mut beef.data,
                Steak::Leaf(_) => unreachable_unchecked(),
            }
        }
    }

    fn steak(&self) -> &BeefSteak<C> {
        debug_assert!(matches!(self.steak, Steak::Beef(_)));
        unsafe {
            match &self.steak {
                Steak::Beef(beef) => beef,
                Steak::Leaf(_) => unreachable_unchecked(),
            }
        }
    }

    fn steak_mut(&mut self) -> &mut BeefSteak<C> {
        debug_assert!(matches!(self.steak, Steak::Beef(_)));
        unsafe {
            match &mut self.steak {
                Steak::Beef(beef) => beef,
                Steak::Leaf(_) => unreachable_unchecked(),
            }
        }
    }

    pub fn left(self) -> Ptr<C> { self.steak().left }

    pub fn right(self) -> Ptr<C> { self.steak().right }

    fn left_mut(&mut self) -> &mut Ptr<C> { &mut self.steak_mut().left }

    fn right_mut(&mut self) -> &mut Ptr<C> { &mut self.steak_mut().right }
}
impl<C: Callback> Deref for BeefPtr<C> {
    type Target = Node<C>;

    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}
impl<C: Callback> DerefMut for BeefPtr<C> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}
impl<C: Callback> Clone for BeefPtr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for BeefPtr<C> {}
impl<C: Callback> fmt::Debug for BeefPtr<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:02x}", self.0.as_ptr() as usize % 0x1000 / 0x10)
    }
}
impl<C: Callback> PartialEq for BeefPtr<C> {
    fn eq(&self, other: &Self) -> bool { self.0.as_ptr() == other.0.as_ptr() }
}
impl<C: Callback> Eq for BeefPtr<C> {}
impl<C: Callback> PartialEq<Ptr<C>> for BeefPtr<C> {
    fn eq(&self, other: &Ptr<C>) -> bool { self.0.as_ptr() == other.0.as_ptr() }
}

#[cfg(test)]
mod tests {
    use super::test_util::for_each;
    use super::test_util::validate;
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[test]
    fn test_optimal_size() {
        use std::mem::size_of;
        enum O {}
        impl Callback for O {
            type BeefData = ();
            type LeafData = ();

            fn push(_: &mut BeefSteak<Self>) {}

            fn update(_: &mut BeefSteak<Self>) {}
        }
        assert_eq!(size_of::<Node<O>>(), 32);
        assert_eq!(size_of::<Ptr<O>>(), 8);
        assert_eq!(size_of::<Steak<O>>(), 16);
        assert_eq!(size_of::<BeefSteak<O>>(), 16);
        assert_eq!(size_of::<Tree<O>>(), 16);
    }

    #[test]
    fn test_insert_remove() {
        #[derive(Clone, Copy, Debug, PartialEq)]
        struct BeefData {
            start: usize,
            end: usize,
        }
        enum C {}
        impl Callback for C {
            type BeefData = BeefData;
            type LeafData = usize;

            fn update(x: &mut BeefSteak<Self>) {
                x.data.start = match &x.left.steak {
                    Steak::Leaf(leaf) => *leaf,
                    Steak::Beef(beef) => beef.data.start,
                };
                x.data.end = match &x.right.steak {
                    Steak::Leaf(leaf) => *leaf,
                    Steak::Beef(beef) => beef.data.end,
                };
            }

            fn push(_: &mut BeefSteak<Self>) {}
        }
        fn feed_beef(left: LeafPtr<C>, right: LeafPtr<C>) -> BeefPtr<C> {
            BeefPtr::new(
                BeefData {
                    start: *left.data(),
                    end: *right.data(),
                },
                left.upcast(),
                right.upcast(),
            )
        }
        fn eat_beef(beef: BeefPtr<C>) { unsafe { drop(Box::from_raw(beef.0.as_ptr())) }; }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let nodes = (0..20).map(LeafPtr::new).collect::<Vec<_>>();
            let mut used = vec![false; nodes.len()];
            let mut tree = Tree::<C>::new();
            for _ in 0..20 {
                let i = rng.gen_range(0..nodes.len());
                if used[i] {
                    tree.remove(nodes[i], eat_beef);
                    used[i] = false;
                } else {
                    let position = tree
                        .binary_search(|beef| {
                            let start = match &beef.right().steak {
                                Steak::Leaf(leaf) => *leaf,
                                Steak::Beef(beef) => beef.data.start,
                            };
                            i < start
                        })
                        .map(|leaf| {
                            let start = *leaf.data();
                            (leaf, i < start)
                        });
                    tree.insert(position, nodes[i], feed_beef);
                    used[i] = true;
                }
                let mut values = Vec::new();
                for_each(&tree, |p| match &p.steak {
                    Steak::Leaf(leaf) => values.push(*leaf),
                    Steak::Beef(_beef) => {}
                });
                let expected_values = (0..nodes.len())
                    .filter(|&i| used[i])
                    .map(|i| *nodes[i].data())
                    .collect::<Vec<_>>();
                assert_eq!(values, expected_values);
                validate(&tree);
            }
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;

    pub fn for_each<C: Callback, F: FnMut(Ptr<C>)>(tree: &Tree<C>, mut f: F) {
        fn for_each<C: Callback, F: FnMut(Ptr<C>)>(p: Ptr<C>, f: &mut F) {
            match &p.steak {
                Steak::Leaf(_) => f(p),
                Steak::Beef(beef) => {
                    for_each(beef.left, f);
                    f(p);
                    for_each(beef.right, f);
                }
            }
        }
        if let Some(root) = tree.root {
            for_each(root, &mut f);
        }
    }

    pub fn write<C: Callback, W: fmt::Write, F: FnMut(Ptr<C>) -> T, T: AsRef<str>>(
        w: &mut W,
        tree: &Tree<C>,
        mut f: F,
    ) -> fmt::Result {
        pub fn write<C: Callback, W: fmt::Write, F: FnMut(Ptr<C>) -> T, T: AsRef<str>>(
            w: &mut W,
            p: Ptr<C>,
            f: &mut F,
        ) -> fmt::Result {
            match &p.steak {
                Steak::Leaf(_) => write!(w, "{}", f(p).as_ref())?,
                Steak::Beef(beef) => {
                    write!(w, "(")?;
                    write(w, beef.left, f)?;
                    match p.color {
                        Color::Red => write!(w, " \x1b[31m{}\x1b[0m ", f(p).as_ref())?,
                        Color::Black => write!(w, " {} ", f(p).as_ref())?,
                    }
                    write(w, beef.right, f)?;
                    write!(w, ")")?;
                }
            }
            Ok(())
        }
        write!(w, "[")?;
        if let Some(root) = tree.root {
            write(w, root, &mut f)?;
        }
        write!(w, "]")?;
        Ok(())
    }

    pub fn format<C: Callback, F: FnMut(Ptr<C>) -> T, T: AsRef<str>>(
        tree: &Tree<C>,
        mut f: F,
    ) -> String {
        let mut result = String::new();
        write(&mut result, tree, &mut f).unwrap();
        result
    }

    pub fn validate<C: Callback>(tree: &Tree<C>)
    where
        C::BeefData: Copy + PartialEq + fmt::Debug,
    {
        fn validate<C: Callback>(p: Ptr<C>) -> Result<u8, String>
        where
            C::BeefData: Copy + PartialEq + fmt::Debug,
        {
            match &p.steak {
                Steak::Leaf(_) => {
                    (p.color == Color::Black)
                        .then_some(())
                        .ok_or_else(|| format!("Red leaf node: {:?}", p))?;
                    Ok(1)
                }
                Steak::Beef(b) => {
                    let left = b.left;
                    let right = b.right;
                    let left_height = validate(left)?;
                    let right_height = validate(right)?;
                    // Check the black height.
                    (left_height == right_height).then_some(()).ok_or_else(|| {
                        format!(
                            "Black height mismatch:\n  left: {:?} (black height: {})\n right: \
                             {:?} (black height: {})",
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
                    let mut b_copied = BeefSteak {
                        left: b.left,
                        right: b.right,
                        data: b.data,
                    };
                    C::update(&mut b_copied);
                    assert_eq!(b.data, b_copied.data);
                    Ok(left_height + u8::from(p.color == Color::Black))
                }
            }
        }
        if let Some(root) = tree.root {
            validate(root).unwrap_or_else(|err| {
                panic!(
                    "validation error: {}\nin a tree {}.",
                    err,
                    format(tree, |p| format!("{:?}", p))
                )
            });
        }
    }

    pub fn random_tree<C: Callback>(
        rng: &mut StdRng,
        black_height: u8,
        mut new_leaf: impl FnMut() -> LeafPtr<C>,
        mut new_beef: impl FnMut(Ptr<C>, Ptr<C>) -> BeefPtr<C>,
    ) -> Tree<C> {
        pub fn random_tree<C: Callback>(
            rng: &mut StdRng,
            black_height: u8,
            mut new_leaf: &mut impl FnMut() -> LeafPtr<C>,
            mut new_beef: &mut impl FnMut(Ptr<C>, Ptr<C>) -> BeefPtr<C>,
        ) -> Ptr<C> {
            if black_height == 1 {
                return new_leaf().upcast();
            }
            match rng.gen_range(0..4) {
                // 2-node
                0 => {
                    let p0 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p1 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let mut p01 = new_beef(p0, p1).upcast();
                    p01.color = Color::Black;
                    p01
                }
                // Left-leaning 3-node
                1 => {
                    let p0 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p1 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p2 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p01 = new_beef(p0, p1).upcast();
                    let mut p012 = new_beef(p01, p2).upcast();
                    p012.color = Color::Black;
                    p012
                }
                // Right-leaning 3-node
                2 => {
                    let p0 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p1 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p2 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p12 = new_beef(p1, p2).upcast();
                    let mut p012 = new_beef(p0, p12).upcast();
                    p012.color = Color::Black;
                    p012
                }
                // 4-node
                3 => {
                    let p0 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p1 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p2 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p3 = random_tree(rng, black_height - 1, &mut new_leaf, &mut new_beef);
                    let p01 = new_beef(p0, p1).upcast();
                    let p23 = new_beef(p2, p3).upcast();
                    let mut p0123 = new_beef(p01, p23).upcast();
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
                Some(random_tree(rng, black_height, &mut new_leaf, &mut new_beef))
            },
            black_height,
        }
    }
}
