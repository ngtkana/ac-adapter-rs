#![allow(dead_code)]
#![allow(missing_docs)]
use std::ops::Deref;
use std::ops::DerefMut;
use std::ptr::NonNull;

trait Callback: Sized {
    /// The data stored in the leaves.
    type LeafData;
    /// The data stored in the inner nodes.
    type BeefData;
    /// The callback function called when it goes down the tree.
    fn push(beef: BeefPtr<Self>);
    /// The callback function called when it goes up the tree.
    fn update(beef: BeefPtr<Self>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Left,
    Right,
}

struct Leaf<C: Callback> {
    data: C::LeafData,
    parent: Option<BeefPtr<C>>,
}

struct Beef<C: Callback> {
    data: C::BeefData,
    left: Ptr<C>,               // size = 16
    right: Ptr<C>,              // size = 16
    parent: Option<BeefPtr<C>>, // size = 8
    color: Color,               // size = 1
}

struct LeafPtr<C: Callback>(NonNull<Leaf<C>>);
impl<C: Callback> PartialEq for LeafPtr<C> {
    fn eq(&self, other: &Self) -> bool { self.0.as_ptr() == other.0.as_ptr() }
}
impl<C: Callback> Deref for LeafPtr<C> {
    type Target = Leaf<C>;

    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}
impl<C: Callback> DerefMut for LeafPtr<C> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}
impl<C: Callback> Clone for LeafPtr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for LeafPtr<C> {}

struct BeefPtr<C: Callback>(NonNull<Beef<C>>);
impl<C: Callback> BeefPtr<C> {
    /// Call `C::update` on the node.
    fn update(self) { C::update(self); }

    /// Call `C::update` on its ancestors.
    fn update_ancestors(self) {
        let mut x = self;
        while let Some(p) = x.parent {
            p.update();
            x = p;
        }
    }
}
impl<C: Callback> PartialEq for BeefPtr<C> {
    fn eq(&self, other: &Self) -> bool { self.0.as_ptr() == other.0.as_ptr() }
}
impl<C: Callback> Deref for BeefPtr<C> {
    type Target = Beef<C>;

    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}
impl<C: Callback> DerefMut for BeefPtr<C> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}
impl<C: Callback> Clone for BeefPtr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for BeefPtr<C> {}

/// A pointer to a node.
enum Ptr<C: Callback> {
    Leaf(LeafPtr<C>),
    Beef(BeefPtr<C>),
}
impl<C: Callback> PartialEq for Ptr<C> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ptr::Leaf(p), Ptr::Leaf(q)) => p == q,
            (Ptr::Beef(p), Ptr::Beef(q)) => p == q,
            _ => false,
        }
    }
}
impl<C: Callback> PartialEq<LeafPtr<C>> for Ptr<C> {
    fn eq(&self, other: &LeafPtr<C>) -> bool {
        match self {
            Ptr::Leaf(p) => p == other,
            _ => false,
        }
    }
}
impl<C: Callback> PartialEq<BeefPtr<C>> for Ptr<C> {
    fn eq(&self, other: &BeefPtr<C>) -> bool {
        match self {
            Ptr::Beef(p) => p == other,
            _ => false,
        }
    }
}
impl<C: Callback> Clone for Ptr<C> {
    fn clone(&self) -> Self { *self }
}
impl<C: Callback> Copy for Ptr<C> {}

struct Tree<C: Callback> {
    root: Option<Ptr<C>>,
    black_height: u8,
}
impl<C: Callback> Tree<C> {
    /// Create a new empty tree.
    fn new() -> Self { Self::default() }

    /// Returns `true` if the tree is empty.
    fn is_empty(&self) -> bool { self.root.is_none() }

    /// Binary searches the tree.
    fn binary_search<F>(&self, mut f: F) -> Option<LeafPtr<C>>
    where
        F: FnMut(BeefPtr<C>) -> Direction,
    {
        let mut p = self.root?;
        loop {
            p = match p {
                Ptr::Leaf(leaf) => return Some(leaf),
                Ptr::Beef(beef) => match f(beef) {
                    Direction::Left => beef.left,
                    Direction::Right => beef.right,
                },
            };
        }
    }

    /// Insert a new leaf `new` at the `position`.
    ///
    /// If `position` is `None`, insert `new` as the root.
    /// If `position` is `Some((p, dir))`, insert `new` as the child of `p` at the direction `dir`.
    fn insert(
        &mut self,
        position: Option<(LeafPtr<C>, Direction)>,
        mut new: LeafPtr<C>,
        feed_beef: impl FnOnce() -> BeefPtr<C>,
    ) {
        // TODO: assert isolatedness
        let Some((mut z, dir)) = position else {
            debug_assert_eq!(self.black_height, 0);
            debug_assert!(self.root.is_none());
            self.root = Some(Ptr::Leaf(new));
            self.black_height = 1;
            return;
        };
        // Join `z` and `new` with a new beef.
        let mut beef = feed_beef();
        match dir {
            Direction::Left => {
                beef.left = Ptr::Leaf(new);
                beef.right = Ptr::Leaf(z);
            }
            Direction::Right => {
                beef.left = Ptr::Leaf(z);
                beef.right = Ptr::Leaf(new);
            }
        }
        let p = z.parent;
        z.parent = Some(beef);
        new.parent = Some(beef);

        // Transplant `beef` to the original place of `z`.
        let Some(mut p) = p else {
            debug_assert_eq!(self.black_height, 1);
            beef.color = Color::Black;
            beef.update();
            self.root = Some(Ptr::Beef(beef));
            self.black_height = 2;
            return;
        };
        if p.left == z {
            p.left = Ptr::Beef(beef);
        } else {
            p.right = Ptr::Beef(beef);
        }
        beef.parent = Some(p);

        // Fix the tree
        self.fix_red(beef);
    }

    /// Fix the red-red violation.
    ///
    /// # Precondition
    /// - `x` is red.
    /// - `x.parent` maight be red, but this is only possible violation of rb constraint.
    /// - Fully updated except for `x` and its ancestors.
    ///
    /// # Note
    /// Why do we let `x` be unupdated? It is because, otherwise, we may have to update `x` twice.
    fn fix_red(&mut self, mut x: BeefPtr<C>) {
        loop {
            debug_assert_eq!(x.color, Color::Red);
            // Handle the case where `x` is the root.
            let Some(mut p) = x.parent else {
                x.color = Color::Black;
                self.black_height += 1;
                return;
            };
            if p.color == Color::Black {
                break;
            }
            let mut pp = p.parent.unwrap();
            // Case 1: `p` is the left child of `pp`.
            if pp.left == p {
                // Case 1.1: Finish by fixing the leaning 4-node.
                if color(pp.right) == Color::Black {
                    // Handle the case where `pp` is a splayed leaning 4-node.
                    if p.right == x {
                        x = p;
                        self.rotate_left(p);
                        p = x.parent.unwrap();
                    }
                    // Now `pp` is a non-splayed leaning 4-node.
                    p.color = Color::Black;
                    pp.color = Color::Red;
                    self.rotate_right(pp);
                    x.update();
                    pp.update();
                    x = p;
                    break;
                }
                // Case 1.2: split the 5-node.
                else {
                    let Ptr::Beef(mut s) = pp.right else { unreachable!() };
                    p.color = Color::Black;
                    s.color = Color::Black;
                    pp.color = Color::Red;
                    x.update();
                    p.update();
                    x = pp;
                }
            }
            // Case 2: `p` is the right child of `pp`.
            else {
                // Case 2.1: Finish by fixing the leaning 4-node.
                if color(pp.left) == Color::Black {
                    // Handle the case where `pp` is a splayed leaning 4-node.
                    if p.left == x {
                        x = p;
                        self.rotate_right(p);
                        p = x.parent.unwrap();
                    }
                    // Now `pp` is a non-splayed leaning 4-node.
                    p.color = Color::Black;
                    pp.color = Color::Red;
                    self.rotate_left(pp);
                    x.update();
                    pp.update();
                    x = p;
                    break;
                }
                // Case 2.2: split the 5-node.
                else {
                    let Ptr::Beef(mut s) = pp.left else { unreachable!() };
                    p.color = Color::Black;
                    s.color = Color::Black;
                    pp.color = Color::Red;
                    x.update();
                    p.update();
                    x = pp;
                }
            }
        }
        // Update the remaining part of the path [root, x].
        x.update();
        x.update_ancestors();
    }

    /// Rotate `l + c * r` to `l * c + r`.
    fn rotate_left(&mut self, mut l: BeefPtr<C>) {
        // Get the nodes.
        let Ptr::Beef(mut r) = l.right else { unreachable!() };
        let mut c = r.left;
        let p = l.parent;

        // Connect `l` and `c`.
        r.left = Ptr::Beef(l);
        l.parent = Some(r);

        // Connect `l` and `c`.
        l.right = c;
        (*match c {
            Ptr::Leaf(ref mut leaf) => &mut leaf.parent,
            Ptr::Beef(ref mut beef) => &mut beef.parent,
        }) = Some(l);

        // Connect `p` and `r`.
        r.parent = p;
        if let Some(mut p) = p {
            if p.left == l {
                p.left = Ptr::Beef(r);
            } else {
                p.right = Ptr::Beef(r);
            }
        } else {
            self.root = Some(Ptr::Beef(r));
        }
    }

    /// Rotate `l * c + r` to `l + c * r`.
    fn rotate_right(&mut self, mut r: BeefPtr<C>) {
        // Get the nodes.
        let Ptr::Beef(mut l) = r.left else { unreachable!() };
        let mut c = l.right;
        let p = r.parent;

        // Connect `r` and `c`.
        l.right = Ptr::Beef(r);
        r.parent = Some(l);

        // Connect `l` and `c`.
        r.left = c;
        (*match c {
            Ptr::Leaf(ref mut leaf) => &mut leaf.parent,
            Ptr::Beef(ref mut beef) => &mut beef.parent,
        }) = Some(r);

        // Connect `p` and `l`.
        l.parent = p;
        if let Some(mut p) = p {
            if p.left == r {
                p.left = Ptr::Beef(l);
            } else {
                p.right = Ptr::Beef(l);
            }
        } else {
            self.root = Some(Ptr::Beef(l));
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
fn color<C: Callback>(p: Ptr<C>) -> Color {
    match p {
        Ptr::Leaf(_) => Color::Black,
        Ptr::Beef(beef) => beef.color,
    }
}

#[cfg(test)]
mod tests {
    use super::test_utils::*;
    use super::*;
    use rand::rngs::StdRng;
    use rand::seq::SliceRandom;
    use rand::SeedableRng;

    #[test]
    fn test_insert() {
        static mut TIMER: usize = 0;
        struct BeefData {
            start: usize,
            end: usize,
            updated_at: usize,
        }
        enum C {}
        impl Callback for C {
            type BeefData = BeefData;
            type LeafData = usize;

            fn push(_: BeefPtr<Self>) {}

            fn update(mut beef: BeefPtr<Self>) {
                beef.data.start = match beef.left {
                    Ptr::Leaf(leaf) => leaf.data,
                    Ptr::Beef(beef) => beef.data.start,
                };
                beef.data.end = match beef.right {
                    Ptr::Leaf(leaf) => leaf.data,
                    Ptr::Beef(beef) => beef.data.end,
                };
                unsafe { TIMER += 1 };
                beef.data.updated_at = unsafe { TIMER };
            }
        }
        fn f(leaf: Ptr<C>) -> String {
            match leaf {
                Ptr::Leaf(leaf) => format!("{}", leaf.data),
                Ptr::Beef(_beef) => String::new(),
            }
        }
        fn to_vec(tree: &Tree<C>) -> Vec<usize> {
            let mut result = Vec::new();
            for_each(tree, |leaf| result.push(leaf.data));
            result
        }
        fn new_leaf(data: usize) -> LeafPtr<C> {
            LeafPtr(NonNull::new(Box::into_raw(Box::new(Leaf { data, parent: None }))).unwrap())
        }
        fn new_beef() -> BeefPtr<C> {
            let beef = BeefPtr(
                NonNull::new(Box::into_raw(Box::new(Beef {
                    data: BeefData {
                        start: usize::MAX,
                        end: usize::MAX,
                        updated_at: usize::MAX,
                    },
                    left: Ptr::Leaf(new_leaf(0)),
                    right: Ptr::Leaf(new_leaf(0)),
                    parent: None,
                    color: Color::Red,
                })))
                .unwrap(),
            );
            beef
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut tree = Tree::<C>::new();
            let mut expected = Vec::new();
            let mut nodes = (0..20).map(new_leaf).collect::<Vec<_>>();
            nodes.shuffle(&mut rng);

            for node in nodes {
                let position = tree
                    .binary_search(|beef| {
                        if (match beef.right {
                            Ptr::Leaf(leaf) => leaf.data,
                            Ptr::Beef(beef) => beef.data.start,
                        }) < node.data
                        {
                            Direction::Right
                        } else {
                            Direction::Left
                        }
                    })
                    .map(|leaf| {
                        (
                            leaf,
                            if leaf.data < node.data { Direction::Right } else { Direction::Left },
                        )
                    });
                tree.insert(position, node, new_beef);
                validate(&tree).unwrap_or_else(|err| panic!("{}\n{}", format(&tree, f), err));

                // Check the ordering of the tree.
                let lower_bound = expected
                    .binary_search(&node.data)
                    .map_or_else(|i| i, |i| i + 1);
                expected.insert(lower_bound, node.data);
                let result = to_vec(&tree);
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_optimal_size() {
        enum C {}
        impl Callback for C {
            type BeefData = ();
            type LeafData = ();

            fn push(_: BeefPtr<Self>) {}

            fn update(_: BeefPtr<Self>) {}
        }

        assert_eq!(std::mem::size_of::<Leaf<C>>(), 8);
        assert_eq!(std::mem::size_of::<Beef<C>>(), 48);
        assert_eq!(std::mem::size_of::<LeafPtr<C>>(), 8);
        assert_eq!(std::mem::size_of::<BeefPtr<C>>(), 8);
        assert_eq!(std::mem::size_of::<Ptr<C>>(), 16);
        assert_eq!(std::mem::size_of::<Option<LeafPtr<C>>>(), 8);
        assert_eq!(std::mem::size_of::<Option<BeefPtr<C>>>(), 8);
        assert_eq!(std::mem::size_of::<Option<Ptr<C>>>(), 16);
        assert_eq!(std::mem::size_of::<Tree<C>>(), 24);
    }
}

#[cfg(test)]
mod test_utils {
    use super::*;
    use core::fmt;

    impl<C: Callback> LeafPtr<C> {
        pub fn debug_ptr(self) -> String {
            format!("0x{:02x}", self.0.as_ptr() as usize % 0x1000 / 0x10)
        }
    }
    impl<C: Callback> BeefPtr<C> {
        pub fn debug_ptr(self) -> String {
            format!("0x{:02x}", self.0.as_ptr() as usize % 0x1000 / 0x10)
        }
    }
    impl<C: Callback> Ptr<C> {
        pub fn debug_ptr(self) -> String {
            match self {
                Ptr::Leaf(leaf) => leaf.debug_ptr(),
                Ptr::Beef(beef) => beef.debug_ptr(),
            }
        }
    }

    fn write<C, W, F>(w: &mut W, tree: &Tree<C>, format: F) -> fmt::Result
    where
        C: Callback,
        W: fmt::Write,
        F: Copy + FnMut(Ptr<C>) -> String,
    {
        fn write<C, W, F>(w: &mut W, ptr: Ptr<C>, mut format: F) -> fmt::Result
        where
            C: Callback,
            W: fmt::Write,
            F: Copy + FnMut(Ptr<C>) -> String,
        {
            match ptr {
                Ptr::Leaf(leaf) => write!(w, "{}", format(Ptr::Leaf(leaf)))?,
                Ptr::Beef(beef) => {
                    if beef.color == Color::Black {
                        write!(w, "[")?;
                    }
                    write(w, beef.left, format)?;
                    write!(
                        w,
                        " {}{} ",
                        match beef.color {
                            Color::Red => "*",
                            Color::Black => "+",
                        },
                        match format(Ptr::Beef(beef)).as_str() {
                            "" => String::new(),
                            s => format!("({})", s),
                        }
                    )?;
                    write(w, beef.right, format)?;
                    if beef.color == Color::Black {
                        write!(w, "]")?;
                    }
                }
            }
            Ok(())
        }
        if let Some(root) = tree.root {
            write!(w, "[")?;
            write(w, root, format)?;
            write!(w, "]")?;
        }
        Ok(())
    }

    pub fn format<C, F>(tree: &Tree<C>, format: F) -> String
    where
        C: Callback,
        F: Copy + FnMut(Ptr<C>) -> String,
    {
        let mut result = String::new();
        write(&mut result, tree, format).unwrap();
        result
    }

    pub fn for_each<C: Callback, F: FnMut(LeafPtr<C>)>(tree: &Tree<C>, mut f: F) {
        fn for_each<C: Callback, F: FnMut(LeafPtr<C>)>(ptr: Ptr<C>, f: &mut F) {
            match ptr {
                Ptr::Leaf(leaf) => f(leaf),
                Ptr::Beef(beef) => {
                    for_each(beef.left, f);
                    for_each(beef.right, f);
                }
            }
        }
        if let Some(root) = tree.root {
            for_each(root, &mut f);
        }
    }

    pub fn validate<C: Callback>(tree: &Tree<C>) -> Result<(), String> {
        fn validate<C: Callback>(node: Ptr<C>) -> Result<u8, String> {
            match node {
                Ptr::Leaf(_) => Ok(1),
                Ptr::Beef(beef) => {
                    // Check the black-height.
                    let left_black_height = validate(beef.left)?;
                    let right_black_height = validate(beef.right)?;
                    (left_black_height == right_black_height)
                        .then(|| left_black_height + (beef.color == Color::Black) as u8)
                        .ok_or_else(|| {
                            format!(
                                "black height mismatch at {}: {} vs {}",
                                beef.debug_ptr(),
                                left_black_height,
                                right_black_height
                            )
                        })?;

                    // Check the red-red violation with the left child.
                    (beef.color == Color::Black || color(beef.left) == Color::Black)
                        .then(|| ())
                        .ok_or_else(|| {
                            format!(
                                "red-red violation at {} and its left child {}",
                                beef.debug_ptr(),
                                match beef.left {
                                    Ptr::Leaf(leaf) => leaf.debug_ptr(),
                                    Ptr::Beef(beef) => beef.debug_ptr(),
                                }
                            )
                        })?;

                    // Check the red-red violation with the right child.
                    (beef.color == Color::Black || color(beef.right) == Color::Black)
                        .then(|| ())
                        .ok_or_else(|| {
                            format!(
                                "red-red violation at {} and its right child {}",
                                beef.debug_ptr(),
                                match beef.right {
                                    Ptr::Leaf(leaf) => leaf.debug_ptr(),
                                    Ptr::Beef(beef) => beef.debug_ptr(),
                                }
                            )
                        })?;
                    Ok(left_black_height + (beef.color == Color::Black) as u8)
                }
            }
        }
        let black_height = tree.root.map_or(Ok(0), |root| validate(root))?;
        (black_height == tree.black_height)
            .then(|| ())
            .ok_or_else(|| {
                format!(
                    "black height mismatch.\n calculated: {}\n     cached: {}",
                    black_height, tree.black_height
                )
            })?;
        Ok(())
    }
}
