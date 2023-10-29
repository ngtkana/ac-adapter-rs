#![warn(missing_docs)]
//! Containers for storing data in a red-black tree.

/// A segtree based on a red-black tree.
mod seg;
/// A sorted vector based on a red-black tree.
mod seg_map;
/// The core implementation of a red-black tree.
mod tree;

/// A list based on a red-black tree.
pub use seg::Seg;
/// A sorted vector based on a red-black tree.
pub use seg_map::SegMap;

/// A trait for algebraic operations.
pub trait Op {
    /// The type of the value stored in the leaf nodes.
    type Value;
    /// The type of the lazy action stored in the internal nodes.
    type Lazy: PartialEq;

    /// Multiply two `Value`s.
    fn mul(_: &Self::Value, _: &Self::Value) -> Self::Value;

    /// Apply a `Lazy` action to a `Value`.
    fn apply(_: &mut Self::Value, _: &Self::Lazy);

    /// Compose two `Lazy` actions.
    fn compose(_: &mut Self::Lazy, _: &Self::Lazy);

    /// The identity of `Lazy` actions.
    fn identity() -> Self::Lazy;

    /// Check if a `Lazy` action is the identity.
    fn is_identity(lazy: &Self::Lazy) -> bool { *lazy == Self::identity() }

    /// Set a `Lazy` action to the identity.
    fn swap_with_identity(lazy: &mut Self::Lazy) -> Self::Lazy {
        let mut tmp = Self::identity();
        std::mem::swap(lazy, &mut tmp);
        tmp
    }
}

#[cfg(test)]
pub mod test_util {
    use super::tree::*;
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use std::fmt;

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Concat {}
    impl Op for Concat {
        type Lazy = ();
        type Value = Vec<u64>;

        fn mul(left: &Self::Value, right: &Self::Value) -> Self::Value {
            left.iter().chain(right.iter()).copied().collect()
        }

        fn compose(_: &mut Self::Lazy, _: &Self::Lazy) {}

        fn identity() -> Self::Lazy {}

        fn apply(_: &mut Self::Value, _: &Self::Lazy) {}
    }

    impl<C: Callback> fmt::Debug for Tree<C> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            pub fn write<C: Callback>(f: &mut fmt::Formatter<'_>, p: Ptr<C>) -> fmt::Result {
                if p.is_leaf() {
                    write!(f, "{:?}", p)?;
                } else {
                    write!(f, "(")?;
                    write(f, p.left.unwrap())?;
                    match p.color {
                        Color::Red => write!(f, " \x1b[31m{:?}\x1b[0m ", p)?,
                        Color::Black => write!(f, " {:?} ", p)?,
                    }
                    write(f, p.right.unwrap())?;
                    write!(f, ")")?;
                }
                Ok(())
            }
            write!(f, "[")?;
            if let Some(root) = self.root {
                write(f, root)?;
            }
            write!(f, "]")?;
            Ok(())
        }
    }

    pub fn visit_nodes<C: Callback>(tree: &Tree<C>, mut f: impl FnMut(Ptr<C>)) {
        fn visit_nodes<C: Callback>(p: Ptr<C>, f: &mut impl FnMut(Ptr<C>)) {
            if let Some(left) = p.left {
                visit_nodes(left, f);
            }
            f(p);
            if let Some(right) = p.right {
                visit_nodes(right, f);
            }
        }
        if let Some(root) = tree.root {
            visit_nodes(root, &mut f);
        }
    }

    pub fn validate_base<C: Callback>(
        tree: &Tree<C>,
        mut additional: impl FnMut(Ptr<C>) -> Result<(), String>,
    ) {
        fn validate_base<C: Callback>(
            p: Ptr<C>,
            additional: &mut impl FnMut(Ptr<C>) -> Result<(), String>,
        ) -> Result<u8, String> {
            if p.is_leaf() {
                (p.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| format!("Red leaf node: {:?}", p))?;
                Ok(1)
            } else {
                let left = p.left.unwrap();
                let right = p.right.unwrap();
                let left_height = validate_base(left, additional)?;
                let right_height = validate_base(right, additional)?;
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
                additional(p)?;
                Ok(left_height + u8::from(p.color == Color::Black))
            }
        }
        || -> Result<(), String> {
            if let Some(root) = tree.root {
                validate_base(root, &mut additional)?;
                (root.color == Color::Black)
                    .then_some(())
                    .ok_or_else(|| format!("The root is not black: {:?}", &tree))?;
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
                        "The black height is not zero, but the tree is empty: {:?}",
                        &tree,
                    )
                })?;
            }
            Ok(())
        }()
        .unwrap_or_else(|err| panic!("validation error: {}\nin a tree {:?}.", err, &tree))
    }

    pub fn validate<C: Callback>(tree: &Tree<C>) { validate_base(tree, |_| Ok(())); }

    pub fn validate_with_data<C: Callback>(tree: &Tree<C>)
    where
        C::Data: Clone + PartialEq + fmt::Debug,
    {
        validate_base(tree, |p| {
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
            })
        })
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
