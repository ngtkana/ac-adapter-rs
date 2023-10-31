#![allow(dead_code, unused_variables)]

use core::fmt;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ptr::NonNull;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Color {
    Red,
    Black,
}

pub trait Node: Sized {
    fn update(&mut self);

    fn push(&mut self);

    fn color(&mut self) -> &mut Color;

    fn parent(&mut self) -> &mut Option<Ptr<Self>>;

    fn left(&mut self) -> &mut Option<Ptr<Self>>;

    fn right(&mut self) -> &mut Option<Ptr<Self>>;
}

pub struct Ptr<T>(NonNull<T>);
impl<T> Clone for Ptr<T> {
    fn clone(&self) -> Self { *self }
}
impl<T> Copy for Ptr<T> {}
impl<T> Deref for Ptr<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}
impl<T> DerefMut for Ptr<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}
impl<T> fmt::Debug for Ptr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:02x}", self.0.as_ptr() as usize % 0x1000 / 0x10)
    }
}
impl<T> PartialEq for Ptr<T> {
    fn eq(&self, other: &Self) -> bool { std::ptr::eq(self.0.as_ptr(), other.0.as_ptr()) }
}

#[cfg(test)]
mod tests {
    use super::Color;
    use super::Ptr;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::cmp::Ordering;
    use std::fmt;
    use std::ptr::NonNull;

    struct Node {
        color: Color,
        parent: Option<Ptr<Self>>,
        left: Option<Ptr<Self>>,
        right: Option<Ptr<Self>>,
    }

    impl super::Node for Node {
        fn update(&mut self) {}

        fn push(&mut self) {}

        fn color(&mut self) -> &mut Color { &mut self.color }

        fn parent(&mut self) -> &mut Option<Ptr<Self>> { &mut self.parent }

        fn left(&mut self) -> &mut Option<Ptr<Self>> { &mut self.left }

        fn right(&mut self) -> &mut Option<Ptr<Self>> { &mut self.right }
    }

    fn new_ptr(color: Color) -> Ptr<Node> {
        Ptr(NonNull::from(Box::leak(Box::new(Node {
            color,
            parent: None,
            left: None,
            right: None,
        }))))
    }

    fn random_tree(
        rng: &mut StdRng,
        black_height: u8,
        red_vio: bool,
    ) -> (Option<Ptr<Node>>, Violations) {
        fn random_tree(
            rng: &mut StdRng,
            black_height: u8,
            parent_color: Color,
            is_root: bool,
            subtree_red_vios: bool,
        ) -> (Option<Ptr<Node>>, Violations) {
            // Whether the current node is violation.
            let root_red_vios = parent_color == Color::Red
                && !is_root
                && subtree_red_vios
                && rng.gen_ratio(1, 2u32.pow(black_height as u32));

            // Select `color`.
            let color = if root_red_vios {
                Color::Red
            } else {
                match parent_color {
                    Color::Red => Color::Black,
                    Color::Black => {
                        if (subtree_red_vios && black_height == 0) || rng.gen() {
                            Color::Red
                        } else {
                            Color::Black
                        }
                    }
                }
            };

            // The concepual "nil" node is black, and has a black height of 0.
            if black_height == 0 && color == Color::Black {
                return (None, Violations::default());
            }

            // Determine where the red violation occurs
            let root_red_vios = (parent_color, color) == (Color::Red, Color::Red);
            let (left_red_vios, right_red_vios) = if !subtree_red_vios || root_red_vios {
                (false, false)
            } else if rng.gen() {
                (true, false)
            } else {
                (false, true)
            };

            // Join the two trees
            let mut root = new_ptr(color);
            let children_black_height = black_height - u8::from(color == Color::Black);
            let (mut left, left_vio) =
                random_tree(rng, children_black_height, color, false, left_red_vios);
            let (mut right, right_vio) =
                random_tree(rng, children_black_height, color, false, right_red_vios);
            if let Some(left) = left.as_mut() {
                left.parent = Some(root);
            }
            if let Some(right) = right.as_mut() {
                right.parent = Some(root);
            }
            root.left = left;
            root.right = right;

            // Merge violations
            let mut vios = left_vio.concat(right_vio);
            if root_red_vios {
                vios.red_vios.push(root);
            }
            (Some(root), vios)
        }

        random_tree(rng, black_height, Color::Red, true, red_vio)
    }

    struct Paren(Option<Ptr<Node>>);
    impl fmt::Display for Paren {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fn write(
                s: &mut fmt::Formatter<'_>,
                p: Option<Ptr<Node>>,
                x: Option<Ptr<Node>>,
            ) -> fmt::Result {
                if let Some(x) = x {
                    if x.color == Color::Black {
                        write!(s, "[")?
                    }
                    write(s, Some(x), x.left)?;
                    match x.color {
                        Color::Red => {
                            if p.map_or(true, |p| p.color == Color::Red) {
                                write!(s, "\x1b[41m\x1b[37m{:?}\x1b[0m", x)?;
                            } else {
                                write!(s, "\x1b[31m{:?}\x1b[0m", x)?;
                            }
                        }
                        Color::Black => write!(s, "{:?}", x)?,
                    }
                    write(s, Some(x), x.right)?;
                    if x.color == Color::Black {
                        write!(s, "]")?;
                    }
                }
                Ok(())
            }
            write(f, None, self.0)
        }
    }

    #[derive(Debug, PartialEq, Default)]
    struct Violations {
        red_vios: Vec<Ptr<Node>>,
        black_vios: Vec<(Option<Ptr<Node>>, Option<Ptr<Node>>)>,
        root_vio: bool,
    }
    impl Violations {
        fn concat(mut self, other: Self) -> Self {
            self.red_vios.extend(other.red_vios);
            self
        }
    }

    fn validate(x: Option<Ptr<Node>>) -> (u8, Violations) {
        fn validate(x: Option<Ptr<Node>>) -> Result<(u8, Violations), String> {
            let Some(x) = x else {
                return Ok((0, Violations::default()));
            };
            let mut red_vios = Vec::new();
            let mut black_vios = Vec::new();
            let (
                left_height,
                Violations {
                    red_vios: left_red_vios,
                    black_vios: left_black_vios,
                    root_vio: _,
                },
            ) = validate(x.left)?;
            let (
                right_height,
                Violations {
                    red_vios: right_red_vios,
                    black_vios: right_black_vios,
                    root_vio: _,
                },
            ) = validate(x.right)?;

            // Collect child violations
            red_vios.extend(left_red_vios);
            red_vios.extend(right_red_vios);
            black_vios.extend(left_black_vios);
            black_vios.extend(right_black_vios);

            // Black vios
            match left_height.cmp(&right_height) {
                Ordering::Less => black_vios.push((x.left, Some(x))),
                Ordering::Greater => black_vios.push((x.right, Some(x))),
                Ordering::Equal => {}
            }

            // Red vios
            if x.color == Color::Red {
                if let Some(left) = x.left {
                    if left.color == Color::Red {
                        red_vios.push(left);
                    }
                }
                if let Some(right) = x.right {
                    if right.color == Color::Red {
                        red_vios.push(right);
                    }
                }
            }

            // Parent pointer incinsistency
            if let Some(left) = x.left {
                (left.parent == Some(x)).then(|| ()).ok_or_else(|| {
                    format!(
                        "parent pointer inconsistency between {:?} and its left child {:?}. The \
                         parent of the left child is {:?}",
                        x, left, left.parent
                    )
                })?;
            }
            if let Some(right) = x.right {
                (right.parent == Some(x)).then(|| ()).ok_or_else(|| {
                    format!(
                        "parent pointer inconsistency between {:?} and its right child {:?}. The \
                         parent of the right child is {:?}",
                        x, right, right.parent
                    )
                })?;
            }
            Ok((
                left_height + u8::from(x.color == Color::Black),
                Violations {
                    red_vios,
                    black_vios,
                    root_vio: false,
                },
            ))
        }
        || -> Result<(u8, Violations), String> {
            let (h, mut violations) = validate(x)?;
            if let Some(x) = x {
                // Root is black
                if x.color != Color::Black {
                    violations.root_vio = true;
                }
                // Parent is None
                (x.parent.is_none())
                    .then_some(())
                    .ok_or_else(|| format!("parent of {:?} is not None", x))?;
            }
            Ok((h, violations))
        }()
        .unwrap_or_else(|e| panic!("Validation error: {}\nTree: {}", e, Paren(x)))
    }

    #[test]
    fn test_random_tree_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(0..=4);
            let (root, expected_violations) = random_tree(&mut rng, h, false);
            let (black_height, actual_violations) = validate(root);
            assert_eq!(black_height, h, "{}", Paren(root));
            assert_eq!(expected_violations, actual_violations, "{}", Paren(root));
            assert_eq!(expected_violations.red_vios.len(), 0, "{}", Paren(root));
        }
    }

    #[test]
    fn test_random_red_vio_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(1..=4);
            let (root, expected_violations) = random_tree(&mut rng, h, true);
            let (black_height, actual_violations) = validate(root);
            assert_eq!(black_height, h, "{}", Paren(root));
            assert_eq!(expected_violations, actual_violations, "{}", Paren(root));
            assert_eq!(expected_violations.red_vios.len(), 1, "{}", Paren(root));
        }
    }

    #[test]
    fn test_random_black_vio_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(1..=4);
            let (root, expected_violations) = random_tree(&mut rng, h, false);
            let (black_height, actual_violations) = validate(root);
            assert_eq!(black_height, h, "{}", Paren(root));
            assert_eq!(expected_violations, actual_violations, "{}", Paren(root));
            assert_eq!(expected_violations.red_vios.len(), 0, "{}", Paren(root));
        }
    }
}
