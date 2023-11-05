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

fn color<T: Node>(x: Option<Ptr<T>>) -> Color {
    match x {
        None => Color::Black,
        Some(mut x) => *x.color(),
    }
}

fn rotate_left<T: Node>(mut l: Ptr<T>) {
    let p = *l.parent();
    let mut r = l.right().unwrap();
    let c = *r.left();

    // Connect `p` and `r`.
    *r.parent() = p;
    if let Some(mut p) = p {
        *(if *p.left() == Some(l) { p.left() } else { p.right() }) = Some(r);
    }

    // Connect `r` and `l`.
    *l.parent() = Some(r);
    *r.left() = Some(l);

    // Connect `l` and `c`.
    if let Some(mut c) = c {
        *c.parent() = Some(l);
    }
    *l.right() = c;
}

fn rotate_right<T: Node>(mut r: Ptr<T>) {
    let p = *r.parent();
    let mut l = r.left().unwrap();
    let c = *l.right();

    // Connect `p` and `l`.
    *l.parent() = p;
    if let Some(mut p) = p {
        *(if *p.left() == Some(r) { p.left() } else { p.right() }) = Some(l);
    }

    // Connect `l` and `r`.
    *r.parent() = Some(l);
    *l.right() = Some(r);

    // Connect `r` and `c`.
    if let Some(mut c) = c {
        *c.parent() = Some(r);
    }
    *r.left() = c;
}

pub fn fix_red<T: Node>(mut x: Ptr<T>) -> (Ptr<T>, bool) {
    while color(*x.parent()) == Color::Red {
        let mut p = x.parent().unwrap();

        let Some(mut pp) = p.parent() else {
            *p.color() = Color::Black;
            return (p, true);
        };

        // Case 1: `p` is the left child.
        if *pp.left() == Some(p) {
            // Case 1.1: `pp` is a 5-node.
            if color(*pp.right()) == Color::Red {
                *p.color() = Color::Black;
                *pp.color() = Color::Red;
                *pp.right().unwrap().color() = Color::Black;
                x = pp;
            }
            // Case 1.2: `pp` is a splayed 4-node.
            else if *p.right() == Some(x) {
                rotate_left(p);
                rotate_right(pp);
                *x.color() = Color::Black;
                *pp.color() = Color::Red;
                break;
            }
            // Case 1.3: `pp` is a straight 4-node.
            else {
                rotate_right(pp);
                *p.color() = Color::Black;
                *pp.color() = Color::Red;
                break;
            }
        }
        // Case 2: `p` is the right child.
        else {
            // Case 2.1: `pp` is a 5-node.
            if color(*pp.left()) == Color::Red {
                *p.color() = Color::Black;
                *pp.color() = Color::Red;
                *pp.left().unwrap().color() = Color::Black;
                x = pp;
            }
            // Case 2.2: `pp` is a splayed 4-node.
            else if *p.left() == Some(x) {
                rotate_right(p);
                rotate_left(pp);
                *x.color() = Color::Black;
                *pp.color() = Color::Red;
                break;
            }
            // Case 2.3: `pp` is a straight 4-node.
            else {
                rotate_left(pp);
                *p.color() = Color::Black;
                *pp.color() = Color::Red;
                break;
            }
        }
    }
    while let Some(mut p) = x.parent() {
        p.update();
        x = p;
    }
    (x, false)
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
    use super::fix_red;
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

    #[derive(Default)]
    struct Tree {
        root: Option<Ptr<Node>>,
        black_height: u8,
    }
    impl fmt::Display for Tree {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fn write(
                s: &mut fmt::Formatter<'_>,
                x: Option<Ptr<Node>>,
                p: Option<Ptr<Node>>,
                vios: &Violations,
            ) -> fmt::Result {
                if vios.black_vios.contains(&(x, p)) {
                    write!(s, "\x1b[40m\x1b[37m«\x1b[0m")?;
                }
                if let Some(x) = x {
                    if x.color == Color::Black {
                        write!(s, "[")?
                    }
                    write(s, x.left, Some(x), vios)?;
                    if vios.red_vios.contains(&x) {
                        write!(s, "\x1b[41m\x1b[37m{:?}\x1b[0m", x)?;
                    } else {
                        match x.color {
                            Color::Black => write!(s, "\x1b[30m{:?}\x1b[0m", x)?,
                            Color::Red => write!(s, "\x1b[31m{:?}\x1b[0m", x)?,
                        }
                    }
                    write(s, x.right, Some(x), vios)?;
                    if x.color == Color::Black {
                        write!(s, "]")?;
                    }
                }
                if vios.black_vios.contains(&(x, p)) {
                    write!(s, "\x1b[40m\x1b[37m»\x1b[0m")?;
                }
                Ok(())
            }
            let vios = Violations::collect(self);
            write!(f, "Tree({}, \"", self.black_height)?;
            write(f, self.root, None, &vios)?;
            write!(f, "\")")?;
            Ok(())
        }
    }
    impl Tree {
        #[allow(clippy::too_many_lines)]
        fn random(
            rng: &mut StdRng,
            black_height: u8,
            red_vio: bool,
            black_vio: bool,
        ) -> (Self, Violations) {
            #[allow(clippy::too_many_lines)]
            fn random_tree(
                rng: &mut StdRng,
                mut black_height: u8,
                red_vio: bool,
                black_vio: bool,
                parent: Option<Ptr<Node>>,
            ) -> (Option<Ptr<Node>>, Violations) {
                // Select the violation position here
                let parent_color = parent.map_or(Color::Black, |p| p.color);
                let here_red_vio;
                let here_black_vio;
                let color;
                match (red_vio, black_vio) {
                    (false, false) => {
                        here_red_vio = false;
                        here_black_vio = false;
                        color = match parent_color {
                            Color::Red => Color::Black,
                            Color::Black => {
                                if rng.gen() {
                                    Color::Red
                                } else {
                                    Color::Black
                                }
                            }
                        }
                    }
                    (true, false) => {
                        here_red_vio = parent_color == Color::Red
                            && red_vio
                            && rng.gen_ratio(1, 2u32.pow(u32::from(black_height)));
                        here_black_vio = false;
                        color = if here_red_vio {
                            Color::Red
                        } else {
                            match parent_color {
                                Color::Red => Color::Black,
                                Color::Black => {
                                    if (red_vio && black_height == 0) || rng.gen() {
                                        Color::Red
                                    } else {
                                        Color::Black
                                    }
                                }
                            }
                        };
                    }
                    (false, true) => {
                        here_red_vio = false;
                        color = match parent_color {
                            Color::Red => Color::Black,
                            Color::Black => {
                                if rng.gen() {
                                    Color::Red
                                } else {
                                    Color::Black
                                }
                            }
                        };
                        here_black_vio = rng.gen_ratio(
                            1,
                            2u32.pow(u32::from(black_height) - u32::from(color == Color::Black)),
                        );
                    }
                    (true, true) => panic!(),
                }

                if here_black_vio {
                    black_height -= 1;
                }

                // Select the violation position at children
                let mut left_red_vio = false;
                let mut right_red_vio = false;
                if red_vio && !here_red_vio {
                    *(if rng.gen() { &mut left_red_vio } else { &mut right_red_vio }) = true;
                }
                let mut left_black_vio = false;
                let mut right_black_vio = false;
                if black_vio && !here_black_vio {
                    *(if rng.gen() { &mut left_black_vio } else { &mut right_black_vio }) = true;
                }

                // Init vios
                let here = if black_height == 0 && color == Color::Black {
                    None
                } else {
                    Some(Ptr(NonNull::from(Box::leak(Box::new(Node {
                        color,
                        parent: None,
                        left: None,
                        right: None,
                    })))))
                };
                let mut vios = Violations::default();
                if here_red_vio {
                    vios.red_vios.push(here.unwrap());
                }
                if here_black_vio {
                    vios.black_vios.push((here, parent));
                }

                // Recurse
                if let Some(mut here) = here {
                    let children_black_height = black_height - u8::from(color == Color::Black);
                    let (mut left, left_vio) = random_tree(
                        rng,
                        children_black_height,
                        left_red_vio,
                        left_black_vio,
                        Some(here),
                    );
                    vios.append(left_vio);
                    let (mut right, right_vio) = random_tree(
                        rng,
                        children_black_height,
                        right_red_vio,
                        right_black_vio,
                        Some(here),
                    );
                    vios.append(right_vio);

                    if let Some(left) = left.as_mut() {
                        left.parent = Some(here);
                    }
                    if let Some(right) = right.as_mut() {
                        right.parent = Some(here);
                    }
                    here.left = left;
                    here.right = right;
                }
                (here, vios)
            }
            let (root, vios) = random_tree(rng, black_height, red_vio, black_vio, None);
            (Tree { root, black_height }, vios)
        }

        fn validate(&self) {
            fn validate(x: Option<Ptr<Node>>) -> Result<u8, String> {
                let Some(x) = x else {
                    return Ok(0);
                };
                let left_height = validate(x.left)?;
                let right_height = validate(x.right)?;
                (left_height == right_height
                    || left_height == right_height + 1
                    || left_height + 1 == right_height)
                    .then_some(())
                    .ok_or_else(|| {
                        format!("The difference of black height is greater than 1: {:?}", x)
                    })?;

                // Parent pointer incinsistency
                if let Some(left) = x.left {
                    (left.parent == Some(x)).then_some(()).ok_or_else(|| {
                        format!(
                            "parent pointer inconsistency between {:?} and its left child {:?}. \
                             The parent of the left child is {:?}",
                            x, left, left.parent
                        )
                    })?;
                }
                if let Some(right) = x.right {
                    (right.parent == Some(x)).then_some(()).ok_or_else(|| {
                        format!(
                            "parent pointer inconsistency between {:?} and its right child {:?}. \
                             The parent of the right child is {:?}",
                            x, right, right.parent
                        )
                    })?;
                }
                Ok(left_height.max(right_height) + u8::from(x.color == Color::Black))
            }
            || -> Result<(), String> {
                let h = validate(self.root)?;
                (self.black_height == h || self.black_height == h + 1)
                    .then_some(())
                    .ok_or_else(|| format!("black height of {} is not {}", self, h))?;
                if let Some(x) = self.root {
                    // Parent is None
                    (x.parent.is_none())
                        .then_some(())
                        .ok_or_else(|| format!("parent of {:?} is not None", x))?;
                }
                Ok(())
            }()
            .unwrap_or_else(|e| panic!("Validation error: {}\nTree: {}", e, self))
        }

        fn collect(&self) -> Vec<Ptr<Node>> {
            fn extend(x: Option<Ptr<Node>>, out: &mut Vec<Ptr<Node>>) {
                if let Some(x) = x {
                    extend(x.left, out);
                    out.push(x);
                    extend(x.right, out);
                }
            }
            let mut out = Vec::new();
            extend(self.root, &mut out);
            out
        }
    }

    #[derive(Debug, PartialEq, Default)]
    #[allow(clippy::type_complexity)]
    struct Violations {
        red_vios: Vec<Ptr<Node>>,
        black_vios: Vec<(Option<Ptr<Node>>, Option<Ptr<Node>>)>, // child, parent
    }
    impl Violations {
        fn append(&mut self, other: Self) {
            self.red_vios.extend(other.red_vios);
            self.black_vios.extend(other.black_vios);
        }

        fn collect(tree: &Tree) -> Self {
            fn extend(x: Option<Ptr<Node>>, p: Option<Ptr<Node>>, vios: &mut Violations) -> u8 {
                let Some(x) = x else { return 0 };
                let left_height = extend(x.left, Some(x), vios);
                let right_height = extend(x.right, Some(x), vios);
                match left_height.cmp(&right_height) {
                    Ordering::Less => vios.black_vios.push((x.left, Some(x))),
                    Ordering::Greater => vios.black_vios.push((x.right, Some(x))),
                    Ordering::Equal => {}
                }
                if let Some(p) = p {
                    if p.color == Color::Red && x.color == Color::Red {
                        vios.red_vios.push(x);
                    }
                }
                left_height.max(right_height) + u8::from(x.color == Color::Black)
            }
            let mut vios = Self::default();
            let h = extend(tree.root, None, &mut vios);
            if tree.black_height != h {
                vios.black_vios.push((tree.root, None));
            }
            vios
        }
    }

    #[test]
    fn test_random_tree_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(0..=4);
            let (tree, expected_violations) = Tree::random(&mut rng, h, false, false);
            assert_eq!(tree.black_height, h, "{}", tree);
            assert_eq!(expected_violations.red_vios.len(), 0, "{}", tree);
            assert_eq!(expected_violations.black_vios.len(), 0, "{}", tree);
            tree.validate();

            let actual_violations = Violations::collect(&tree);
            assert_eq!(expected_violations, actual_violations, "{}", tree);
        }
    }

    #[test]
    fn test_random_red_vio_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(0..=4);
            let (tree, expected_violations) = Tree::random(&mut rng, h, true, false);
            assert_eq!(tree.black_height, h, "{}", tree);
            assert_eq!(expected_violations.red_vios.len(), 1, "{}", tree);
            assert_eq!(expected_violations.black_vios.len(), 0, "{}", tree);
            tree.validate();

            let actual_violations = Violations::collect(&tree);
            assert_eq!(expected_violations, actual_violations, "{}", tree);
        }
    }

    #[test]
    fn test_random_black_vio_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(1..=4);
            let (tree, expected_violations) = Tree::random(&mut rng, h, false, true);
            assert_eq!(tree.black_height, h, "{}", tree);
            assert_eq!(expected_violations.red_vios.len(), 0, "{}", tree);
            assert_eq!(expected_violations.black_vios.len(), 1, "{}", tree);
            tree.validate();

            let actual_violations = Violations::collect(&tree);
            assert_eq!(expected_violations, actual_violations, "{}", tree);
        }
    }

    #[test]
    fn test_fix_red() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(1..=4);
            let (mut tree, violations) = Tree::random(&mut rng, h, true, false);
            let red_vio = violations.red_vios[0];
            let before = tree.collect();

            let (root, changed) = fix_red(red_vio);
            tree.root = Some(root);
            if changed {
                tree.black_height += 1;
            }
            let after = tree.collect();
            tree.validate();

            // Make sure the violation has fixed.
            assert_eq!(Violations::collect(&tree), Violations::default());
            // Make sure the sequence of nodes has not changed.
            assert_eq!(before, after);
        }
    }
}
