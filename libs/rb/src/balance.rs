use core::fmt;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ptr::NonNull;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Color {
    Red,
    Black,
}

pub trait Balance: Sized {
    fn update(&mut self);

    fn push(&mut self);

    fn color(&mut self) -> &mut Color;

    fn parent(&mut self) -> &mut Option<Ptr<Self>>;

    fn left(&mut self) -> &mut Option<Ptr<Self>>;

    fn right(&mut self) -> &mut Option<Ptr<Self>>;
}

pub struct Tree<T: Balance> {
    pub root: Option<Ptr<T>>,
    pub black_height: u8,
}
impl<T: Balance> Tree<T> {
    pub fn new() -> Self {
        Self {
            root: None,
            black_height: 0,
        }
    }

    pub fn min(&self) -> Option<Ptr<T>> {
        let mut x = self.root?;
        while let Some(l) = *x.left() {
            x = l;
        }
        Some(x)
    }

    pub fn max(&self) -> Option<Ptr<T>> {
        let mut x = self.root?;
        while let Some(r) = *x.right() {
            x = r;
        }
        Some(x)
    }

    // Updates: the proper ancestors of `x` (i.e. `x` should be already updated)
    pub fn fix_red(&mut self, mut x: Ptr<T>) {
        while color(*x.parent()) == Color::Red {
            let mut p = x.parent().unwrap();

            let Some(mut pp) = p.parent() else {
                p.update();
                *p.color() = Color::Black;
                self.black_height += 1;
                return;
            };

            // Case 1: `p` is the left child.
            if *pp.left() == Some(p) {
                // Case 1.1: `pp` is a 5-node.
                if color(*pp.right()) == Color::Red {
                    *p.color() = Color::Black;
                    *pp.color() = Color::Red;
                    *pp.right().unwrap().color() = Color::Black;
                    p.update();
                    pp.update();
                    x = pp;
                }
                // Case 1.2: `pp` is a splayed 4-node.
                else if *p.right() == Some(x) {
                    rotate_left(p);
                    rotate_right(pp);
                    *x.color() = Color::Black;
                    *pp.color() = Color::Red;
                    p.update();
                    pp.update();
                    x.update();
                    break;
                }
                // Case 1.3: `pp` is a straight 4-node.
                else {
                    rotate_right(pp);
                    *p.color() = Color::Black;
                    *pp.color() = Color::Red;
                    pp.update();
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
                    p.update();
                    pp.update();
                    x = pp;
                }
                // Case 2.2: `pp` is a splayed 4-node.
                else if *p.left() == Some(x) {
                    rotate_right(p);
                    rotate_left(pp);
                    *x.color() = Color::Black;
                    *pp.color() = Color::Red;
                    p.update();
                    pp.update();
                    x.update();
                    break;
                }
                // Case 2.3: `pp` is a straight 4-node.
                else {
                    rotate_left(pp);
                    *p.color() = Color::Black;
                    *pp.color() = Color::Red;
                    pp.update();
                    break;
                }
            }
        }
        self.root = Some(x.update_ancestors());
    }

    // Updates: the proper ancestors of `x` (i.e. `x` should be already updated)
    pub fn fix_black(&mut self, black_violation: BlackViolation<T>) {
        let BlackViolation { p, mut x } = black_violation;
        loop {
            if color(x) == Color::Red {
                *x.unwrap().color() = Color::Black;
                break;
            }
            let p = x.map_or(p, |mut x| *x.parent());
            let Some(mut p) = p else {
                self.black_height -= 1;
                return;
            };
            // Case 1: `x` is the left child.
            if *p.left() == x {
                let mut s = p.right().unwrap();
                if *s.color() == Color::Red {
                    rotate_left(p);
                    *p.color() = Color::Red;
                    *s.color() = Color::Black;
                    s = p.right().unwrap();
                }
                match (color(*s.left()), color(*s.right())) {
                    // Case 1.1: `s` is a 2-node.
                    (Color::Black, Color::Black) => {
                        *s.color() = Color::Red;
                        p.update();
                        x = Some(p);
                    }
                    // Case 1.2: `s` is a left-leaning 3-node.
                    (Color::Red, Color::Black) => {
                        let mut c = s.left().unwrap();
                        rotate_right(s);
                        rotate_left(p);
                        *c.color() = *p.color();
                        *p.color() = Color::Black;
                        s.update();
                        break;
                    }
                    // Case 1.3: `s` is a right-leaning 3-node, or a 4-node.
                    (_, Color::Red) => {
                        rotate_left(p);
                        *s.color() = *p.color();
                        *p.color() = Color::Black;
                        *s.right().unwrap().color() = Color::Black;
                        break;
                    }
                }
            }
            // Case 2: `x` is the right child.
            else {
                let mut s = p.left().unwrap();
                if *s.color() == Color::Red {
                    rotate_right(p);
                    *p.color() = Color::Red;
                    *s.color() = Color::Black;
                    s = p.left().unwrap();
                }
                match (color(*s.left()), color(*s.right())) {
                    // Case 2.1: `s` is a 2-node.
                    (Color::Black, Color::Black) => {
                        *s.color() = Color::Red;
                        p.update();
                        x = Some(p);
                    }
                    // Case 2.2: `s` os a right-leaning 3-node.
                    (Color::Black, Color::Red) => {
                        let mut c = s.right().unwrap();
                        rotate_left(s);
                        rotate_right(p);
                        *c.color() = *p.color();
                        *p.color() = Color::Black;
                        s.update();
                        break;
                    }
                    // Case 2.3: `s` is a left-leaning 3-node, or a 4-node.
                    (Color::Red, _) => {
                        rotate_right(p);
                        *s.color() = *p.color();
                        *p.color() = Color::Black;
                        *s.left().unwrap().color() = Color::Black;
                        break;
                    }
                }
            }
        }
        self.root = Some(match x {
            None => {
                p.unwrap().update();
                p.unwrap().update_ancestors()
            }
            Some(x) => x.update_ancestors(),
        })
    }

    pub fn transplant(&mut self, mut place: Ptr<T>, new: Option<Ptr<T>>) {
        if let Some(mut p) = *place.parent() {
            *(if *p.left() == Some(place) { p.left() } else { p.right() }) = new;
        } else {
            self.root = new;
        }
        if let Some(mut new) = new {
            *new.parent() = *place.parent();
        }
    }
}

pub struct BlackViolation<T: Balance> {
    pub p: Option<Ptr<T>>,
    pub x: Option<Ptr<T>>,
}
impl<T: Balance> PartialEq for BlackViolation<T> {
    fn eq(&self, other: &Self) -> bool { (self.p, self.x) == (other.p, other.x) }
}
impl<T: Balance> fmt::Debug for BlackViolation<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BlackViolation")
            .field("p", &self.p)
            .field("x", &self.x)
            .finish()
    }
}
impl<T: Balance> Clone for BlackViolation<T> {
    fn clone(&self) -> Self {
        Self {
            p: self.p,
            x: self.x,
        }
    }
}
impl<T: Balance> Copy for BlackViolation<T> {}

fn color<T: Balance>(x: Option<Ptr<T>>) -> Color {
    match x {
        None => Color::Black,
        Some(mut x) => *x.color(),
    }
}

fn rotate_left<T: Balance>(mut l: Ptr<T>) {
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

fn rotate_right<T: Balance>(mut r: Ptr<T>) {
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

pub struct Ptr<T>(NonNull<T>);
impl<T: Balance> Ptr<T> {
    pub fn new(x: T) -> Self { Self(NonNull::from(Box::leak(Box::new(x)))) }

    pub fn free(self) -> T { unsafe { *Box::from_raw(self.0.as_ptr()) } }

    // Returns the root
    pub fn update_ancestors(self) -> Self {
        let mut x = self;
        while let Some(mut p) = *x.parent() {
            p.update();
            x = p;
        }
        x
    }

    pub fn as_longlife_ref<'a>(self) -> &'a T { unsafe { self.0.as_ref() } }

    pub fn as_longlife_mut<'a>(mut self) -> &'a mut T { unsafe { self.0.as_mut() } }
}
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
pub mod test_utils {
    use super::BlackViolation;
    use super::Color;
    use super::Ptr;
    use super::Tree;
    use crate::balance::Balance;
    use rand::rngs::StdRng;
    use rand::Rng;
    use std::cmp::Ordering;
    use std::fmt;

    impl<T: Balance> fmt::Display for Tree<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            self.fmt_by(f, |p| format!("{:?}", p))
        }
    }
    struct TreeFormatter<'a, T: Balance, F: Fn(Ptr<T>) -> String>(&'a Tree<T>, &'a F);
    impl<'a, T: Balance, F: Fn(Ptr<T>) -> String> fmt::Display for TreeFormatter<'a, T, F> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            self.0.fmt_by(f, |p| (self.1)(p))
        }
    }
    impl<T: Balance> Tree<T> {
        pub fn format_by<F: Fn(Ptr<T>) -> String>(&self, key: F) -> String {
            format!("{}", TreeFormatter(self, &key))
        }

        fn fmt_by(
            &self,
            f: &mut fmt::Formatter<'_>,
            mut key: impl Fn(Ptr<T>) -> String,
        ) -> fmt::Result {
            fn write<T: Balance>(
                s: &mut fmt::Formatter<'_>,
                x: Option<Ptr<T>>,
                p: Option<Ptr<T>>,
                vios: &Violations<T>,
                key: &mut impl Fn(Ptr<T>) -> String,
            ) -> fmt::Result {
                if vios.black_vios.contains(&BlackViolation { p, x }) {
                    write!(s, "\x1b[40m\x1b[37m«\x1b[0m")?;
                }
                if let Some(mut x) = x {
                    if *x.color() == Color::Black {
                        write!(s, "[")?
                    }
                    write(s, *x.left(), Some(x), vios, key)?;
                    if vios.red_vios.contains(&x) {
                        write!(s, "\x1b[41m\x1b[37m{}\x1b[0m", key(x))?;
                    } else {
                        match *x.color() {
                            Color::Black => write!(s, "\x1b[30m{}\x1b[0m", key(x))?,
                            Color::Red => write!(s, "\x1b[31m{}\x1b[0m", key(x))?,
                        }
                    }
                    write(s, *x.right(), Some(x), vios, key)?;
                    if *x.color() == Color::Black {
                        write!(s, "]")?;
                    }
                }
                if vios.black_vios.contains(&BlackViolation { p, x }) {
                    write!(s, "\x1b[40m\x1b[37m»\x1b[0m")?;
                }
                Ok(())
            }
            let vios = Violations::collect(self);
            write!(f, "Tree({}, \"", self.black_height)?;
            write(f, self.root, None, &vios, &mut key)?;
            write!(f, "\")")?;
            Ok(())
        }

        #[allow(clippy::too_many_lines)]
        pub fn random(
            rng: &mut StdRng,
            mut new_node: impl Fn(&mut StdRng, Color) -> T,
            black_height: u8,
            red_vio: bool,
            black_vio: bool,
        ) -> (Self, Violations<T>) {
            #[allow(clippy::too_many_lines)]
            fn random_tree<T: Balance>(
                rng: &mut StdRng,
                new_node: &mut impl Fn(&mut StdRng, Color) -> T,
                mut black_height: u8,
                red_vio: bool,
                black_vio: bool,
                parent: Option<Ptr<T>>,
            ) -> (Option<Ptr<T>>, Violations<T>) {
                // Select the violation position here
                let parent_color = parent.map_or(Color::Black, |mut p| *p.color());
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
                    Some(Ptr::new(new_node(rng, color)))
                };
                let mut vios = Violations::default();
                if here_red_vio {
                    vios.red_vios.push(here.unwrap());
                }
                if here_black_vio {
                    vios.black_vios.push(BlackViolation { x: here, p: parent });
                }

                // Recurse
                if let Some(mut here) = here {
                    let children_black_height = black_height - u8::from(color == Color::Black);
                    let (mut left, left_vio) = random_tree(
                        rng,
                        new_node,
                        children_black_height,
                        left_red_vio,
                        left_black_vio,
                        Some(here),
                    );
                    vios.append(left_vio);
                    let (mut right, right_vio) = random_tree(
                        rng,
                        new_node,
                        children_black_height,
                        right_red_vio,
                        right_black_vio,
                        Some(here),
                    );
                    vios.append(right_vio);

                    if let Some(left) = left.as_mut() {
                        *left.parent() = Some(here);
                    }
                    if let Some(right) = right.as_mut() {
                        *right.parent() = Some(here);
                    }
                    *here.left() = left;
                    *here.right() = right;
                }
                (here, vios)
            }
            let (root, vios) =
                random_tree(rng, &mut new_node, black_height, red_vio, black_vio, None);
            (Tree { root, black_height }, vios)
        }

        pub fn validate(&self) {
            fn validate<T: Balance>(x: Option<Ptr<T>>) -> Result<u8, String> {
                let Some(mut x) = x else {
                    return Ok(0);
                };
                let left_height = validate(*x.left())?;
                let right_height = validate(*x.right())?;
                (left_height == right_height
                    || left_height == right_height + 1
                    || left_height + 1 == right_height)
                    .then_some(())
                    .ok_or_else(|| {
                        format!("The difference of black height is greater than 1: {:?}", x)
                    })?;

                // Parent pointer incinsistency
                if let Some(mut left) = *x.left() {
                    let p = *left.parent();
                    (p == Some(x)).then_some(()).ok_or_else(|| {
                        format!(
                            "parent pointer inconsistency between {:?} and its left child {:?}. \
                             The parent of the left child is {:?}",
                            x, left, p,
                        )
                    })?;
                }
                if let Some(mut right) = *x.right() {
                    let p = *right.parent();
                    (p == Some(x)).then_some(()).ok_or_else(|| {
                        format!(
                            "parent pointer inconsistency between {:?} and its right child {:?}. \
                             The parent of the right child is {:?}",
                            x, right, p,
                        )
                    })?;
                }
                Ok(left_height.max(right_height) + u8::from(*x.color() == Color::Black))
            }
            || -> Result<(), String> {
                let h = validate(self.root)?;
                (self.black_height == h || self.black_height == h + 1)
                    .then_some(())
                    .ok_or_else(|| format!("black height of {} is not {}", self, h))?;
                if let Some(mut x) = self.root {
                    // Parent is None
                    (x.parent().is_none())
                        .then_some(())
                        .ok_or_else(|| format!("parent of {:?} is not None", x))?;
                }
                Ok(())
            }()
            .unwrap_or_else(|e| panic!("Validation error: {}\nTree: {}", e, self))
        }

        pub fn collect(&self) -> Vec<Ptr<T>> {
            fn extend<T: Balance>(x: Option<Ptr<T>>, out: &mut Vec<Ptr<T>>) {
                if let Some(mut x) = x {
                    extend(*x.left(), out);
                    out.push(x);
                    extend(*x.right(), out);
                }
            }
            let mut out = Vec::new();
            extend(self.root, &mut out);
            out
        }
    }

    #[allow(clippy::type_complexity)]
    pub struct Violations<T: Balance> {
        pub red_vios: Vec<Ptr<T>>,
        pub black_vios: Vec<BlackViolation<T>>,
    }
    impl<T: Balance> Default for Violations<T> {
        fn default() -> Self {
            Self {
                red_vios: Vec::new(),
                black_vios: Vec::new(),
            }
        }
    }
    impl<T: Balance> PartialEq for Violations<T> {
        fn eq(&self, other: &Self) -> bool {
            self.red_vios == other.red_vios && self.black_vios == other.black_vios
        }
    }
    impl<T: Balance> fmt::Debug for Violations<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Violations")
                .field("red_vios", &self.red_vios)
                .field("black_vios", &self.black_vios)
                .finish()
        }
    }
    impl<T: Balance> Violations<T> {
        pub fn append(&mut self, other: Self) {
            self.red_vios.extend(other.red_vios);
            self.black_vios.extend(other.black_vios);
        }

        pub fn collect(tree: &Tree<T>) -> Self {
            fn extend<T: Balance>(
                x: Option<Ptr<T>>,
                p: Option<Ptr<T>>,
                vios: &mut Violations<T>,
            ) -> u8 {
                let Some(mut x) = x else { return 0 };
                let left_height = extend(*x.left(), Some(x), vios);
                let right_height = extend(*x.right(), Some(x), vios);
                match left_height.cmp(&right_height) {
                    Ordering::Less => vios.black_vios.push(BlackViolation {
                        p: Some(x),
                        x: *x.left(),
                    }),
                    Ordering::Greater => vios.black_vios.push(BlackViolation {
                        p: Some(x),
                        x: *x.right(),
                    }),
                    Ordering::Equal => {}
                }
                if let Some(mut p) = p {
                    if *p.color() == Color::Red && *x.color() == Color::Red {
                        vios.red_vios.push(x);
                    }
                }
                left_height.max(right_height) + u8::from(*x.color() == Color::Black)
            }
            let mut vios = Self::default();
            let h = extend(tree.root, None, &mut vios);
            if tree.black_height != h {
                vios.black_vios.push(BlackViolation {
                    p: None,
                    x: tree.root,
                })
            }
            vios
        }
    }
}

#[cfg(test)]
mod test_fix {
    use super::Color;
    use super::Ptr;
    use crate::balance::test_utils::Violations;
    use crate::balance::Tree;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    pub struct Node {
        pub color: Color,
        pub parent: Option<Ptr<Self>>,
        pub left: Option<Ptr<Self>>,
        pub right: Option<Ptr<Self>>,
    }

    impl super::Balance for Node {
        fn update(&mut self) {}

        fn push(&mut self) {}

        fn color(&mut self) -> &mut Color { &mut self.color }

        fn parent(&mut self) -> &mut Option<Ptr<Self>> { &mut self.parent }

        fn left(&mut self) -> &mut Option<Ptr<Self>> { &mut self.left }

        fn right(&mut self) -> &mut Option<Ptr<Self>> { &mut self.right }
    }

    fn new_node(_: &mut StdRng, color: Color) -> Node {
        Node {
            color,
            parent: None,
            left: None,
            right: None,
        }
    }

    #[test]
    fn test_random_tree_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(0..=4);
            let (tree, expected_violations) = Tree::random(&mut rng, new_node, h, false, false);
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
            let (tree, expected_violations) = Tree::random(&mut rng, new_node, h, true, false);
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
            let (tree, expected_violations) = Tree::random(&mut rng, new_node, h, false, true);
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
            let (mut tree, vios) = Tree::random(&mut rng, new_node, h, true, false);
            let before = tree.collect();

            tree.fix_red(vios.red_vios[0]);
            let after = tree.collect();
            tree.validate();

            // Make sure the violation has fixed.
            assert_eq!(Violations::collect(&tree), Violations::default());
            // Make sure the sequence of nodes has not changed.
            assert_eq!(before, after);
        }
    }

    #[test]
    fn test_fix_black() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(1..=4);
            let (mut tree, vios) = Tree::random(&mut rng, new_node, h, false, true);
            let before = tree.collect();

            tree.fix_black(vios.black_vios[0]);
            let after = tree.collect();
            tree.validate();

            // Make sure the violation has fixed.
            assert_eq!(Violations::collect(&tree), Violations::default());
            // Make sure the sequence of nodes has not changed.
            assert_eq!(before, after);
        }
    }
}

#[cfg(test)]
mod test_update {
    use super::test_utils::Violations;
    use super::Balance as _;
    use super::Color;
    use super::Ptr;
    use crate::balance::Tree;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    const VALUE_LIM: i32 = 20;

    struct SumNode {
        pub value: i32,
        pub sum: i32,
        pub color: Color,
        pub parent: Option<Ptr<Self>>,
        pub left: Option<Ptr<Self>>,
        pub right: Option<Ptr<Self>>,
    }
    fn sum(p: Option<Ptr<SumNode>>) -> i32 { p.map_or(0, |p| p.sum) }
    impl super::Balance for SumNode {
        fn update(&mut self) { self.sum = sum(self.left) + self.value + sum(self.right); }

        fn push(&mut self) {}

        fn color(&mut self) -> &mut Color { &mut self.color }

        fn parent(&mut self) -> &mut Option<Ptr<Self>> { &mut self.parent }

        fn left(&mut self) -> &mut Option<Ptr<Self>> { &mut self.left }

        fn right(&mut self) -> &mut Option<Ptr<Self>> { &mut self.right }
    }

    impl Tree<SumNode> {
        fn random_sum(
            rng: &mut StdRng,
            black_height: u8,
            red_vio: bool,
            black_vio: bool,
        ) -> (Self, Violations<SumNode>) {
            fn new_node(rng: &mut StdRng, color: Color) -> SumNode {
                let value = rng.gen_range(0..VALUE_LIM);
                SumNode {
                    value,
                    sum: value,
                    color,
                    parent: None,
                    left: None,
                    right: None,
                }
            }
            fn update(p: Option<Ptr<SumNode>>) {
                if let Some(mut p) = p {
                    update(p.left);
                    update(p.right);
                    p.update();
                }
            }

            let (tree, vios) = Self::random(rng, new_node, black_height, red_vio, black_vio);
            update(tree.root);
            (tree, vios)
        }

        fn validate_sum(&self) {
            fn validate_sum(p: Option<Ptr<SumNode>>) -> Result<(), String> {
                if let Some(p) = p {
                    validate_sum(p.left)?;
                    let expected = sum(p.left) + p.value + sum(p.right);
                    (p.sum == expected).then_some(()).ok_or_else(|| {
                        format!(
                            "Sum is incorrect at {:?}. Expected {}, but cached {}",
                            p, expected, p.sum
                        )
                    })?;
                    validate_sum(p.right)?;
                }
                Ok(())
            }
            validate_sum(self.root).unwrap_or_else(|e| {
                panic!(
                    "{e}:\n Tree: {}",
                    self.format_by(|p| format!("<{:?}:{},{}>", p, p.value, p.sum))
                )
            });
        }
    }

    #[test]
    fn test_random_tree_is_valid() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(0..=4);
            let (tree, _) = Tree::random_sum(&mut rng, h, false, false);
            tree.validate_sum();
        }
    }

    #[test]
    fn test_fix_red() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(1..=4);
            let (mut tree, vios) = Tree::random_sum(&mut rng, h, true, false);
            let mut p = vios.red_vios[0];
            tree.validate_sum();

            // Change this value to make sure `fix_red` updates all the proper ancestors.
            p.value = rng.gen_range(0..VALUE_LIM);
            p.update();

            tree.fix_red(p);
            tree.validate_sum();
        }
    }

    #[test]
    fn test_fix_black() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..200 {
            let h = rng.gen_range(1..=4);
            let (mut tree, vios) = Tree::random_sum(&mut rng, h, false, true);
            let vio = vios.black_vios[0];
            tree.validate_sum();

            // Change this value to make sure `fix_black` updates all the proper ancestors.
            if let Some(mut p) = vio.p {
                p.value = rng.gen_range(0..VALUE_LIM);
            }

            tree.fix_black(vio);
            tree.validate_sum();
        }
    }
}
