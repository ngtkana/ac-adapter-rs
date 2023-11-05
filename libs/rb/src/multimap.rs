use crate::balance::Balance;
use crate::balance::BlackViolation;
use crate::balance::Color;
use crate::balance::Ptr;
use crate::balance::Tree;
use std::borrow::Borrow;
use std::cmp::Ordering;

pub trait MultimapOp {
    type Value;
    type Acc;
    type Lazy: PartialEq;

    fn to_acc(value: &Self::Value) -> Self::Acc;

    fn join(lhs: Option<&Self::Acc>, center: &Self::Value, rhs: Option<&Self::Acc>) -> Self::Acc;

    fn apply(_value: &mut Self::Value, _lazy: &Self::Lazy);

    fn compose(_lhs: &Self::Lazy, _rhs: &Self::Lazy) -> Self::Lazy;

    fn identity() -> Self::Lazy;

    fn is_identity(lazy: &Self::Lazy) -> bool { *lazy == Self::identity() }
}

#[allow(dead_code)]
pub struct Node<K, O: MultimapOp> {
    key: K,
    value: O::Value,
    acc: O::Acc,
    lazy: O::Lazy,
    parent: Option<Ptr<Node<K, O>>>,
    left: Option<Ptr<Node<K, O>>>,
    right: Option<Ptr<Node<K, O>>>,
    len: usize,
    color: Color,
}
impl<K: Ord, O: MultimapOp> Node<K, O> {
    pub fn new(key: K, value: O::Value, color: Color) -> Self {
        Self {
            key,
            acc: O::to_acc(&value),
            value,
            lazy: O::identity(),
            parent: None,
            left: None,
            right: None,
            len: 1,
            color,
        }
    }
}
fn len<K, O: MultimapOp>(node: Option<Ptr<Node<K, O>>>) -> usize {
    node.as_ref().map_or(0, |node| node.len)
}
fn acc<K, O: MultimapOp>(node: &Option<Ptr<Node<K, O>>>) -> Option<&O::Acc> {
    node.as_ref().map(|node| &node.acc)
}
impl<K, O: MultimapOp> Balance for Node<K, O> {
    fn update(&mut self) {
        self.len = len(self.left) + 1 + len(self.right);
        self.acc = O::join(acc(&self.left), &self.value, acc(&self.right));
    }

    fn push(&mut self) {}

    fn color(&mut self) -> &mut Color { &mut self.color }

    fn parent(&mut self) -> &mut Option<Ptr<Self>> { &mut self.parent }

    fn left(&mut self) -> &mut Option<Ptr<Self>> { &mut self.left }

    fn right(&mut self) -> &mut Option<Ptr<Self>> { &mut self.right }
}

pub struct Multimap<K, O: MultimapOp> {
    tree: Tree<Node<K, O>>,
}
impl<K: Ord, O: MultimapOp> Multimap<K, O> {
    pub fn new() -> Self { Self { tree: Tree::new() } }

    pub fn len(&self) -> usize { len(self.tree.root) }

    pub fn is_empty(&self) -> bool { self.tree.root.is_none() }

    pub fn nth(&self, n: usize) -> (&K, &O::Value) {
        let x = self.nth_ptr(n).as_longlife_ref();
        (&x.key, &x.value)
    }

    pub fn insert(&mut self, key: K, value: O::Value) {
        let mut new = Ptr::new(Node::new(key, value, Color::Red));
        let Some(mut x) = self.tree.root else {
            new.color = Color::Black;
            self.tree.root = Some(new);
            self.tree.black_height = 1;
            return;
        };
        let key = &new.key;
        loop {
            match key.cmp(&x.key) {
                Ordering::Less | Ordering::Equal => {
                    if let Some(left) = x.left {
                        x = left;
                    } else {
                        new.parent = Some(x);
                        x.left = Some(new);
                        break;
                    }
                }
                Ordering::Greater => {
                    if let Some(right) = x.right {
                        x = right;
                    } else {
                        new.parent = Some(x);
                        x.right = Some(new);
                        break;
                    }
                }
            }
        }
        if x.color == Color::Red {
            self.tree.fix_red(new);
        } else {
            new.update_ancestors();
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, O::Value)>
    where
        K: Ord + Borrow<Q>,
        Q: Ord,
    {
        let mut x = self.tree.root?;
        loop {
            match key.cmp(x.key.borrow()) {
                Ordering::Less => x = x.left?,
                Ordering::Greater => x = x.right?,
                Ordering::Equal => break,
            }
        }
        self.remove_ptr(x);
        let x = x.free();
        Some((x.key, x.value))
    }

    pub fn remove_nth(&mut self, n: usize) -> (K, O::Value) {
        let x = self.nth_ptr(n);
        self.remove_ptr(x);
        let x = x.free();
        (x.key, x.value)
    }

    fn nth_ptr(&self, mut n: usize) -> Ptr<Node<K, O>> {
        assert!(
            n < self.len(),
            "Index out of range: n = {n}, while len = {}",
            self.len()
        );
        let mut x = self.tree.root.unwrap();
        loop {
            let left_len = len(x.left);
            x = match n.cmp(&left_len) {
                Ordering::Less => x.left.unwrap(),
                Ordering::Equal => break,
                Ordering::Greater => {
                    n -= left_len + 1;
                    x.right.unwrap()
                }
            };
        }
        x
    }

    fn remove_ptr(&mut self, x: Ptr<Node<K, O>>) {
        let needs_fix;
        let black_vio;
        match (x.left, x.right) {
            (Some(_), Some(top)) => {
                let mut next = top;
                while let Some(left) = next.left {
                    next = left;
                }
                needs_fix = next.color == Color::Black;
                next.left = x.left;
                x.left.unwrap().parent = Some(next);
                next.color = x.color;
                if top == next {
                    black_vio = BlackViolation {
                        p: Some(next),
                        x: next.right,
                    };
                    self.tree.transplant(x, Some(next));
                } else {
                    black_vio = BlackViolation {
                        p: next.parent,
                        x: next.right,
                    };
                    self.tree.transplant(next, next.right);
                    next.right = x.right;
                    if let Some(mut r) = next.right {
                        r.parent = Some(next);
                    }
                    self.tree.transplant(x, Some(next));
                }
            }
            (None, Some(_)) => {
                needs_fix = x.color == Color::Black;
                black_vio = BlackViolation {
                    p: x.parent,
                    x: x.right,
                };
                self.tree.transplant(x, x.right);
            }
            (_, None) => {
                needs_fix = x.color == Color::Black;
                black_vio = BlackViolation {
                    p: x.parent,
                    x: x.left,
                };
                self.tree.transplant(x, x.left);
            }
        }
        if needs_fix {
            self.tree.fix_black(black_vio);
        } else if let Some(mut p) = black_vio.p {
            p.update();
            p.update_ancestors();
        }
    }
}

impl<K: Ord, O: MultimapOp> Default for Multimap<K, O> {
    fn default() -> Self { Self::new() }
}

enum Nop {}
impl MultimapOp for Nop {
    type Acc = ();
    type Lazy = ();
    type Value = ();

    fn to_acc(_value: &Self::Value) -> Self::Acc {}

    fn join(
        _lhs: Option<&Self::Acc>,
        _center: &Self::Value,
        _rhs: Option<&Self::Acc>,
    ) -> Self::Acc {
    }

    fn apply(_value: &mut Self::Value, _lazy: &Self::Lazy) {}

    fn compose(_lhs: &Self::Lazy, _rhs: &Self::Lazy) -> Self::Lazy {}

    fn identity() -> Self::Lazy {}
}

pub struct Multiset<K> {
    map: Multimap<K, Nop>,
}
impl<K: Ord> Multiset<K> {
    pub fn new() -> Self {
        Self {
            map: Multimap::new(),
        }
    }

    pub fn len(&self) -> usize { self.map.len() }

    pub fn is_empty(&self) -> bool { self.map.is_empty() }

    pub fn insert(&mut self, key: K) { self.map.insert(key, ()) }

    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<K>
    where
        K: Ord + Borrow<Q>,
        Q: Ord,
    {
        self.map.remove(key).map(|(k, _)| k)
    }

    pub fn nth(&self, n: usize) -> &K { self.map.nth(n).0 }

    pub fn remove_nth(&mut self, n: usize) -> K { self.map.remove_nth(n).0 }
}
impl<K: Ord> Default for Multiset<K> {
    fn default() -> Self { Self::new() }
}

#[cfg(test)]
mod test_multiset {
    use crate::balance::test_utils::Violations;
    use crate::balance::Ptr;
    use crate::multimap::len;
    use crate::multimap::Node;
    use crate::multimap::Nop;
    use crate::Multiset;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn to_vec<K: Ord + Clone>(set: &Multiset<K>) -> Vec<K> {
        set.map
            .tree
            .collect()
            .into_iter()
            .map(|x| x.key.clone())
            .collect()
    }

    impl Multiset<i32> {
        fn validate_len(&self) {
            fn validate_len(p: Option<Ptr<Node<i32, Nop>>>) -> Result<(), String> {
                if let Some(p) = p {
                    validate_len(p.left)?;
                    let expected = len(p.left) + 1 + len(p.right);
                    (p.len == expected).then_some(()).ok_or_else(|| {
                        format!(
                            "Len is incorrect at {:?}. Expected {}, but cached {}",
                            p, expected, p.len
                        )
                    })?;
                    validate_len(p.right)?;
                }
                Ok(())
            }
            validate_len(self.map.tree.root).unwrap_or_else(|e| {
                panic!(
                    "{e}:\n Tree: {}",
                    self.map.tree.format_by(|p| format!("<{:?}:{}>", p, p.len))
                )
            });
        }
    }

    #[test]
    fn test_insert_remove_nth() {
        const VALUE_LIM: i32 = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..10 {
            let mut set = Multiset::new();
            let mut vec = Vec::new();
            for _ in 0..200 {
                // Mutation
                match rng.gen_range(0..4) {
                    // Insert
                    0 | 1 => {
                        let key = rng.gen_range(0..VALUE_LIM);
                        set.insert(key);
                        let i = vec.binary_search(&key).unwrap_or_else(|i| i);
                        vec.insert(i, key);
                    }
                    // Remove
                    2 => {
                        let key = rng.gen_range(0..VALUE_LIM);
                        let result = set.remove(&key);
                        let expected = vec.binary_search(&key).ok().map(|i| vec.remove(i));
                        assert_eq!(result, expected);
                    }
                    // Remove nth
                    3 => {
                        if !vec.is_empty() {
                            let i = rng.gen_range(0..vec.len());
                            let result = set.remove_nth(i);
                            let expected = vec.remove(i);
                            assert_eq!(result, expected);
                        }
                    }
                    _ => unreachable!(),
                }
                assert_eq!(to_vec(&set), vec);

                set.map.tree.validate();
                assert_eq!(Violations::collect(&set.map.tree), Violations::default());
                set.validate_len();

                // Nth query
                for (i, &expected) in vec.iter().enumerate() {
                    let result = *set.nth(i);
                    assert_eq!(result, expected);
                }
            }
        }
    }
}
