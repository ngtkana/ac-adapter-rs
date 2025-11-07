#![allow(clippy::unnecessary_box_returns)]
#![allow(clippy::type_complexity)]

use std::{cmp::Ordering, mem};

pub struct AvlTree<C: NodeMarker> {
    pub root: Option<Box<Node<C>>>,
}

impl<C: NodeMarker> Default for AvlTree<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: NodeMarker> AvlTree<C> {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |x| x.len)
    }

    pub fn insert(&mut self, index: usize, value: C::Value) {
        assert!(index <= self.len());
        let c = Box::new(Node::new(value));
        let (l, r) = split2(self.root.take(), index);
        self.root = Some(merge3(l, c, r));
    }

    pub fn remove(&mut self, index: usize) -> C::Value {
        assert!(index < self.len());
        let (l, c, r) = split3(self.root.take().unwrap(), index);
        self.root = merge2(l, r);
        c.value
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        assert!(index <= self.len());
        let (l, r) = split2(self.root.take(), index);
        self.root = l;
        Self { root: r }
    }

    pub fn append(&mut self, rhs: Self) {
        self.root = merge2(self.root.take(), rhs.root);
    }

    pub fn reverse(&mut self, start: usize, end: usize) {
        assert!(start <= end && end <= self.len());
        let (lc, r) = split2(self.root.take(), end);
        let (l, mut c) = split2(lc, start);
        if let Some(c) = c.as_deref_mut() {
            c.rev ^= true;
        }
        let lc = merge2(l, c);
        self.root = merge2(lc, r);
    }

    pub fn product(&mut self, start: usize, end: usize) -> C::Prod {
        fold(self.root.as_deref_mut(), start, end, 0, C::identity())
    }

    pub fn touch<T>(
        &mut self,
        start: usize,
        end: usize,
        f: impl FnMut(&mut Node<C>) -> T,
    ) -> Option<T> {
        assert!(start <= end && end <= self.len());
        let (lc, r) = split2(self.root.take(), end);
        let (l, mut c) = split2(lc, start);
        let result = c.as_deref_mut().map(f);
        let lc = merge2(l, c);
        self.root = merge2(lc, r);
        result
    }
}

impl<C: NodeMarker> FromIterator<C::Value> for AvlTree<C>
// TODO: I don't want to require clone here
where
    C::Value: Clone,
{
    fn from_iter<T: IntoIterator<Item = C::Value>>(iter: T) -> Self {
        fn from_slice<C: NodeMarker>(slice: &[C::Value]) -> Option<Box<Node<C>>>
        where
            C::Value: Clone,
        {
            if slice.is_empty() {
                return None;
            }
            let i = slice.len() / 2;
            let left = from_slice(&slice[..i]);
            let right = from_slice(&slice[i + 1..]);
            let mut x = Box::new(Node::new(slice[i].clone()));
            x.left = left;
            x.right = right;
            x.update();
            Some(x)
        }
        let slice: Vec<_> = iter.into_iter().collect();
        AvlTree {
            root: from_slice(&slice),
        }
    }
}

pub struct Node<C: NodeMarker + ?Sized> {
    pub left: Option<Box<Self>>,
    pub right: Option<Box<Self>>,
    pub ht: u8,
    pub len: usize,
    pub rev: bool,
    pub value: C::Value,
    pub prod: C::Prod,
    pub op: C::Operator,
}

impl<C: NodeMarker> Node<C> {
    pub fn new(value: C::Value) -> Self {
        Self {
            left: None,
            right: None,
            ht: 1,
            len: 1,
            rev: false,
            prod: C::singleton(&value),
            value,
            op: C::nop(),
        }
    }
    fn update(&mut self) {
        self.len =
            self.left.as_ref().map_or(0, |l| l.len) + 1 + self.right.as_ref().map_or(0, |r| r.len);
        self.ht = 1 + self
            .left
            .as_ref()
            .map_or(0, |l| l.ht)
            .max(self.right.as_ref().map_or(0, |r| r.ht));
        self.prod = C::identity();
        if let Some(l) = self.left.as_mut() {
            self.prod = C::mul(&self.prod, &l.prod);
        }
        self.prod = C::mul(&self.prod, &C::singleton(&self.value));
        if let Some(r) = self.right.as_mut() {
            self.prod = C::mul(&self.prod, &r.prod);
        }
    }
    fn push(&mut self) {
        if self.rev {
            self.rev = false;
            mem::swap(&mut self.left, &mut self.right);
            if let Some(l) = self.left.as_mut() {
                l.rev ^= true;
            }
            if let Some(r) = self.right.as_mut() {
                r.rev ^= true;
            }
        }
        if self.op != C::nop() {
            let op = std::mem::replace(&mut self.op, C::nop());
            if let Some(l) = self.left.as_deref_mut() {
                C::op_value(&op, &mut l.value);
                C::op_prod(&op, &mut l.prod, l.len);
                C::compose(&op, &mut l.op);
            }
            if let Some(r) = self.right.as_deref_mut() {
                C::op_value(&op, &mut r.value);
                C::op_prod(&op, &mut r.prod, r.len);
                C::compose(&op, &mut r.op);
            }
        }
    }
}

pub trait NodeMarker {
    type Value;

    type Prod;

    type Operator: PartialEq;

    fn singleton(value: &Self::Value) -> Self::Prod;

    fn mul(lhs: &Self::Prod, rhs: &Self::Prod) -> Self::Prod;

    fn identity() -> Self::Prod;

    fn nop() -> Self::Operator;

    fn op_value(f: &Self::Operator, x: &mut Self::Value);

    fn op_prod(f: &Self::Operator, x: &mut Self::Prod, len: usize);

    fn compose(f: &Self::Operator, g: &mut Self::Operator);
}

pub fn fold<C: NodeMarker>(
    x: Option<&mut Node<C>>,
    start: usize,
    end: usize,
    offset: usize,
    mut init: C::Prod,
) -> C::Prod {
    let Some(x) = x else { return init };
    x.push();
    if start <= offset && offset + x.len <= end {
        return C::mul(&init, &x.prod);
    }
    let pivot = offset + x.left.as_deref().map_or(0, |l| l.len);
    if start < pivot {
        init = fold(x.left.as_deref_mut(), start, end, offset, init);
    }
    if (start..end).contains(&pivot) {
        init = C::mul(&init, &C::singleton(&x.value));
    }
    if pivot + 1 < end {
        init = fold(x.right.as_deref_mut(), start, end, pivot + 1, init);
    }
    init
}

pub fn merge2<C: NodeMarker>(
    l: Option<Box<Node<C>>>,
    mut r: Option<Box<Node<C>>>,
) -> Option<Box<Node<C>>> {
    let Some(r) = r.take() else { return l };
    let (_, c, r) = split3(r, 0);
    Some(merge3(l, c, r))
}

pub fn merge3<C: NodeMarker>(
    l: Option<Box<Node<C>>>,
    mut c: Box<Node<C>>,
    r: Option<Box<Node<C>>>,
) -> Box<Node<C>> {
    match ht(l.as_deref()).cmp(&ht(r.as_deref())) {
        Ordering::Less => {
            let mut r = r.unwrap();
            r.push();
            r.left = Some(merge3(l, c, r.left));
            balance(r)
        }
        Ordering::Equal => {
            c.left = l;
            c.right = r;
            c.update();
            c
        }
        Ordering::Greater => {
            let mut l = l.unwrap();
            l.push();
            l.right = Some(merge3(l.right, c, r));
            balance(l)
        }
    }
}

pub fn split2<C: NodeMarker>(
    x: Option<Box<Node<C>>>,
    index: usize,
) -> (Option<Box<Node<C>>>, Option<Box<Node<C>>>) {
    assert!(index <= x.as_ref().map_or(0, |x| x.len));
    let Some(indexm1) = index.checked_sub(1) else { return (None, x) };
    let (l, c, r) = split3(x.unwrap(), indexm1);
    (merge2(l, Some(c)), r)
}

pub fn split3<C: NodeMarker>(
    mut x: Box<Node<C>>,
    index: usize,
) -> (Option<Box<Node<C>>>, Box<Node<C>>, Option<Box<Node<C>>>) {
    x.push();
    let llen = x.left.as_ref().map_or(0, |l| l.len);
    let l = x.left.take();
    let r = x.right.take();
    match index.cmp(&llen) {
        Ordering::Less => {
            let (ll, lc, lr) = split3(l.unwrap(), index);
            (ll, lc, Some(merge3(lr, x, r)))
        }
        Ordering::Equal => {
            x.update();
            (l, x, r)
        }
        Ordering::Greater => {
            let (rl, rc, rr) = split3(r.unwrap(), index - 1 - llen);
            (Some(merge3(l, x, rl)), rc, rr)
        }
    }
}

fn balance<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    match ht(x.left.as_deref()) as i8 - ht(x.right.as_deref()) as i8 {
        -2 => {
            x.right = x.right.map(|mut r| {
                if ht(r.left.as_deref()) > ht(r.right.as_deref()) {
                    r.push();
                    r = rotate_right(r);
                }
                r
            });
            x = rotate_left(x);
        }
        -1..=1 => x.update(),
        2 => {
            x.left = x.left.map(|mut l| {
                if ht(l.left.as_deref()) < ht(l.right.as_deref()) {
                    l.push();
                    l = rotate_left(l);
                }
                l
            });
            x = rotate_right(x);
        }
        _ => unreachable!(),
    }
    x
}

fn ht<C: NodeMarker>(x: Option<&Node<C>>) -> u8 {
    x.as_ref().map_or(0, |x| x.ht)
}

fn rotate_left<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    x.push();
    let mut y = x.right.take().unwrap();
    y.push();
    x.right = y.left.take();
    x.update();
    y.left = Some(x);
    y.update();
    y
}

fn rotate_right<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    x.push();
    let mut y = x.left.take().unwrap();
    y.push();
    x.left = y.right.take();
    x.update();
    y.right = Some(x);
    y.update();
    y
}

#[cfg(test)]
pub mod debug {
    use std::fmt::Debug;

    use super::{Node, NodeMarker};

    pub fn display<C: NodeMarker>(x: Option<&Node<C>>) -> String
    where
        C::Value: Debug,
        C::Prod: Debug,
        C::Operator: Debug,
    {
        fn display_recur<C: NodeMarker>(x: &Node<C>, s: &mut String, d: u8)
        where
            C::Value: Debug,
            C::Prod: Debug,
            C::Operator: Debug,
        {
            use std::fmt::Write;
            if let Some(l) = x.left.as_ref() {
                display_recur(l, s, d + 1);
            }
            let Node {
                ht,
                len,
                rev,
                value,
                prod,
                op,
                ..
            } = x;
            writeln!(
                s,
                "{space1}●{space2} len={len:2} ht={ht} {rev}{{ value: {value:?}, prod: {prod:?}, op: {op:?} }}",
                space1 = " ".repeat(d as usize),
                space2 = " ".repeat(6_usize.saturating_sub(d as usize)),
                rev = if *rev { "[rev] " } else { "      " },
            )
            .unwrap();
            if let Some(r) = x.right.as_ref() {
                display_recur(r, s, d + 1);
            }
        }
        let Some(x) = x else { return "(empty)".to_owned() };
        let mut s = String::new();
        display_recur(x, &mut s, 1);
        s
    }

    pub fn validate<C: NodeMarker>(x: Option<&Node<C>>)
    where
        C::Value: Debug,
        C::Prod: Debug + PartialEq + Clone,
        C::Operator: Clone,
    {
        fn validate_recur<C: NodeMarker>(x: &Node<C>, rev: bool)
        where
            C::Value: Debug,
            C::Prod: Debug + PartialEq + Clone,
            C::Operator: Clone,
        {
            let lh = x.left.as_ref().map_or(0, |l| l.ht);
            let rh = x.right.as_ref().map_or(0, |r| r.ht);
            assert!(matches!(lh as i8 - rh as i8, -1..=1));
            assert_eq!(lh.max(rh) + 1, x.ht);
            let mut prod = C::identity();
            if let Some(p) = if rev { x.right.as_ref() } else { x.left.as_ref() } {
                let mut p_prod = p.prod.clone();
                C::op_prod(&x.op, &mut p_prod, p.len);
                prod = C::mul(&prod, &p_prod);
                validate_recur(p, rev ^ x.rev);
            }
            prod = C::mul(&prod, &C::singleton(&x.value));
            if let Some(p) = if rev { x.left.as_ref() } else { x.right.as_ref() } {
                let mut p_prod = p.prod.clone();
                C::op_prod(&x.op, &mut p_prod, p.len);
                prod = C::mul(&prod, &p_prod);
                validate_recur(p, rev ^ x.rev);
            }
            assert_eq!(&prod, &x.prod);
        }
        let Some(x) = x else { return };
        validate_recur(x, false);
    }

    pub fn collect<C: NodeMarker>(x: Option<&Node<C>>) -> Vec<C::Value>
    where
        C::Value: Clone,
        C::Operator: Clone,
    {
        fn collect_recur<C: NodeMarker>(
            x: &Node<C>,
            out: &mut Vec<C::Value>,
            mut rev: bool,
            op: C::Operator,
        ) where
            C::Value: Clone,
            C::Operator: Clone,
        {
            let mut value = x.value.clone();
            C::op_value(&op, &mut value);
            let mut next_op = x.op.clone();
            C::compose(&op, &mut next_op);
            rev ^= x.rev;
            if let Some(y) = if rev { x.right.as_ref() } else { x.left.as_ref() } {
                collect_recur(y, out, rev, next_op.clone());
            }
            out.push(value);
            if let Some(y) = if rev { x.left.as_ref() } else { x.right.as_ref() } {
                collect_recur(y, out, rev, next_op);
            }
        }
        let Some(x) = x else { return vec![] };
        let mut out = Vec::new();
        collect_recur(x, &mut out, false, C::nop());
        out
    }
}
