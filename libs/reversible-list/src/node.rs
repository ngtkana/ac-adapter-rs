#![allow(clippy::unnecessary_box_returns)]
#![allow(clippy::type_complexity)]
#![allow(dead_code)]

#[allow(unused_imports)]
use crate::node::debug::display;

use procon_lg::lg_recur;
use std::cmp::Ordering;

pub(crate) struct Node<C: NodeMarker + ?Sized> {
    pub(crate) left: Option<Box<Self>>,
    pub(crate) right: Option<Box<Self>>,
    pub(crate) ht: u8,
    pub(crate) len: usize,
    pub(crate) rev: bool,
    pub(crate) data: C::Data,
}

impl<C: NodeMarker> Node<C> {
    pub(crate) fn new(data: C::Data) -> Self {
        Self {
            left: None,
            right: None,
            ht: 1,
            len: 1,
            rev: false,
            data,
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
        C::update(self);
    }
}

pub(crate) trait NodeMarker {
    type Data: std::fmt::Debug; // remove

    fn update(node: &mut Node<Self>);

    fn push(node: &mut Node<Self>);
}

pub(crate) fn merge2<C: NodeMarker>(
    l: Option<Box<Node<C>>>,
    mut r: Option<Box<Node<C>>>,
) -> Option<Box<Node<C>>> {
    let Some(r) = r.take() else { return l };
    let (_, c, r) = split3(r, |node| {
        if node.left.is_some() { Ordering::Less } else { Ordering::Equal }
    });
    Some(merge3(l, c, r))
}

pub(crate) fn split2_by_index<C: NodeMarker>(
    x: Option<Box<Node<C>>>,
    index: usize,
) -> (Option<Box<Node<C>>>, Option<Box<Node<C>>>) {
    assert!(index <= x.as_ref().map_or(0, |x| x.len));
    let Some(indexm1) = index.checked_sub(1) else { return (None, x) };
    let (l, c, r) = split3_by_index(x.unwrap(), indexm1);
    (merge2(l, Some(c)), r)
}

pub(crate) fn split2<C: NodeMarker>(
    x: Option<Box<Node<C>>>,
    mut pred: impl FnMut(&Node<C>) -> bool,
) -> (Option<Box<Node<C>>>, Option<Box<Node<C>>>) {
    let Some(x) = x else { return (None, None) };
    let (l, c, r) = split3(x, |node| {
        if node.left.is_none() && node.right.is_none() {
            Ordering::Equal
        } else if pred(node) {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    });
    if pred(c.as_ref()) {
        (Some(merge3(l, c, None)), r)
    } else {
        (l, Some(merge3(None, c, r)))
    }
}

#[lg_recur]
pub(crate) fn split3_by_index<C: NodeMarker>(
    mut x: Box<Node<C>>,
    index: usize,
) -> (Option<Box<Node<C>>>, Box<Node<C>>, Option<Box<Node<C>>>) {
    let llen = x.left.as_ref().map_or(0, |l| l.len);
    let l = x.left.take();
    let r = x.right.take();
    match index.cmp(&llen) {
        Ordering::Less => {
            let (ll, lc, lr) = split3_by_index(l.unwrap(), index);
            (ll, lc, Some(merge3(lr, x, r)))
        }
        Ordering::Equal => {
            x.update();
            (l, x, r)
        }
        Ordering::Greater => {
            let (rl, rc, rr) = split3_by_index(r.unwrap(), index - 1 - llen);
            (Some(merge3(l, x, rl)), rc, rr)
        }
    }
}

#[lg_recur]
pub(crate) fn split3<C: NodeMarker>(
    mut x: Box<Node<C>>,
    mut cmp: impl FnMut(&Node<C>) -> Ordering,
) -> (Option<Box<Node<C>>>, Box<Node<C>>, Option<Box<Node<C>>>) {
    C::push(&mut x);
    match cmp(&*x) {
        Ordering::Less => {
            let (ll, lc, lr) = split3(x.left.take().unwrap(), cmp);
            let r = x.right.take();
            (ll, lc, Some(merge3(lr, x, r)))
        }
        Ordering::Equal => {
            let l = x.left.take();
            let r = x.right.take();
            x.update();
            (l, x, r)
        }
        Ordering::Greater => {
            let (rl, rc, rr) = split3(x.right.take().unwrap(), cmp);
            let l = x.left.take();
            (Some(merge3(l, x, rl)), rc, rr)
        }
    }
}

#[lg_recur]
pub(crate) fn merge3<C: NodeMarker>(
    l: Option<Box<Node<C>>>,
    mut c: Box<Node<C>>,
    r: Option<Box<Node<C>>>,
) -> Box<Node<C>> {
    match ht(l.as_deref()).cmp(&ht(r.as_deref())) {
        Ordering::Less => {
            let mut r = r.unwrap();
            C::push(&mut r);
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
            C::push(&mut l);
            l.right = Some(merge3(l.right, c, r));
            balance(l)
        }
    }
}

#[lg_recur]
fn balance<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    match ht(x.left.as_deref()) as i8 - ht(x.right.as_deref()) as i8 {
        -2 => {
            x.right = x.right.map(|mut r| {
                if ht(r.left.as_deref()) > ht(r.right.as_deref()) {
                    C::push(&mut r);
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
                    C::push(&mut l);
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

#[lg_recur]
fn rotate_left<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    C::push(&mut *x);
    let mut y = x.right.take().unwrap();
    C::push(&mut y);
    x.right = y.left.take();
    (*x).update();
    y.left = Some(x);
    (*y).update();
    y
}

#[lg_recur]
fn rotate_right<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    C::push(&mut *x);
    let mut y = x.left.take().unwrap();
    C::push(&mut y);
    x.left = y.right.take();
    (*x).update();
    y.right = Some(x);
    (*y).update();
    y
}

pub(crate) mod debug {
    use super::{Node, NodeMarker};

    pub(crate) fn display<C: NodeMarker>(x: Option<&Node<C>>) -> String
    where
        C::Data: std::fmt::Debug,
    {
        fn display_recur<C: NodeMarker>(x: &Node<C>, s: &mut String, d: u8)
        where
            C::Data: std::fmt::Debug,
        {
            use std::fmt::Write;
            if let Some(l) = x.left.as_ref() {
                display_recur(l, s, d + 1);
            }
            writeln!(
                s,
                "{space1}●{space2} len={len} ht={ht} {data:?}",
                space1 = " ".repeat(d as usize),
                space2 = " ".repeat(4_usize.saturating_sub(d as usize)),
                len = x.len,
                ht = x.ht,
                data = x.data,
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

    pub(crate) fn validate<C: NodeMarker>(x: Option<&Node<C>>)
    where
        C::Data: std::fmt::Debug,
    {
        fn validate_recur<C: NodeMarker>(x: &Node<C>)
        where
            C::Data: std::fmt::Debug,
        {
            let lh = x.left.as_ref().map_or(0, |l| l.ht);
            let rh = x.right.as_ref().map_or(0, |r| r.ht);
            assert!(matches!(lh as i8 - rh as i8, -1..=1));
            assert_eq!(lh.max(rh) + 1, x.ht);
            if let Some(l) = x.left.as_ref() {
                validate_recur(l);
            }
            if let Some(r) = x.right.as_ref() {
                validate_recur(r);
            }
        }
        let Some(x) = x else { return };
        validate_recur(x);
    }

    pub(crate) fn collect<C: NodeMarker>(x: Option<&Node<C>>) -> Vec<C::Data>
    where
        C::Data: Clone,
    {
        fn collect_recur<C: NodeMarker>(x: &Node<C>, out: &mut Vec<C::Data>)
        where
            C::Data: Clone,
        {
            if let Some(l) = x.left.as_ref() {
                collect_recur(l, out);
            }
            out.push(x.data.clone());
            if let Some(r) = x.right.as_ref() {
                collect_recur(r, out);
            }
        }
        let Some(x) = x else { return vec![] };
        let mut out = Vec::new();
        collect_recur(x, &mut out);
        out
    }
}
