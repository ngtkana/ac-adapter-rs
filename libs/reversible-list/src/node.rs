#![allow(clippy::unnecessary_box_returns)]
#![allow(clippy::type_complexity)]
#![allow(dead_code)]

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
}

pub(crate) trait NodeMarker {
    type Data;

    fn update(node: &mut Node<Self>);

    fn push(node: &mut Node<Self>);
}

pub(crate) fn split2_by_index<C: NodeMarker>(
    x: Option<Box<Node<C>>>,
    mut index: usize,
) -> (Option<Box<Node<C>>>, Option<Box<Node<C>>>) {
    assert!(index <= x.as_ref().map_or(0, |x| x.len));
    split2(x, |node| {
        let llen = node.left.as_ref().map_or(0, |l| l.len);
        if llen < index {
            index -= llen + 1;
            false
        } else {
            true
        }
    })
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
    if pred(&*c) {
        (Some(merge3(l, c, None)), r)
    } else {
        (l, Some(merge3(None, c, r)))
    }
}

pub(crate) fn merge2<C: NodeMarker>(
    l: Option<Box<Node<C>>>,
    mut r: Option<Box<Node<C>>>,
) -> Option<Box<Node<C>>> {
    let Some(r) = r.take() else { return l };
    let (_, c, r) = split3(r, |_| Ordering::Less);
    Some(merge3(l, c, r))
}

pub(crate) fn split3<C: NodeMarker>(
    mut x: Box<Node<C>>,
    mut cmp: impl FnMut(&Node<C>) -> Ordering,
) -> (Option<Box<Node<C>>>, Box<Node<C>>, Option<Box<Node<C>>>) {
    C::push(&mut x);
    let l = x.left.take();
    let r = x.right.take();
    match cmp(&*x) {
        Ordering::Less => {
            let (ll, lc, lr) = split3(l.unwrap(), cmp);
            (ll, lc, Some(merge3(lr, x, r)))
        }
        Ordering::Equal => {
            C::update(&mut x);
            (l, x, r)
        }
        Ordering::Greater => {
            let (rl, rc, rr) = split3(r.unwrap(), cmp);
            (Some(merge3(l, x, rl)), rc, rr)
        }
    }
}

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
            C::update(&mut c);
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
        -1..=1 => C::update(&mut x),
        2 => {
            x.left = x.left.map(|mut l| {
                if ht(l.left.as_deref()) < ht(l.right.as_deref()) {
                    C::push(&mut l);
                    l = rotate_right(l);
                }
                l
            });
            x = rotate_left(x);
        }
        _ => unreachable!(),
    }
    x
}

fn ht<C: NodeMarker>(x: Option<&Node<C>>) -> u8 {
    x.as_ref().map_or(0, |x| x.ht)
}

fn rotate_left<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    C::push(&mut *x);
    let mut y = x.right.take().unwrap();
    C::push(&mut y);
    x.right = y.left.take();
    C::update(&mut *x);
    y.left = Some(x);
    C::update(&mut *y);
    y
}

fn rotate_right<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    C::push(&mut *x);
    let mut y = x.left.take().unwrap();
    C::push(&mut y);
    x.left = y.right.take();
    C::update(&mut *x);
    y.right = Some(x);
    C::update(&mut *y);
    y
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

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
}
