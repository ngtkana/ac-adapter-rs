use super::{NodeMarker, Ordering};

pub struct Node<C: NodeMarker + ?Sized> {
    pub left: Option<Box<Self>>,
    pub right: Option<Box<Self>>,
    pub ht: u8,
    pub len: usize,
    pub rev: bool,
    pub data: C::Data,
}

impl<C: NodeMarker> Node<C> {
    pub fn new(data: C::Data) -> Self {
        Self {
            left: None,
            right: None,
            ht: 1,
            len: 1,
            rev: false,
            data,
        }
    }
    pub fn update(&mut self) {
        self.len =
            self.left.as_ref().map_or(0, |l| l.len) + 1 + self.right.as_ref().map_or(0, |r| r.len);
        self.ht = 1 + self
            .left
            .as_ref()
            .map_or(0, |l| l.ht)
            .max(self.right.as_ref().map_or(0, |r| r.ht));
        C::update(self);
    }
    pub fn push(&mut self) {
        if self.rev {
            self.rev = false;
            std::mem::swap(&mut self.left, &mut self.right);
            if let Some(l) = self.left.as_mut() {
                l.rev ^= true;
            }
            if let Some(r) = self.right.as_mut() {
                r.rev ^= true;
            }
        }
        C::push(self);
    }
}

pub(crate) fn merge2<C: NodeMarker>(
    l: Option<Box<Node<C>>>,
    mut r: Option<Box<Node<C>>>,
) -> Option<Box<Node<C>>> {
    let Some(r) = r.take() else { return l };
    let (_, c, r) = split3(r, 0);
    Some(merge3(l, c, r))
}

pub(crate) fn merge3<C: NodeMarker>(
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

pub(crate) fn split2<C: NodeMarker>(
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

pub(crate) fn ht<C: NodeMarker>(x: Option<&Node<C>>) -> u8 {
    x.as_ref().map_or(0, |x| x.ht)
}

pub(crate) fn rotate_left<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    x.push();
    let mut y = x.right.take().unwrap();
    y.push();
    x.right = y.left.take();
    x.update();
    y.left = Some(x);
    y.update();
    y
}

pub(crate) fn rotate_right<C: NodeMarker>(mut x: Box<Node<C>>) -> Box<Node<C>> {
    x.push();
    let mut y = x.left.take().unwrap();
    y.push();
    x.left = y.right.take();
    x.update();
    y.right = Some(x);
    y.update();
    y
}
