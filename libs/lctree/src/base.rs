pub trait OpBase {
    type FrontValue: Clone;
    type InternalValue: Clone;

    fn identity() -> Self::InternalValue;

    fn mul(lhs: &Self::InternalValue, rhs: &Self::InternalValue) -> Self::InternalValue;

    fn into_front(value: Self::InternalValue) -> Self::FrontValue;

    fn from_front(value: Self::FrontValue) -> Self::InternalValue;

    fn rev(value: &mut Self::InternalValue);
}

pub struct LinkCutTreeBase<O: OpBase> {
    pub nodes: Vec<Node<O>>,
}
impl<O: OpBase> LinkCutTreeBase<O> {
    pub fn new(n: usize) -> Self {
        Self {
            nodes: (0..n)
                .map(|id| Node {
                    id,
                    parent: std::ptr::null_mut(),
                    left: std::ptr::null_mut(),
                    right: std::ptr::null_mut(),
                    rev: false,
                    value: O::identity(),
                    acc: O::identity(),
                })
                .collect(),
        }
    }

    pub fn from_values(values: impl IntoIterator<Item = O::FrontValue>) -> Self {
        Self {
            nodes: values
                .into_iter()
                .map(O::from_front)
                .enumerate()
                .map(|(id, value)| Node {
                    id,
                    parent: std::ptr::null_mut(),
                    left: std::ptr::null_mut(),
                    right: std::ptr::null_mut(),
                    rev: false,
                    value: value.clone(),
                    acc: value,
                })
                .collect(),
        }
    }

    pub fn link(&mut self, p: usize, c: usize) {
        unsafe {
            let c = (&mut self.nodes[c]) as *mut Node<O>;
            let p = (&mut self.nodes[p]) as *mut Node<O>;
            expose(c);
            assert!((*c).left.is_null(), "c = {} is not a root", (*c).id);
            expose(p);
            assert!(
                (*c).parent.is_null(),
                "c = {} and p = {} are already connected",
                (*c).id,
                (*p).id
            );
            (*c).parent = p;
            (*p).right = c;
            update(p);
        }
    }

    pub fn undirected_link(&mut self, i: usize, j: usize) -> bool {
        if self.undirected_is_connected(i, j) {
            return false;
        }
        self.evert(j);
        self.link(i, j);
        true
    }

    pub fn cut(&mut self, x: usize) -> Option<usize> {
        unsafe {
            let x = (&mut self.nodes[x]) as *mut _;
            expose(x);
            let p = (*x).left;
            (*x).left = std::ptr::null_mut();
            let ans = p.as_ref().map(|p| p.id);
            if !p.is_null() {
                (*p).parent = std::ptr::null_mut();
            }
            update(x);
            ans
        }
    }

    pub fn undirected_cut(&mut self, i: usize, j: usize) -> bool {
        if !self.undirected_has_edge(i, j) {
            return false;
        }
        self.evert(i);
        self.cut(j);
        true
    }

    pub fn evert(&mut self, x: usize) {
        unsafe {
            let x = (&mut self.nodes[x]) as *mut _;
            expose(x);
            rev(x);
            push(x);
        }
    }

    pub fn undirected_has_edge(&mut self, x: usize, y: usize) -> bool {
        self.parent(x) == Some(y) || self.parent(y) == Some(x)
    }

    pub fn undirected_is_connected(&mut self, x: usize, y: usize) -> bool {
        if x == y {
            return true;
        }
        unsafe {
            let x = (&mut self.nodes[x]) as *mut _;
            let y = (&mut self.nodes[y]) as *mut _;
            expose(x);
            expose(y);
            !(*x).parent.is_null()
        }
    }

    pub fn lca(&mut self, x: usize, y: usize) -> Option<usize> {
        if x == y {
            return Some(x);
        }
        unsafe {
            let x = (&mut self.nodes[x]) as *mut _;
            let y = (&mut self.nodes[y]) as *mut _;
            expose(x);
            let lca = expose(y);
            if (*x).parent.is_null() {
                None
            } else {
                Some((*lca).id)
            }
        }
    }

    pub fn set(&mut self, x: usize, mut f: impl FnMut(O::FrontValue) -> O::FrontValue) {
        unsafe {
            let x = (&mut self.nodes[x]) as *mut Node<O>;
            expose(x);
            (*x).value = O::from_front(f(O::into_front((*x).value.clone())));
            update(x);
        }
    }

    pub fn fold(&mut self, x: usize) -> O::FrontValue {
        unsafe {
            let x = (&mut self.nodes[x]) as *mut Node<O>;
            expose(x);
            O::into_front((*x).acc.clone())
        }
    }

    pub fn undirected_fold(&mut self, i: usize, j: usize) -> Option<O::FrontValue> {
        if !self.undirected_is_connected(i, j) {
            return None;
        }
        self.evert(i);
        Some(self.fold(j))
    }

    pub fn parent(&mut self, x: usize) -> Option<usize> {
        unsafe {
            let x = (&mut self.nodes[x]) as *mut Node<O>;
            expose(x);
            let mut p = (*x).left.as_mut()?;
            while let Some(next) = (*p).right.as_mut() {
                p = next;
            }
            splay(p);
            Some((*p).id)
        }
    }
}

#[derive(Clone, Copy)]
pub struct Node<O: OpBase> {
    pub id: usize,
    pub parent: *mut Self,
    pub left: *mut Self,
    pub right: *mut Self,
    pub rev: bool,
    pub value: O::InternalValue,
    pub acc: O::InternalValue,
}

unsafe fn is_splay_root<O: OpBase>(x: *mut Node<O>) -> bool {
    let x = &*x;
    let p = match x.parent.as_ref() {
        Some(p) => p,
        None => return true,
    };
    !std::ptr::eq(x, p.left) && !std::ptr::eq(x, p.right)
}

unsafe fn push<O: OpBase>(x: *mut Node<O>) {
    let x = &mut *x;
    if x.rev {
        if let Some(l) = x.left.as_mut() {
            rev(l);
        }
        if let Some(r) = x.right.as_mut() {
            rev(r);
        }
        x.rev = false;
    }
}

unsafe fn update<O: OpBase>(x: *mut Node<O>) {
    let x = &mut *x;
    x.acc = x.value.clone();
    if !x.left.is_null() {
        x.acc = O::mul(&(*x.left).acc, &x.acc);
    }
    if !x.right.is_null() {
        x.acc = O::mul(&x.acc, &(*x.right).acc);
    }
}

unsafe fn rev<O: OpBase>(x: *mut Node<O>) {
    let x = &mut *x;
    std::mem::swap(&mut x.left, &mut x.right);
    O::rev(&mut x.acc);
    x.rev ^= true;
}

unsafe fn expose<O: OpBase>(x: *mut Node<O>) -> *mut Node<O> {
    let mut last = std::ptr::null_mut();
    let mut current = x;
    while !current.is_null() {
        splay(current);
        (*current).right = last;
        update(current);
        last = current;
        current = (*current).parent;
    }
    splay(x);
    last
}

unsafe fn splay<O: OpBase>(x: *mut Node<O>) {
    let x = &mut *x;
    push(x);
    while !is_splay_root(x) {
        let p = &mut *x.parent;
        if is_splay_root(p) {
            push(p);
            push(x);
            if std::ptr::eq((*p).left, x) {
                rotate_right(p);
            } else {
                rotate_left(p);
            }
        } else {
            let g = &mut *p.parent;
            push(g);
            push(p);
            push(x);
            if std::ptr::eq((*p).left, x) {
                if std::ptr::eq((*g).left, p) {
                    rotate_right(g);
                    rotate_right(p);
                } else {
                    rotate_right(p);
                    rotate_left(g);
                }
            } else {
                if std::ptr::eq((*g).left, p) {
                    rotate_left(p);
                    rotate_right(g);
                } else {
                    rotate_left(g);
                    rotate_left(p);
                }
            }
        }
    }
}

unsafe fn rotate_left<O: OpBase>(l: *mut Node<O>) {
    let l = &mut *l;
    let r = &mut *l.right;
    let p = l.parent;
    let c = r.left;
    l.right = c;
    if !c.is_null() {
        (*c).parent = l;
    }
    r.left = l;
    l.parent = r;
    r.parent = p;
    update(l);
    update(r);
    if !p.is_null() {
        if std::ptr::eq((*p).left, l) {
            (*p).left = r;
        } else if std::ptr::eq((*p).right, l) {
            (*p).right = r;
        }
        update(&mut *p);
    }
}

unsafe fn rotate_right<O: OpBase>(r: *mut Node<O>) {
    let r = &mut *r;
    let l = &mut *r.left;
    let p = r.parent;
    let c = l.right;
    r.left = c;
    if !c.is_null() {
        (*c).parent = r;
    }
    l.right = r;
    r.parent = l;
    l.parent = p;
    update(r);
    update(l);
    if !p.is_null() {
        if std::ptr::eq((*p).left, r) {
            (*p).left = l;
        } else if std::ptr::eq((*p).right, r) {
            (*p).right = l;
        }
        update(&mut *p);
    }
}
