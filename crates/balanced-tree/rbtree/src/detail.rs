use {
    super::{Nop, Op},
    std::{
        cmp::Ordering,
        hash::{Hash, Hasher},
        marker::PhantomData,
        mem::swap,
    },
};

pub enum Root<T, O: Op<Value = T> = Nop<T>> {
    Nil(Nil<T>),
    Node(Node<T, O>),
}
#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
pub struct Nil<T>(pub T);
pub struct Node<T, O: Op<Value = T>> {
    pub left: Box<Root<T, O>>,
    pub right: Box<Root<T, O>>,
    pub height: usize,
    pub len: usize,
    pub summary: O::Summary,
    pub __marker: PhantomData<fn(O) -> O>,
}
impl<T, O: Op<Value = T>> Node<T, O> {
    pub fn new(lhs: Box<Root<T, O>>, rhs: Box<Root<T, O>>, height: usize) -> Self {
        Self {
            len: lhs.len() + rhs.len(),
            summary: O::op(lhs.summary(), rhs.summary()),
            height,
            left: lhs,
            right: rhs,
            __marker: PhantomData,
        }
    }
    pub fn update(&mut self) {
        self.len = self.left.len() + self.right.len();
        self.summary = O::op(self.left.summary(), self.right.summary());
    }
}
impl<T, O: Op<Value = T>> Root<T, O> {
    pub fn len(&self) -> usize {
        match self {
            Self::Nil(_) => 1,
            Self::Node(node) => node.len,
        }
    }
    pub fn fold(&self, start: usize, end: usize) -> O::Summary {
        debug_assert!(start < end && end <= self.len());
        match self {
            Self::Nil(Nil(x)) => O::summarize(x),
            Self::Node(node) => {
                let lsize = node.left.len();
                if start == 0 && end == self.len() {
                    node.summary.clone()
                } else if end <= lsize {
                    node.left.fold(start, end)
                } else if lsize <= start {
                    node.right.fold(start - lsize, end - lsize)
                } else {
                    O::op(
                        node.left.fold(start, lsize),
                        node.right.fold(0, end - lsize),
                    )
                }
            }
        }
    }
    pub fn split(self, i: usize) -> [Self; 2] {
        let node = self.into_node().unwrap();
        let left_len = node.left.len();
        match i.cmp(&left_len) {
            Ordering::Equal => [*node.left, *node.right],
            Ordering::Less => {
                let [l, r] = node.left.split(i);
                [l, Self::merge(r, *node.right)]
            }
            Ordering::Greater => {
                let [l, r] = node.right.split(i - left_len);
                [Self::merge(*node.left, l), r]
            }
        }
    }
    pub fn singleton(x: T) -> Self {
        Self::Nil(Nil(x))
    }
    pub fn merge(mut lhs: Self, mut rhs: Self) -> Self {
        let h = lhs.height();
        match h.cmp(&rhs.height()) {
            Ordering::Equal => Self::Node(Node::new(Box::new(lhs), Box::new(rhs), h + 1)),
            Ordering::Less => {
                rhs.merge_front(lhs);
                rhs
            }
            Ordering::Greater => {
                lhs.merge_back(rhs);
                lhs
            }
        }
    }
    pub fn merge_front(&mut self, other: Self) {
        let h = self.height();
        if other.height() == self.node().unwrap().left.height() {
            let Node { left, .. } = self.node_mut().unwrap();
            replace_with(left, |left| {
                Box::new(Self::Node(Node::new(Box::new(other), left, h)))
            });
        } else {
            self.node_mut().unwrap().left.merge_front(other);
        }
        if self.node().unwrap().left.node().unwrap().left.height() == h {
            if self.node().unwrap().right.height() == h {
                self.node_mut().unwrap().height += 1;
            } else {
                let Node { left, right, .. } = self.node_mut().unwrap();
                swap(left, right);
                let l = left;
                let Node { left, right, .. } = right.node_mut().unwrap();
                swap(l, left);
                swap(left, right);
                self.node_mut().unwrap().right.node_mut().unwrap().update();
            }
        }
        self.node_mut().unwrap().update();
    }
    pub fn merge_back(&mut self, other: Self) {
        let h = self.height();
        if other.height() == self.node().unwrap().right.height() {
            let Node { right, .. } = self.node_mut().unwrap();
            replace_with(right, |right| {
                Box::new(Self::Node(Node::new(right, Box::new(other), h)))
            });
        } else {
            self.node_mut().unwrap().right.merge_back(other);
        }
        if self.node().unwrap().right.node().unwrap().right.height() == h {
            if self.node().unwrap().left.height() == h {
                self.node_mut().unwrap().height += 1;
            } else {
                let Node { left, right, .. } = self.node_mut().unwrap();
                swap(left, right);
                let r = right;
                let Node { left, right, .. } = left.node_mut().unwrap();
                swap(right, r);
                swap(left, right);
                self.node_mut().unwrap().left.node_mut().unwrap().update();
            }
        }
        self.node_mut().unwrap().update();
    }
    pub fn node(&self) -> Option<&Node<T, O>> {
        match self {
            Self::Nil(_) => None,
            Self::Node(node) => Some(node),
        }
    }
    pub fn node_mut(&mut self) -> Option<&mut Node<T, O>> {
        match self {
            Self::Nil(_) => None,
            Self::Node(node) => Some(node),
        }
    }
    fn into_node(self) -> Option<Node<T, O>> {
        match self {
            Self::Nil(_) => None,
            Self::Node(node) => Some(node),
        }
    }
    fn height(&self) -> usize {
        match self {
            Self::Nil(_) => 0,
            Self::Node(node) => node.height,
        }
    }
    pub fn summary(&self) -> O::Summary {
        match self {
            Self::Nil(Nil(x)) => O::summarize(x),
            Self::Node(node) => node.summary.clone(),
        }
    }
}

fn replace_with<T, F: FnOnce(T) -> T>(dest: &mut T, f: F) {
    unsafe { std::ptr::write(dest, f(std::ptr::read(dest))) }
}

impl<T: Clone, O: Op<Value = T>> Clone for Root<T, O>
where
    O::Summary: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::Nil(x) => Self::Nil(x.clone()),
            Self::Node(x) => Self::Node(x.clone()),
        }
    }
}
impl<T: Clone, O: Op<Value = T>> Clone for Node<T, O>
where
    O::Summary: Clone,
{
    fn clone(&self) -> Self {
        Self {
            left: self.left.clone(),
            right: self.right.clone(),
            height: self.height,
            len: self.len,
            summary: self.summary.clone(),
            __marker: self.__marker,
        }
    }
}
impl<T: PartialEq, O: Op<Value = T>> PartialEq for Root<T, O>
where
    O::Summary: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match [self, other] {
            [Self::Nil(x), Self::Nil(y)] => x.eq(y),
            [Self::Node(x), Self::Node(y)] => x.eq(y),
            _ => false,
        }
    }
}
impl<T: PartialEq, O: Op<Value = T>> PartialEq for Node<T, O>
where
    O::Summary: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.left.eq(&other.left)
            && self.right.eq(&other.right)
            && self.height.eq(&other.height)
            && self.len.eq(&other.len)
            && self.summary.eq(&other.summary)
    }
}
impl<T: Hash, O: Op<Value = T>> Hash for Root<T, O>
where
    O::Summary: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Nil(x) => x.hash(state),
            Self::Node(x) => x.hash(state),
        }
    }
}
impl<T: Hash, O: Op<Value = T>> Hash for Node<T, O>
where
    O::Summary: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.left.hash(state);
        self.right.hash(state);
        self.height.hash(state);
        self.len.hash(state);
        self.summary.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{Nil, Node, Op, Root},
        test_case::test_case,
    };

    fn to_structure_sring<T, O: Op<Value = T>>(root: &Root<T, O>) -> String {
        let mut s = String::new();
        to_structure_sring_dfs(root, &mut s);
        s
    }
    fn to_structure_sring_dfs<T, O: Op<Value = T>>(root: &Root<T, O>, s: &mut String) {
        s.push('(');
        match root {
            Root::Nil(_) => (),
            Root::Node(node) => {
                to_structure_sring_dfs(&node.left, s);
                s.push_str(&node.height.to_string());
                s.push(',');
                s.push_str(&node.len.to_string());
                to_structure_sring_dfs(&node.right, s);
            }
        }
        s.push(')');
    }

    fn validate(root: &Root<()>) {
        if let Some(node) = root.node() {
            let h = node.height;
            assert_eq!(node.len, node.left.len() + node.right.len());
            for x in node.left.node().into_iter().chain(node.right.node()) {
                assert!(x.height == node.height || x.height == node.height - 1);
                for y in x.left.node().into_iter().chain(x.right.node()) {
                    assert_ne!(y.height, h);
                }
            }
            validate(&node.left);
            validate(&node.right);
        }
    }

    fn nil() -> Root<()> {
        Root::Nil(Nil(()))
    }
    fn n2(x: impl Fn() -> Root<()>, y: impl Fn() -> Root<()>, h: usize) -> impl Fn() -> Root<()> {
        move || Root::Node(Node::new(Box::new(x()), Box::new(y()), h))
    }
    fn l3(
        x: impl Fn() -> Root<()>,
        y: impl Fn() -> Root<()>,
        z: impl Fn() -> Root<()>,
        h: usize,
    ) -> impl Fn() -> Root<()> {
        n2(n2(x, y, h), z, h)
    }
    fn r3(
        x: impl Fn() -> Root<()>,
        y: impl Fn() -> Root<()>,
        z: impl Fn() -> Root<()>,
        h: usize,
    ) -> impl Fn() -> Root<()> {
        n2(x, n2(y, z, h), h)
    }
    fn n4(
        x: impl Fn() -> Root<()>,
        y: impl Fn() -> Root<()>,
        z: impl Fn() -> Root<()>,
        w: impl Fn() -> Root<()>,
        height: usize,
    ) -> impl Fn() -> Root<()> {
        n2(n2(x, y, height), n2(z, w, height), height)
    }
    fn n2nil() -> Root<()> {
        n2(nil, nil, 1)()
    }
    fn l3nil() -> Root<()> {
        l3(nil, nil, nil, 1)()
    }
    fn r3nil() -> Root<()> {
        r3(nil, nil, nil, 1)()
    }
    fn n4nil() -> Root<()> {
        n4(nil, nil, nil, nil, 1)()
    }

    #[test_case(nil => "()".to_owned())]
    #[test_case(n2nil => "(()1,2())".to_owned())]
    #[test_case(l3nil => "((()1,2())1,3())".to_owned())]
    #[test_case(r3nil => "(()1,3(()1,2()))".to_owned())]
    #[test_case(n4nil => "((()1,2())1,4(()1,2()))".to_owned())]
    fn test_to_structure_string(x: impl Fn() -> Root<()>) -> String {
        to_structure_sring(&x())
    }

    #[test_case(nil, nil => to_structure_sring(&n2nil()))]
    #[test_case(nil, n2nil => to_structure_sring(&l3nil()))]
    #[test_case(nil, l3nil => to_structure_sring(&n4nil()))]
    #[test_case(nil, r3nil => to_structure_sring(&n4nil()))]
    #[test_case(n2nil, n2nil => to_structure_sring(&n2(n2nil, n2nil, 2)()))]
    #[test_case(n2nil, l3nil => to_structure_sring(&n2(n2nil, l3nil, 2)()))]
    #[test_case(n2nil, r3nil => to_structure_sring(&n2(n2nil, r3nil, 2)()))]
    #[test_case(n2nil, n2(n2nil, n2nil, 2) => to_structure_sring(&l3(n2nil, n2nil, n2nil, 2)()))]
    #[test_case(n2nil, l3(n2nil, n2nil, n2nil, 2) => to_structure_sring(&n4(n2nil, n2nil, n2nil, n2nil, 2)()))]
    #[test_case(n2nil, r3(n2nil, n2nil, n2nil, 2) => to_structure_sring(&n4(n2nil, n2nil, n2nil, n2nil, 2)()))]
    #[test_case(n2nil, n4(n2nil, n2nil, n2nil, n2nil, 2) => to_structure_sring(&n2(l3(n2nil, n2nil, n2nil, 2), n2(n2nil, n2nil, 2), 3)()))]
    fn test_merge(lhs: impl Fn() -> Root<()>, rhs: impl Fn() -> Root<()>) -> String {
        let root = Root::merge(lhs(), rhs());
        let res = to_structure_sring(&root);
        println!("{}", res);
        validate(&root);
        res
    }
}
