use std::hash::{Hash, Hasher};

use {
    super::{Nop, Op},
    std::{cmp::Ordering, marker::PhantomData},
};

#[derive(Clone)]
pub enum Root<T, O: Op<Value = T> = Nop<T>> {
    Nil(Nil<T>),
    Node(Node<T, O>),
}
#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
pub struct Nil<T>(pub T);
#[derive(Clone)]
pub struct Node<T, O: Op<Value = T>> {
    pub left: Box<Root<T, O>>,
    pub right: Box<Root<T, O>>,
    pub height: usize,
    pub len: usize,
    pub summary: O::Summary,
    pub __marker: PhantomData<fn(O) -> O>,
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
    }
}
impl<T, O: Op<Value = T>> Root<T, O> {
    pub fn len(&self) -> usize {
        match self {
            Self::Nil(_) => 1,
            Self::Node(node) => node.len,
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
    pub fn merge(lhs: Self, rhs: Self) -> Self {
        let h = lhs.height();
        match h.cmp(&rhs.height()) {
            Ordering::Equal => Self::Node(Node::new(Box::new(lhs), Box::new(rhs), h + 1)),
            Ordering::Less => rhs.merge_front(lhs),
            Ordering::Greater => lhs.merge_back(rhs),
        }
    }
    pub fn merge_front(self, rhs: Self) -> Self {
        let mut node = self.into_node().unwrap();
        node.left = Box::new(if node.left.height() == rhs.height() {
            Self::Node(Node::new(Box::new(rhs), node.left, node.height))
        } else {
            node.left.merge_front(rhs)
        });
        if node.height == node.left.node().unwrap().left.height() {
            let left = node.left.into_node().unwrap();
            node = Node::new(
                left.left,
                Box::new(Root::Node(Node::new(left.right, node.right, left.height))),
                left.height + 1,
            );
        } else {
            node.update();
        }
        Self::Node(node)
    }
    pub fn merge_back(self, rhs: Self) -> Self {
        let mut node = self.into_node().unwrap();
        node.right = Box::new(if node.right.height() == rhs.height() {
            Self::Node(Node::new(node.right, Box::new(rhs), node.height))
        } else {
            node.right.merge_back(rhs)
        });
        if node.height == node.right.height() {
            if node.height == node.left.height() {
                node.height += 1;
                node.update();
            } else {
                let right = node.right.into_node().unwrap();
                node = Node::new(
                    Box::new(Root::Node(Node::new(node.left, right.left, right.height))),
                    right.right,
                    right.height,
                );
            }
        } else {
            node.update();
        }
        Self::Node(node)
    }
    pub fn node(&self) -> Option<&Node<T, O>> {
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
    fn summary(&self) -> O::Summary {
        match self {
            Self::Nil(Nil(x)) => O::summarize(x),
            Self::Node(node) => node.summary,
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{Nil, Node, Root},
        test_case::test_case,
    };

    fn validate(root: &Root<()>) {
        if let Some(node) = root.node() {
            if let Some(left) = node.left.node() {
                assert!(left.height == node.height || left.height == node.height - 1);
                if let Some(ll) = left.left.node() {
                    assert_ne!(ll.height, node.height);
                }
            }
            if let Some(right) = node.right.node() {
                assert_eq!(right.height + 1, node.height);
            }
            validate(&node.left);
            validate(&node.right);
        }
    }

    fn to_structure_sring(root: &Root<()>) -> String {
        fn dfs(root: &Root<()>, s: &mut String) {
            s.push('(');
            match root {
                Root::Nil(_) => (),
                Root::Node(node) => {
                    dfs(&node.left, s);
                    s.push_str(&node.height.to_string());
                    s.push(',');
                    s.push_str(&node.len.to_string());
                    dfs(&node.right, s);
                }
            }
            s.push(')');
        }
        let mut s = String::new();
        dfs(root, &mut s);
        s
    }

    fn one_node() -> Root<()> {
        Root::Nil(Nil(()))
    }
    fn two_node() -> Root<()> {
        Root::Node(Node::new(Box::new(one_node()), Box::new(one_node()), 1))
    }
    fn three_node() -> Root<()> {
        Root::Node(Node::new(Box::new(two_node()), Box::new(one_node()), 1))
    }
    fn two_node_two_node() -> Root<()> {
        Root::Node(Node::new(Box::new(two_node()), Box::new(two_node()), 2))
    }
    fn two_node_three_node() -> Root<()> {
        Root::Node(Node::new(Box::new(two_node()), Box::new(three_node()), 2))
    }
    fn three_node_two_node() -> Root<()> {
        Root::Node(Node::new(Box::new(three_node()), Box::new(two_node()), 2))
    }
    fn three_node_three_node() -> Root<()> {
        Root::Node(Node::new(Box::new(three_node()), Box::new(three_node()), 2))
    }

    #[test_case(one_node() => "()".to_owned())]
    #[test_case(two_node() => "(()1,2())".to_owned())]
    #[test_case(three_node() => "((()1,2())1,3())".to_owned())]
    fn test_to_structure_string(root: Root<()>) -> String {
        to_structure_sring(&root)
    }

    #[test_case(one_node(), one_node() => to_structure_sring(&two_node()))]
    #[test_case(one_node(), two_node() => to_structure_sring(&three_node()))]
    #[test_case(one_node(), three_node() => to_structure_sring(&two_node_two_node()))]
    #[test_case(two_node(), one_node() => to_structure_sring(&three_node()))]
    #[test_case(two_node(), two_node() => to_structure_sring(&two_node_two_node()))]
    #[test_case(two_node(), three_node() => to_structure_sring(&two_node_three_node()))]
    #[test_case(three_node(), one_node() => to_structure_sring(&two_node_two_node()))]
    #[test_case(three_node(), two_node() => to_structure_sring(&three_node_two_node()))]
    #[test_case(three_node(), three_node() => to_structure_sring(&three_node_three_node()))]
    fn test_merge(lhs: Root<()>, rhs: Root<()>) -> String {
        let res = Root::merge(lhs, rhs);
        validate(&res);
        to_structure_sring(&res)
    }

    #[test_case(two_node(), 1 => [to_structure_sring(&one_node()), to_structure_sring(&one_node())])]
    #[test_case(three_node(), 1 => [to_structure_sring(&one_node()), to_structure_sring(&two_node())])]
    #[test_case(three_node(), 2 => [to_structure_sring(&two_node()), to_structure_sring(&one_node())])]
    #[test_case(two_node_two_node(), 1 => [to_structure_sring(&one_node()), to_structure_sring(&three_node())])]
    #[test_case(two_node_two_node(), 2 => [to_structure_sring(&two_node()), to_structure_sring(&two_node())])]
    #[test_case(two_node_two_node(), 3 => [to_structure_sring(&three_node()), to_structure_sring(&one_node())])]
    #[test_case(two_node_three_node(), 1 => [to_structure_sring(&one_node()), to_structure_sring(&two_node_two_node())])]
    #[test_case(two_node_three_node(), 2 => [to_structure_sring(&two_node()), to_structure_sring(&three_node())])]
    #[test_case(two_node_three_node(), 3 => [to_structure_sring(&three_node()), to_structure_sring(&two_node())])]
    #[test_case(two_node_three_node(), 4 => [to_structure_sring(&two_node_two_node()), to_structure_sring(&one_node())])]
    fn test_split(root: Root<()>, i: usize) -> [String; 2] {
        let [l, r] = &Root::split(root, i);
        validate(&l);
        validate(&r);
        [to_structure_sring(&l), to_structure_sring(&r)]
    }
}
