use std::cmp::Ordering;

// Non-empty RB-tree
#[derive(Clone, Debug, Hash, PartialEq)]
enum Root<T> {
    Nil(Nil<T>),
    Node(Node<T>),
}
#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
struct Nil<T>(T);

#[derive(Clone, Debug, Hash, PartialEq)]
struct Node<T> {
    left: Box<Root<T>>,
    right: Box<Root<T>>,
    height: usize,
    len: usize,
}

impl<T> Node<T> {
    fn new(lhs: Box<Root<T>>, rhs: Box<Root<T>>, height: usize) -> Self {
        Self {
            len: lhs.len() + rhs.len(),
            height,
            left: lhs,
            right: rhs,
        }
    }
    fn update(&mut self) {
        self.len = self.left.len() + self.right.len();
    }
}

impl<T> Root<T> {
    fn split(self, i: usize) -> [Self; 2] {
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
    fn merge(lhs: Self, rhs: Self) -> Self {
        let h = lhs.height();
        match h.cmp(&rhs.height()) {
            Ordering::Equal => Self::Node(Node::new(Box::new(lhs), Box::new(rhs), h + 1)),
            Ordering::Less => rhs.merge_front(lhs),
            Ordering::Greater => lhs.merge_back(rhs),
        }
    }
    fn merge_front(self, rhs: Self) -> Self {
        let mut node = self.into_node().unwrap();
        node.left = Box::new(if node.left.height() == rhs.height() {
            Self::Node(Node::new(Box::new(rhs), node.left, node.height))
        } else {
            node.left.merge_front(rhs)
        });
        if node.height == node.left.node().unwrap().left.height() {
            let Node {
                left: l,
                right: r,
                height,
                len: _,
            } = node.left.into_node().unwrap();
            node = Node::new(
                l,
                Box::new(Root::Node(Node::new(r, node.right, height))),
                height + 1,
            );
        } else {
            node.update();
        }
        Self::Node(node)
    }
    fn merge_back(self, rhs: Self) -> Self {
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
                let Node {
                    left: l,
                    right: r,
                    height,
                    len: _,
                } = node.right.into_node().unwrap();
                node = Node::new(
                    Box::new(Root::Node(Node::new(node.left, l, height))),
                    r,
                    height,
                );
            }
        } else {
            node.update();
        }
        Self::Node(node)
    }
    fn node(&self) -> Option<&Node<T>> {
        match self {
            Self::Nil(_) => None,
            Self::Node(node) => Some(node),
        }
    }
    fn into_node(self) -> Option<Node<T>> {
        match self {
            Self::Nil(_) => None,
            Self::Node(node) => Some(node),
        }
    }
    fn len(&self) -> usize {
        match self {
            Self::Nil(_) => 1,
            Self::Node(node) => node.len,
        }
    }
    fn height(&self) -> usize {
        match self {
            Self::Nil(_) => 0,
            Self::Node(node) => node.height,
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
