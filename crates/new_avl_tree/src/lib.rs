use std::{fmt::Debug, mem::swap};

pub struct AvlTree<T> {
    root: Option<Box<Node<T>>>,
}
impl<T: Debug> AvlTree<T> {
    pub fn new() -> Self {
        Self::default()
    }
    // TODO: iterator
    pub fn collect_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        fn collect_vec<T: Debug + Clone>(node: &Node<T>, out: &mut Vec<T>) {
            if let Some(c) = node.child[0].as_ref() {
                collect_vec(c, out);
            }
            out.push(node.value.clone());
            if let Some(c) = node.child[1].as_ref() {
                collect_vec(c, out);
            }
        }
        let mut out = Vec::new();
        if let Some(node) = self.root.as_ref() {
            collect_vec(node, &mut out);
        }
        out
    }
}

impl<T: Debug> Default for AvlTree<T> {
    fn default() -> Self {
        Self { root: None }
    }
}
// TODO: not using vector
impl<T: Debug> FromIterator<T> for AvlTree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        fn from_slice_of_nodes<T: Debug>(
            nodes: &mut [Option<Box<Node<T>>>],
        ) -> Option<Box<Node<T>>> {
            if nodes.is_empty() {
                None
            } else {
                let i = nodes.len() / 2;
                Some(merge_with_root(
                    [
                        from_slice_of_nodes(&mut nodes[..i]),
                        from_slice_of_nodes(&mut nodes[i + 1..]),
                    ],
                    nodes[i].take().unwrap(),
                ))
            }
        }
        Self {
            root: from_slice_of_nodes(
                iter.into_iter()
                    .map(new)
                    .map(Some)
                    .collect::<Vec<_>>()
                    .as_mut_slice(),
            ),
        }
    }
}

struct Node<T> {
    child: [Option<Box<Self>>; 2],
    value: T,
    len: usize,
    ht: u8,
}
fn new<T: Debug>(value: T) -> Box<Node<T>> {
    Box::new(Node {
        child: [None, None],
        value,
        len: 1,
        ht: 1,
    })
}
impl<T: Debug> Node<T> {
    fn update(&mut self) {
        self.len = len(&self.child[0]) + 1 + len(&self.child[1]);
        self.ht = 1 + ht(&self.child[0]).max(ht(&self.child[1]));
    }
    fn diff(&self, e: usize) -> isize {
        ht(&self.child[e]) as isize - ht(&self.child[1 - e]) as isize
    }
}
fn len<T: Debug>(tree: &Option<Box<Node<T>>>) -> usize {
    tree.as_ref().map_or(0, |node| node.len)
}
fn ht<T: Debug>(tree: &Option<Box<Node<T>>>) -> u8 {
    tree.as_ref().map_or(0, |node| node.ht)
}
fn balance<T: Debug>(tree: &mut Box<Node<T>>) {
    fn rotate<T: Debug>(tree: &mut Box<Node<T>>, e: usize) {
        let mut x = tree.child[e].take().unwrap();
        let y = x.child[1 - e].take();
        swap(tree, &mut x);
        x.child[e] = y;
        x.update();
        tree.child[1 - e] = Some(x);
        tree.update();
    }
    tree.update();
    for e in 0..2 {
        if 1 < tree.diff(e) {
            if 0 < tree.child[e].as_ref().unwrap().diff(1 - e) {
                rotate(tree.child[e].as_mut().unwrap(), 1 - e);
            }
            rotate(tree, e);
            break;
        }
    }
}
fn merge_with_root<T: Debug>(
    mut sub: [Option<Box<Node<T>>>; 2],
    mut center: Box<Node<T>>,
) -> Box<Node<T>> {
    for e in 0..2 {
        if ht(&sub[e]) > ht(&sub[1 - e]) {
            let mut root = sub[e].take().unwrap();
            let mut tmp = [None, None];
            tmp[e] = root.child[1 - e].take();
            tmp[1 - e] = sub[1 - e].take();
            root.child[1 - e] = Some(merge_with_root(tmp, center));
            root.update();
            return root;
        }
    }
    center.child = sub;
    center.update();
    center
}
fn split_delete_by<T: Debug>(
    mut root: Box<Node<T>>,
    mut is_right: impl FnMut(&Node<T>) -> usize,
) -> ([Option<Box<Node<T>>>; 2], Box<Node<T>>, usize) {
    let e = is_right(&*root);
    if root.child[1 - e].is_none() {
        let mut sub = [None, None];
        sub[e] = root.child[e].take();
        (sub, root, e)
    } else {
        let (mut sub, center, res) = split_delete_by(root.child[1 - e].take().unwrap(), is_right);
        let mut tmp = [None, None];
        tmp[e] = root.child[e].take();
        tmp[1 - e] = sub[e].take();
        sub[e] = Some(merge_with_root(tmp, root));
        (sub, center, res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_iter() {
        for n in 0..=10 {
            let result = (0..n).collect::<AvlTree<_>>().collect_vec();
            let expected = (0..n).collect::<Vec<_>>();
            assert_eq!(result, expected);
        }
    }
}
