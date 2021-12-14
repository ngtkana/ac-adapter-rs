use std::{fmt::Debug, mem::swap};

struct Node<T: Debug> {
    child: [Option<Box<Self>>; 2],
    value: T,
    len: usize,
    ht: u8,
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
