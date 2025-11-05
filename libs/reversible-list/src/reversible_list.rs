use super::node::{Node, NodeMarker};

pub struct ReversibleList {
    _node: Option<Node<ReversibleListContent>>,
}

struct ReversibleListContent;
impl NodeMarker for ReversibleListContent {
    type Data = ();

    fn update(_node: &mut Node<Self>) {}

    fn push(_node: &mut Node<Self>) {}
}
