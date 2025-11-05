use super::node::{Node, NodeMarker};

pub struct ReversibleSegtree<O: Op> {
    _node: Option<Node<Marker<O>>>,
}

pub trait Op {
    type Value: Clone;

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}
struct Marker<O> {
    __marker: O,
}
#[allow(dead_code)]
struct Data<O: Op> {
    value: O::Value,
    sum: O::Value,
}
impl<O: Op> NodeMarker for Marker<O> {
    type Data = Data<O>;

    fn update(node: &mut Node<Self>) {
        let mut sum = node.data.value.clone();
        if let Some(l) = node.left.as_ref() {
            sum = O::mul(&l.data.sum, &sum);
        }
        if let Some(r) = node.right.as_ref() {
            sum = O::mul(&sum, &r.data.sum);
        }
        node.data.sum = sum;
    }

    fn push(_node: &mut Node<Self>) {}
}
