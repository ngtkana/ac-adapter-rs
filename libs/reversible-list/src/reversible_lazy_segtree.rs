use super::node::{Node, NodeMarker};
use std::marker::PhantomData;

pub struct ReversibleLazySegtree<O: Op> {
    _node: Option<Node<Marker<O>>>,
}

pub trait Op {
    type Value: Clone;

    type Operator: PartialEq + Eq;

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    fn nop() -> Self::Operator;

    fn op(f: &Self::Operator, x: &Self::Value) -> Self::Value;

    fn compose(f: &Self::Operator, g: &Self::Operator) -> Self::Operator;
}
struct Marker<O> {
    __marker: PhantomData<O>,
}
#[allow(dead_code)]
struct Data<O: Op> {
    value: O::Value,
    sum: O::Value,
    op: O::Operator,
}
impl<O: Op> NodeMarker for Marker<O> {
    type Data = Data<O>;

    fn update(node: &mut Node<Self>) {
        let mut sum = node.data.value.clone();
        if let Some(l) = node.left.as_deref() {
            sum = O::mul(&l.data.sum, &sum);
        }
        if let Some(r) = node.right.as_deref() {
            sum = O::mul(&sum, &r.data.sum);
        }
        node.data.sum = sum;
    }

    fn push(node: &mut Node<Self>) {
        if node.data.op != O::nop() {
            let op = std::mem::replace(&mut node.data.op, O::nop());
            if let Some(l) = node.left.as_deref_mut() {
                l.data.sum = O::op(&op, &l.data.sum);
                l.data.value = O::op(&op, &l.data.value);
                l.data.op = O::compose(&op, &l.data.op);
            }
            if let Some(r) = node.right.as_deref_mut() {
                r.data.sum = O::op(&op, &r.data.sum);
                r.data.value = O::op(&op, &r.data.value);
                r.data.op = O::compose(&op, &r.data.op);
            }
        }
    }
}
