use super::core::{Node, NodeMarker};
use std::fmt::Debug;
use std::marker::PhantomData;

pub struct AvlLazySegtree<O: Op> {
    _node: Option<Node<Marker<O>>>,
}

pub trait Op {
    type Value: Clone + Debug; // TODO: remove

    type Operator: PartialEq + Eq + Debug; // TODO: remove

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
impl<O: Op> Debug for Data<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Data")
            .field("value", &self.value)
            .field("sum", &self.sum)
            .field("op", &self.op)
            .finish()
    }
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
