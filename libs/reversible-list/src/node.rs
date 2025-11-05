#[allow(dead_code)]
pub(crate) struct Node<C: NodeMarker + ?Sized> {
    pub(crate) left: Option<Box<Self>>,
    pub(crate) right: Option<Box<Self>>,
    pub(crate) height: u8,
    pub(crate) len: usize,
    pub(crate) rev: bool,
    pub(crate) data: C::Data,
}
#[allow(dead_code)]
pub(crate) trait NodeMarker {
    type Data;

    fn update(node: &mut Node<Self>);

    fn push(node: &mut Node<Self>);
}
