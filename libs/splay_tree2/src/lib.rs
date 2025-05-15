//! **WIP** A new implementation of a splay tree.
//!
//! # Overview
//!
//! | Operation | API | comments |
//! |-|-|-|
//! | Create | [`new`](SplayTree::new), [`default`](SplayTree::default)| $\emptyset$ |
//! | Insert | [`insert`](SplayTree::insert)| by binary searching by `f: FnMut(&Value<O>) -> Direction` |
//! | Remove | TBD | TBD |
//! | Find | TBD | TBD |
//! | Merge/Split | under discussion |  |
//! | Fold | [`fold_all`](SplayTree::fold_all)| TODO: implement general `fold` and replace by it |
//! | Debug | | `{ leaves: ..., internals: ...}` |
//!
//! TODO: testing

pub struct SplayTree<O: Op> {
    root: *mut Node<O>,
}
impl<O: Op> SplayTree<O> {
    pub fn new() -> Self {
        Self {
            root: std::ptr::null_mut(),
        }
    }

    pub fn fold_all(&self) -> O::InternalValue
    where
        O::InternalValue: Clone,
    {
        unsafe {
            if self.root.is_null() {
                return O::identity();
            }
            match (*self.root).value {
                Value::Leaf(ref value) => O::proj(value),
                Value::Internal(ref value) => value.clone(),
            }
        }
    }

    pub fn insert(&mut self, value: O::LeafValue, f: impl FnMut(&Value<O>) -> Direction) {
        unsafe {
            let new_leaf = Box::leak(Box::new(Node {
                parent: std::ptr::null_mut(),
                left: std::ptr::null_mut(),
                right: std::ptr::null_mut(),
                value: Value::Leaf(value),
            }));
            if self.root.is_null() {
                self.root = new_leaf;
            } else {
                let (existing_leaf, dir) = partition_point(self.root, f);
                let p = (*existing_leaf).parent;
                let leaves = match dir {
                    Direction::Left => [new_leaf, existing_leaf],
                    Direction::Right => [existing_leaf, new_leaf],
                };
                let new_node = Box::leak(Box::new(Node {
                    parent: p,
                    left: leaves[0],
                    right: leaves[1],
                    value: Value::Internal(op_values(&(*leaves[0]).value, &(*leaves[1]).value)),
                }));
                if !p.is_null() {
                    if (*p).left == existing_leaf {
                        (*p).left = new_node;
                    } else {
                        (*p).right = new_node;
                    }
                }
                (*leaves[0]).parent = new_node;
                (*leaves[1]).parent = new_node;
                splay(new_node);
                self.root = new_node;
            }
        }
    }
}

impl<O: Op> Default for SplayTree<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Op> std::fmt::Debug for SplayTree<O>
where
    O::LeafValue: std::fmt::Debug,
    O::InternalValue: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SplayTree")
            .field("leaves", &SplayTreeLeafFormatter { tree: self })
            .field("internals", &SplayTreeInternalFormatter { tree: self })
            .finish()
    }
}

struct SplayTreeLeafFormatter<'a, O: Op> {
    tree: &'a SplayTree<O>,
}
impl<'a, O: Op> std::fmt::Debug for SplayTreeLeafFormatter<'a, O>
where
    O: Op,
    O::LeafValue: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe fn find_leaves<O: Op>(
            node: *mut Node<O>,
            f: &mut std::fmt::DebugList,
        ) -> std::fmt::Result
        where
            O::LeafValue: std::fmt::Debug,
        {
            if node.is_null() {
                return Ok(());
            }
            find_leaves((*node).left, f)?;
            if let Value::Leaf(ref value) = (*node).value {
                f.entry(&value);
            }
            find_leaves((*node).right, f)
        }
        unsafe {
            let mut f = f.debug_list();
            find_leaves(self.tree.root, &mut f)?;
            f.finish()?;
            Ok(())
        }
    }
}

struct SplayTreeInternalFormatter<'a, O: Op> {
    tree: &'a SplayTree<O>,
}
impl<'a, O: Op> std::fmt::Debug for SplayTreeInternalFormatter<'a, O>
where
    O: Op,
    O::InternalValue: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe fn find_internals<O: Op>(
            node: *mut Node<O>,
            found_leaves: &mut usize,
            f: &mut std::fmt::DebugList,
        ) -> std::fmt::Result
        where
            O::InternalValue: std::fmt::Debug,
        {
            if node.is_null() {
                return Ok(());
            }
            match (*node).value {
                Value::Leaf(_) => *found_leaves += 1,
                Value::Internal(ref value) => {
                    let start = *found_leaves;
                    find_internals((*node).left, found_leaves, f)?;
                    find_internals((*node).right, found_leaves, f)?;
                    let end = *found_leaves;
                    f.entry(&(start..end, value));
                }
            }
            Ok(())
        }
        unsafe {
            let mut f = f.debug_list();
            find_internals(self.tree.root, &mut 0, &mut f)?;
            f.finish()?;
            Ok(())
        }
    }
}

pub trait Op: Sized {
    type InternalValue;
    type LeafValue;

    fn proj(x: &Self::LeafValue) -> Self::InternalValue;

    fn identity() -> Self::InternalValue;

    fn mul(lhs: &Self::InternalValue, rhs: &Self::InternalValue) -> Self::InternalValue;
}

fn op_values<O: Op>(lhs: &Value<O>, rhs: &Value<O>) -> O::InternalValue {
    match (lhs, rhs) {
        (Value::Leaf(l), Value::Leaf(r)) => O::mul(&O::proj(l), &O::proj(r)),
        (Value::Leaf(l), Value::Internal(r)) => O::mul(&O::proj(l), r),
        (Value::Internal(l), Value::Leaf(r)) => O::mul(l, &O::proj(r)),
        (Value::Internal(l), Value::Internal(r)) => O::mul(l, r),
    }
}

pub enum Value<O: Op> {
    Leaf(O::LeafValue),
    Internal(O::InternalValue),
}
impl<O: Op> std::fmt::Debug for Value<O>
where
    O::LeafValue: std::fmt::Debug,
    O::InternalValue: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Leaf(x) => f.debug_tuple("Leaf").field(x).finish(),
            Value::Internal(x) => f.debug_tuple("Internal").field(x).finish(),
        }
    }
}

struct Node<O: Op> {
    parent: *mut Self,
    left: *mut Self,
    right: *mut Self,
    value: Value<O>,
}
impl<O: Op> Node<O> {
    unsafe fn update(&mut self) {
        self.value = Value::Internal(op_values(&(*self.left).value, &(*self.right).value));
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Direction {
    Left,
    Right,
}

unsafe fn partition_point<O: Op>(
    mut x: *mut Node<O>,
    mut go: impl FnMut(&Value<O>) -> Direction,
) -> (*mut Node<O>, Direction) {
    loop {
        match go(&(*x).value) {
            Direction::Left => {
                if (*x).left.is_null() {
                    return (x, Direction::Left);
                }
                x = (*x).left;
            }
            Direction::Right => {
                if (*x).right.is_null() {
                    return (x, Direction::Right);
                }
                x = (*x).right;
            }
        }
    }
}

unsafe fn splay<O: Op>(x: *mut Node<O>) {
    let mut p = (*x).parent;
    while !p.is_null() {
        let g = (*p).parent;
        if g.is_null() {
            if (*p).left == x {
                rotate_right(p);
            } else {
                rotate_left(p);
            }
        } else if (*g).left == p {
            if (*p).left == x {
                rotate_right(g);
                rotate_right(p);
            } else {
                rotate_left(p);
                rotate_right(g);
            }
        } else {
            #[allow(clippy::collapsible_if)]
            if (*p).left == x {
                rotate_right(p);
                rotate_left(g);
            } else {
                rotate_left(g);
                rotate_left(p);
            }
        }
        p = (*x).parent;
    }
}

unsafe fn rotate_left<O: Op>(x: *mut Node<O>) {
    let p = (*x).parent;
    let y = (*x).right;
    let c = (*y).left;
    (*x).right = c;
    if !c.is_null() {
        (*c).parent = x;
    }
    (*y).left = x;
    (*x).parent = y;
    (*x).update();
    (*y).update();
    (*y).parent = p;
    if !p.is_null() {
        if (*p).left == x {
            (*p).left = y;
        } else {
            (*p).right = y;
        }
        (*p).update();
    }
}

unsafe fn rotate_right<O: Op>(x: *mut Node<O>) {
    let p = (*x).parent;
    let y = (*x).left;
    let c = (*y).right;
    (*x).left = c;
    if !c.is_null() {
        (*c).parent = x;
    }
    (*y).right = x;
    (*x).parent = y;
    (*x).update();
    (*y).update();
    (*y).parent = p;
    if !p.is_null() {
        if (*p).left == x {
            (*p).left = y;
        } else {
            (*p).right = y;
        }
        (*p).update();
    }
}
