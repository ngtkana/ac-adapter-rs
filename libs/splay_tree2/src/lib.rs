//! **WIP** A new implementation of a splay tree.
//!
//! # Overview
//!
//! | Operation | API | comments |
//! |-|-|-|
//! | Create | [`new`](SplayTree::new), [`default`](SplayTree::default)| $\emptyset$ |
//! | Insert | [`insert`](SplayTree::insert)| by binary searching by key. requires [`RightMin`] |
//! | Remove | TBD | TBD |
//! | Find | TBD | TBD |
//! | Merge/Split | under discussion |  |
//! | Fold | [`fold_all`](SplayTree::fold_all)| TODO: implement general `fold` and replace by it |
//! | Debug | | `{ leaves: ..., internals: ...}` |
//!
//! TODO: testing

use std::ptr;

pub struct SplayTree<O: Op> {
    root: *mut Node<O>,
}
impl<O: Op> SplayTree<O> {
    pub fn new() -> Self {
        Self {
            root: ptr::null_mut(),
        }
    }

    pub fn fold_all(&self) -> Option<&Value<O>> {
        unsafe { Some(&self.root.as_ref()?.value) }
    }
}

impl<O: RightMin> SplayTree<O>
where
    O::LeafValue: Ord,
{
    pub fn insert(&mut self, value: O::LeafValue) {
        unsafe {
            if self.root.is_null() {
                self.root = alloc_from_leaf_value(value);
            } else {
                let (existing_leaf, dir) = lower_bound(self.root, &value);
                self.root = insert_leaf_beside_a_leaf(existing_leaf, dir, value);
            }
        }
    }

    pub fn contains(&mut self, key: &O::LeafValue) -> bool {
        unsafe {
            if self.root.is_null() {
                return false;
            }
            let (leaf, _) = lower_bound(self.root, key);
            self.root = splay(leaf);
            let Value::Leaf(ref leaf_value) = (*leaf).value else {
                panic!("leaf is not a leaf");
            };
            leaf_value == key
        }
    }
}

impl<O: LeftLen> SplayTree<O> {
    pub fn remove_at(&mut self, index: usize) -> O::LeafValue {
        unsafe {
            let leaf = get_by_index(self.root, index);
            let (new_root, leaf_value) = remove_leaf(leaf);
            self.root = new_root;
            leaf_value
        }
    }
}

impl<O: Op> Default for SplayTree<O> {
    fn default() -> Self {
        Self::new()
    }
}

pub trait Op: Sized {
    type InternalValue;
    type LeafValue;

    fn proj(x: &Self::LeafValue) -> Self::InternalValue;

    fn mul(lhs: &Self::InternalValue, rhs: &Self::InternalValue) -> Self::InternalValue;
}

pub trait LeftLen: Op {
    fn left_len(internal_value: &Self::InternalValue) -> usize;
}

pub trait RightMin: Op
where
    <Self as Op>::LeafValue: Ord,
{
    fn right_min(internal_value: &Self::InternalValue) -> &Self::LeafValue;
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
    fn from_value(value: Value<O>) -> Self {
        Self {
            parent: ptr::null_mut(),
            left: ptr::null_mut(),
            right: ptr::null_mut(),
            value,
        }
    }
    unsafe fn update(&mut self) {
        fn op_values<O: Op>(lhs: &Value<O>, rhs: &Value<O>) -> O::InternalValue {
            match (lhs, rhs) {
                (Value::Leaf(l), Value::Leaf(r)) => O::mul(&O::proj(l), &O::proj(r)),
                (Value::Leaf(l), Value::Internal(r)) => O::mul(&O::proj(l), r),
                (Value::Internal(l), Value::Leaf(r)) => O::mul(l, &O::proj(r)),
                (Value::Internal(l), Value::Internal(r)) => O::mul(l, r),
            }
        }
        self.value = Value::Internal(op_values(&(*self.left).value, &(*self.right).value));
    }
}

fn alloc_from_node<O: Op>(node: Node<O>) -> *mut Node<O> {
    Box::into_raw(Box::new(node))
}
fn alloc_from_value<O: Op>(value: Value<O>) -> *mut Node<O> {
    alloc_from_node(Node::from_value(value))
}
fn alloc_from_leaf_value<O: Op>(leaf_value: O::LeafValue) -> *mut Node<O> {
    alloc_from_value(Value::Leaf(leaf_value))
}

#[derive(Clone, Copy, Debug)]
pub enum Direction {
    Left,
    Right,
}

unsafe fn insert_leaf_beside_a_leaf<O: Op>(
    existing_leaf: *mut Node<O>, // not null
    dir: Direction,
    new_leaf_value: O::LeafValue,
) -> *mut Node<O> {
    let p = (*existing_leaf).parent;
    let Value::Leaf(existing_leaf_value) = &(*existing_leaf).value else {
        panic!("existing_leaf is not a leaf");
    };
    let new_leaf = alloc_from_leaf_value(new_leaf_value);
    let Value::Leaf(new_leaf_value) = &(*new_leaf).value else { unreachable!() };
    let internal = alloc_from_node(match dir {
        Direction::Left => Node {
            parent: p,
            left: new_leaf,
            right: existing_leaf,
            value: Value::Internal(O::mul(
                &O::proj(new_leaf_value),
                &O::proj(existing_leaf_value),
            )),
        },
        Direction::Right => Node {
            parent: p,
            left: existing_leaf,
            right: new_leaf,
            value: Value::Internal(O::mul(
                &O::proj(existing_leaf_value),
                &O::proj(new_leaf_value),
            )),
        },
    });
    (*existing_leaf).parent = internal;
    (*new_leaf).parent = internal;
    if !p.is_null() {
        if (*p).left == existing_leaf {
            (*p).left = internal;
        } else {
            (*p).right = internal;
        }
        (*p).update();
    }
    splay(internal)
}

unsafe fn remove_leaf<O: Op>(leaf: *mut Node<O>) -> (*mut Node<O>, O::LeafValue) {
    let Node {
        parent: p,
        value: Value::Leaf(leaf_value),
        ..
    } = *Box::from_raw(leaf)
    else {
        panic!("leaf is not a leaf");
    };
    if p.is_null() {
        return (ptr::null_mut(), leaf_value);
    }
    let s = if (*p).left == leaf { (*p).right } else { (*p).left };
    let q = (*p).parent;
    (*s).parent = q;
    if q.is_null() {
        (s, leaf_value)
    } else {
        if (*q).left == p {
            (*q).left = s;
        } else {
            (*q).right = s;
        }
        (*q).update();
        (splay(q), leaf_value)
    }
}

unsafe fn lower_bound<O: RightMin>(
    root: *mut Node<O>, // not null
    key: &<O as Op>::LeafValue,
) -> (*mut Node<O>, Direction)
where
    O::LeafValue: Ord,
{
    let mut x = root;
    loop {
        match (*x).value {
            Value::Leaf(ref leaf_value) => {
                let dir = if key <= leaf_value { Direction::Left } else { Direction::Right };
                return (x, dir);
            }
            Value::Internal(ref internal_value) => {
                x = if key <= O::right_min(internal_value) { (*x).left } else { (*x).right };
            }
        }
    }
}

unsafe fn get_by_index<O: LeftLen>(
    root: *mut Node<O>, // not null
    mut index: usize,
) -> *mut Node<O> {
    let mut x = root;
    loop {
        match (*x).value {
            Value::Leaf(_) => return x,
            Value::Internal(ref internal_value) => {
                let left_len = O::left_len(internal_value);
                if index < left_len {
                    x = (*x).left;
                } else {
                    index -= left_len;
                    x = (*x).right;
                }
            }
        }
    }
}

unsafe fn splay<O: Op>(x: *mut Node<O>) -> *mut Node<O> {
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
    x
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
