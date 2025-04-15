#![allow(dead_code)]
use crate::balance::Balance;
use crate::balance::BlackViolation;
use crate::balance::Color;
use crate::balance::Ptr;
use crate::balance::Tree;
use std::cmp::Ordering;
use std::cmp::Reverse;
use std::fmt;
use std::marker::PhantomData;
use std::ops;
use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;

pub trait Op {
    type Value: Clone;

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    fn identity() -> Self::Value;
}

pub struct Node<O: Op> {
    value: O::Value,
    parent: Option<Ptr<Node<O>>>,
    left: Option<Ptr<Node<O>>>,
    right: Option<Ptr<Node<O>>>,
    len: usize,
    color: Color,
}
impl<O: Op> Node<O> {
    pub fn new(value: O::Value, color: Color, len: usize) -> Self {
        Self {
            value,
            parent: None,
            left: None,
            right: None,
            len,
            color,
        }
    }

    pub fn is_leaf(&self) -> bool {
        match self.left {
            None => {
                debug_assert!(self.left.is_none());
                debug_assert!(self.right.is_none());
                debug_assert_eq!(self.len, 1);
                true
            }
            Some(_) => {
                debug_assert!(self.left.is_some());
                debug_assert!(self.right.is_some());
                debug_assert_ne!(self.len, 1);
                false
            }
        }
    }
}
impl<O: Op> Balance for Node<O> {
    fn update(&mut self) {
        // TODO: make sure `update()` is not called for a leaf node.
        match (&self.left, &self.right) {
            (None, None) => {}
            (Some(left), Some(right)) => {
                self.len = left.len + right.len;
                self.value = O::mul(&left.value, &right.value);
            }
            _ => unreachable!(),
        }
    }

    fn push(&mut self) {}

    fn color(&mut self) -> &mut Color {
        &mut self.color
    }

    fn parent(&mut self) -> &mut Option<Ptr<Self>> {
        &mut self.parent
    }

    fn left(&mut self) -> &mut Option<Ptr<Self>> {
        &mut self.left
    }

    fn right(&mut self) -> &mut Option<Ptr<Self>> {
        &mut self.right
    }
}
impl<O: Op> Ptr<Node<O>> {
    pub fn mul(left: Self, right: Self, color: Color) -> Self {
        Ptr::new(Node {
            value: O::mul(
                &left.as_longlife_ref().value,
                &right.as_longlife_ref().value,
            ),
            parent: None,
            left: Some(left),
            right: Some(right),
            len: left.len + right.len,
            color,
        })
    }

    pub fn mul_in(left: Self, right: Self, color: Color, mut p: Self) -> Self {
        p.value = O::mul(
            &left.as_longlife_ref().value,
            &right.as_longlife_ref().value,
        );
        p.parent = None;
        p.left = Some(left);
        p.right = Some(right);
        p.len = left.len + right.len;
        p.color = color;
        p
    }

    pub fn next(self) -> Option<Self> {
        let mut x = self;
        x = loop {
            let mut p = (*x.parent())?;
            if *p.left() == Some(x) {
                break p;
            }
            x = p;
        };
        x = (*x.right())?;
        while let Some(l) = *x.left() {
            x = l;
        }
        Some(x)
    }

    pub fn prev(self) -> Option<Self> {
        let mut x = self;
        if let Some(l) = *x.left() {
            x = l;
            while let Some(r) = *x.right() {
                x = r;
            }
            Some(x)
        } else {
            while let Some(mut p) = *x.parent() {
                if *p.right() == Some(x) {
                    return Some(p);
                }
                x = p;
            }
            None
        }
    }
}

fn join<O: Op>(
    mut left: Tree<Node<O>>,
    center: impl FnOnce(Ptr<Node<O>>, Ptr<Node<O>>, Color) -> Ptr<Node<O>>,
    mut right: Tree<Node<O>>,
) -> Tree<Node<O>> {
    debug_assert!(left.root.is_some());
    debug_assert!(right.root.is_some());
    match left.black_height.cmp(&right.black_height) {
        Ordering::Less => {
            if *left.root.unwrap().color() == Color::Red {
                *left.root.unwrap().color() = Color::Black;
                left.black_height += 1;
            }
            debug_assert!(left.black_height > 0);
            let mut right1 = Tree {
                root: right.root,
                black_height: right.black_height,
            };
            while left.black_height < right1.black_height
                || *right1.root.unwrap().color() == Color::Red
            {
                let mut root = right1.root.unwrap();
                if *root.color() == Color::Black {
                    right1.black_height -= 1;
                }
                right1.root = Some(root.left().unwrap());
            }
            let mut center = center(left.root.unwrap(), right1.root.unwrap(), Color::Red);
            right.transplant(right1.root.unwrap(), Some(center));
            *right1.root.unwrap().parent() = Some(center);
            *left.root.unwrap().parent() = Some(center);
            center.update();
            right.fix_red(center);
            right
        }
        Ordering::Greater => {
            if *right.root.unwrap().color() == Color::Red {
                *right.root.unwrap().color() = Color::Black;
                right.black_height += 1;
            }
            debug_assert!(right.black_height > 0);
            let mut left1 = Tree {
                root: left.root,
                black_height: left.black_height,
            };
            while left1.black_height > right.black_height
                || *left1.root.unwrap().color() == Color::Red
            {
                let mut root = left1.root.unwrap();
                if *root.color() == Color::Black {
                    left1.black_height -= 1;
                }
                left1.root = Some(root.right().unwrap());
            }
            let center = center(left1.root.unwrap(), right.root.unwrap(), Color::Red);
            left.transplant(left1.root.unwrap(), Some(center));
            *left1.root.unwrap().parent() = Some(center);
            *right.root.unwrap().parent() = Some(center);
            left.fix_red(center);
            left
        }
        Ordering::Equal => {
            let center = center(left.root.unwrap(), right.root.unwrap(), Color::Black);
            *left.root.unwrap().parent() = Some(center);
            *right.root.unwrap().parent() = Some(center);
            Tree {
                root: Some(center),
                black_height: left.black_height + 1,
            }
        }
    }
}

pub fn unjoin<O: Op>(mut x: Ptr<Node<O>>, mut x_h: u8) -> (Tree<Node<O>>, Tree<Node<O>>) {
    let mut left = Tree {
        root: *x.left(),
        black_height: x_h - u8::from(*x.color() == Color::Black),
    };
    let mut right = Tree {
        root: *x.right(),
        black_height: x_h - u8::from(*x.color() == Color::Black),
    };
    if let Some(mut l) = *x.left() {
        *l.parent() = None;
    }
    if let Some(mut r) = *x.right() {
        *r.parent() = None;
    }
    while let Some(mut p) = *x.parent() {
        *x.parent() = *p.parent();
        let original_p_color = p.color;
        if let Some(mut pp) = *p.parent() {
            if *pp.left() == Some(p) {
                *pp.left() = Some(x);
            } else {
                *pp.right() = Some(x);
            }
        }
        if *p.left() == Some(x) {
            let s = Tree {
                root: *p.right(),
                black_height: x_h,
            };
            if let Some(mut s) = s.root {
                *s.parent() = None;
            }
            right = join(right, move |l, r, color| Ptr::mul_in(l, r, color, p), s);
        } else {
            let s = Tree {
                root: *p.left(),
                black_height: x_h,
            };
            if let Some(mut s) = s.root {
                *s.parent() = None;
            }
            left = join(s, move |l, r, color| Ptr::mul_in(l, r, color, p), left);
        }
        x_h += u8::from(original_p_color == Color::Black);
    }
    (left, right)
}

pub struct Seg<O: Op> {
    tree: Tree<Node<O>>,
}
impl<O: Op> Seg<O> {
    pub fn new() -> Self {
        Self { tree: Tree::new() }
    }

    pub fn len(&self) -> usize {
        self.tree.root.map_or(0, |root| root.len)
    }

    pub fn is_empty(&self) -> bool {
        self.tree.root.is_none()
    }

    pub fn iter(&self) -> SegIter<'_, O> {
        SegIter {
            start: self.tree.min(),
            end: self.tree.max(),
            len: self.len(),
            marker: PhantomData,
        }
    }

    pub fn display(&self) -> SegDisplay<'_, O> {
        SegDisplay(self)
    }

    pub fn table(&self) -> SegTable<'_, O> {
        SegTable(self)
    }

    pub fn nth(&self, index: usize) -> &O::Value {
        &self.nth_ptr(index).as_longlife_ref().value
    }

    pub fn nth_mut(&mut self, index: usize) -> Entry<'_, O> {
        Entry {
            p: self.nth_ptr(index),
            marker: PhantomData,
        }
    }

    pub fn fold(&self, range: impl RangeBounds<usize>) -> O::Value {
        let (start, end) = into_range(range, self.len());
        assert!(
            start <= end && end <= self.len(),
            "Index out of range:\n range: {start}..{end}\n   len:{}",
            self.len(),
        );
        if start == end {
            return O::identity();
        }
        let mut x = self.tree.root.unwrap();
        let mut offset = 0;
        loop {
            if x.is_leaf() {
                return x.value.clone();
            }
            let node_mid = offset + x.left.unwrap().len;
            x = if end <= node_mid {
                x.left.unwrap()
            } else if node_mid <= start {
                offset = node_mid;
                x.right.unwrap()
            } else {
                break;
            };
        }
        debug_assert!(
            offset <= start
                && start <= offset + x.left.unwrap().len
                && offset + x.left.unwrap().len <= end
        );
        O::mul(
            &{
                let mut node_start = offset;
                let mut x = x.left.unwrap();
                let mut result = O::identity();
                loop {
                    while node_start < start {
                        node_start += x.left.unwrap().len;
                        x = x.right.unwrap();
                    }
                    result = O::mul(&x.value, &result);
                    if node_start == start {
                        break result;
                    }
                    x = x.parent.unwrap().left.unwrap();
                    node_start -= x.len;
                }
            },
            &{
                let mut node_end = offset + x.len;
                let mut x = x.right.unwrap();
                let mut result = O::identity();
                loop {
                    while end < node_end {
                        node_end -= x.right.unwrap().len;
                        x = x.left.unwrap();
                    }
                    result = O::mul(&result, &x.value);
                    if end == node_end {
                        break result;
                    }
                    x = x.parent.unwrap().right.unwrap();
                    node_end += x.len;
                }
            },
        )
    }

    pub fn insert(&mut self, mut index: usize, value: O::Value) {
        assert!(index <= self.len());
        let mut new = Ptr::new(Node::new(value, Color::Black, 1));
        let Some(mut x) = self.tree.root else {
            new.color = Color::Black;
            self.tree.root = Some(new);
            self.tree.black_height = 1;
            return;
        };
        while !x.is_leaf() {
            let left_len = x.left.unwrap().len;
            x = if index < left_len {
                x.left.unwrap()
            } else {
                index -= left_len;
                x.right.unwrap()
            }
        }
        let p = match index {
            0 => Ptr::mul(new, x, Color::Red),
            1 => Ptr::mul(x, new, Color::Red),
            _ => unreachable!(),
        };
        self.tree.transplant(x, Some(p));
        x.parent = Some(p);
        new.parent = Some(p);
        self.tree.fix_red(p);
    }

    pub fn remove(&mut self, index: usize) -> O::Value {
        assert!(index < self.len());
        let x = self.nth_ptr(index);
        let Some(mut p) = x.parent else {
            *self = Self::new();
            return x.free().value;
        };
        let p_color = *p.color();
        let y = (if p.left == Some(x) { p.right } else { p.left }).unwrap();
        self.tree.transplant(p, Some(y));
        if p_color == Color::Black {
            self.tree.fix_black(BlackViolation {
                p: y.parent,
                x: Some(y),
            });
        } else {
            y.update_ancestors();
        }
        x.free().value
    }

    pub fn append(&mut self, other: &mut Self) {
        if self.is_empty() {
            std::mem::swap(self, other);
        }
        if other.is_empty() {
            return;
        }
        self.tree = join(self.tree, Ptr::mul, other.tree);
        other.tree = Tree::new();
    }

    pub fn split_off(&mut self, mut index: usize) -> Self {
        assert!(index <= self.len());
        if index == 0 {
            return std::mem::take(self);
        } else if index == self.len() {
            return Self::new();
        }
        let mut x = self.tree.root.unwrap();
        let mut x_h = self.tree.black_height;
        while !x.is_leaf() {
            let left_len = x.left.unwrap().len;
            x_h -= u8::from(*x.color() == Color::Black);
            x = if index < left_len {
                x.left.unwrap()
            } else {
                index -= left_len;
                x.right.unwrap()
            };
        }
        loop {
            let mut p = x.parent.unwrap();
            if *p.right() == Some(x) {
                x = p;
                x_h += u8::from(*x.color() == Color::Black);
                break;
            }
            x = p;
            x_h += u8::from(*x.color() == Color::Black);
        }
        let (left, right) = unjoin(x, x_h);
        self.tree = left;
        Self { tree: right }
    }

    fn nth_ptr(&self, mut index: usize) -> Ptr<Node<O>> {
        assert!(index < self.len());
        let mut x = self.tree.root.unwrap();
        while !x.is_leaf() {
            let left_len = x.left.unwrap().len;
            x = if index < left_len {
                x.left.unwrap()
            } else {
                index -= left_len;
                x.right.unwrap()
            }
        }
        x
    }
}
impl<O: Op> Default for Seg<O> {
    fn default() -> Self {
        Self::new()
    }
}
impl<O: Op> FromIterator<O::Value> for Seg<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut nodes = iter
            .into_iter()
            .map(|value| Ptr::new(Node::new(value, Color::Black, 1)))
            .collect::<Vec<_>>();
        if nodes.is_empty() {
            return Self::new();
        }
        let mut black_height = 1;
        while nodes.len() > 1 {
            for i in (0..nodes.len() - 1).step_by(2) {
                if i + 3 == nodes.len() {
                    let mut left = nodes[i];
                    let mut center = nodes[i + 1];
                    let mut right = nodes[i + 2];
                    let mut x = Ptr::mul(left, center, Color::Red);
                    let p = Ptr::mul(x, right, Color::Black);
                    left.parent = Some(x);
                    center.parent = Some(x);
                    x.parent = Some(p);
                    right.parent = Some(p);
                    nodes[i / 2] = p;
                } else {
                    let mut left = nodes[i];
                    let mut right = nodes[i + 1];
                    let p = Ptr::mul(left, right, Color::Black);
                    left.parent = Some(p);
                    right.parent = Some(p);
                    nodes[i / 2] = p;
                }
            }
            nodes.truncate(nodes.len() / 2);
            black_height += 1;
        }
        Self {
            tree: Tree {
                root: Some(nodes[0]),
                black_height,
            },
        }
    }
}
impl<O: Op> fmt::Debug for Seg<O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}
impl<'a, O: Op> IntoIterator for &'a Seg<O> {
    type IntoIter = SegIter<'a, O>;
    type Item = &'a O::Value;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
pub struct Entry<'a, O: Op> {
    p: Ptr<Node<O>>,
    marker: PhantomData<&'a O>,
}
impl<'a, O: Op> ops::Deref for Entry<'a, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target {
        &self.p.as_longlife_ref().value
    }
}
impl<'a, O: Op> ops::DerefMut for Entry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.p.as_longlife_mut().value
    }
}
impl<'a, O: Op> Drop for Entry<'a, O> {
    fn drop(&mut self) {
        self.p.update();
        self.p.update_ancestors();
    }
}
struct SegTableCell<'a, O: Op> {
    start: usize,
    end: usize,
    value: &'a O::Value,
}
pub struct SegTable<'a, O: Op>(&'a Seg<O>);
impl<'a, O: Op> SegTable<'a, O> {
    fn collect(&self) -> Vec<Vec<SegTableCell<'a, O>>> {
        fn traverse<'a, O: Op + 'a>(
            vec: &mut Vec<(usize, SegTableCell<'a, O>)>,
            p: Ptr<Node<O>>,
            offset: usize,
        ) -> usize {
            if p.is_leaf() {
                vec.push((0, SegTableCell {
                    start: offset,
                    end: offset + 1,
                    value: &p.as_longlife_ref().value,
                }));
                0
            } else {
                let ht = 1 + traverse(vec, p.left.unwrap(), offset).max(traverse(
                    vec,
                    p.right.unwrap(),
                    offset + p.left.unwrap().len,
                ));
                vec.push((ht, SegTableCell {
                    start: offset,
                    end: offset + p.len,
                    value: &p.as_longlife_ref().value,
                }));
                ht
            }
        }
        let mut vec = Vec::new();
        if let Some(p) = self.0.tree.root {
            traverse(&mut vec, p, 0);
        }
        let mut result = Vec::new();
        for (ht, cell) in vec {
            while result.len() <= ht {
                result.push(Vec::new());
            }
            result[ht].push(cell);
        }
        result
    }
}
impl<'a, O: Op> fmt::Debug for SegTable<'a, O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Row<'a, O: Op>(&'a [SegTableCell<'a, O>]);
        impl<'a, O: Op> fmt::Debug for Row<'a, O>
        where
            O::Value: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let mut debug_map = f.debug_map();
                for cell in self.0 {
                    if cell.start + 1 == cell.end {
                        debug_map.entry(&cell.start, &cell.value);
                    } else {
                        debug_map.entry(&(cell.start..cell.end), &cell.value);
                    }
                }
                debug_map.finish()
            }
        }
        f.debug_list()
            .entries(self.collect().iter().map(|row| Row(row)))
            .finish()
    }
}
impl<'a, O: Op> fmt::Display for SegTable<'a, O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rows = self
            .collect()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|cell| (cell.start..cell.end, format!("{:?}", cell.value)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        if rows.is_empty() {
            writeln!(f, "SegTable (empty)")?;
            return Ok(());
        }
        let n = rows[0].len();
        let mut colomn_width = (0..n).map(|i| i.to_string().len()).collect::<Vec<_>>();
        for (range, value) in rows.iter().flatten() {
            let current_width =
                range.clone().map(|i| colomn_width[i]).sum::<usize>() + range.len() - 1;
            if current_width < value.len() {
                colomn_width[range.end - 1] += value.len() - current_width;
            }
        }
        write!(f, "\x1b[48;2;127;127;127;37m")?;
        write!(f, "|")?;
        for (i, colomn_width) in colomn_width.iter().enumerate() {
            write!(f, "{i:colomn_width$}|")?;
        }
        write!(f, "\x1b[0m")?;
        writeln!(f)?;
        let mut refinement = vec![false; n];
        let rows = rows
            .iter()
            .rev()
            .map(|row| {
                let mut swp = Vec::new();
                let mut offset = 0;
                for (range, value) in row {
                    refinement[range.start] = true;
                    while offset < range.start {
                        let end = (offset + 1..n).find(|&i| refinement[i]).unwrap_or(n);
                        swp.push((offset..end, None));
                        offset = end;
                    }
                    swp.push((range.clone(), Some(value)));
                    offset = range.end;
                }
                if offset < n {
                    swp.push((offset..n, None));
                }
                swp
            })
            .collect::<Vec<_>>();
        for row in rows.iter().rev() {
            write!(f, "|")?;
            for (range, value) in row {
                let width = range.clone().map(|i| colomn_width[i]).sum::<usize>() + range.len() - 1;
                if let Some(value) = value {
                    write!(f, "{value:^width$}")?;
                } else {
                    write!(f, "{:^width$}", "", width = width)?;
                }
                write!(f, "|")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}
pub struct SegDisplay<'a, O: Op>(&'a Seg<O>);
impl<'a, O: Op> SegDisplay<'a, O> {
    fn collect(&self) -> Vec<(Range<usize>, &O::Value)> {
        let mut stack = vec![(0..self.0.len(), self.0.tree.root)];
        let mut vec = Vec::new();
        while let Some((range, p)) = stack.pop() {
            if let Some(p) = p {
                vec.push((range.clone(), &p.as_longlife_ref().value));
                if !p.is_leaf() {
                    let left_len = p.left.unwrap().len;
                    stack.push((range.start..range.start + left_len, p.left));
                    stack.push((range.start + left_len..range.end, p.right));
                }
            }
        }
        vec.sort_by_key(|(range, _)| (Reverse(range.len()), range.end));
        vec
    }
}
impl<'a, O: Op> fmt::Display for SegDisplay<'a, O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SegDisplay ({:?}):", &self.0)?;
        for (range, value) in self.collect() {
            if range.start + 1 < range.end {
                writeln!(f, " {}..{}: {:?}", range.start, range.end, value)?;
            }
        }
        Ok(())
    }
}
impl<'a, O: Op> fmt::Debug for SegDisplay<'a, O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug_map = f.debug_map();
        for (range, value) in self.collect() {
            if range.start + 1 == range.end {
                debug_map.entry(&range.start, value);
            } else {
                debug_map.entry(&range, value);
            }
        }
        debug_map.finish()
    }
}
pub struct SegIter<'a, O: Op> {
    start: Option<Ptr<Node<O>>>,
    end: Option<Ptr<Node<O>>>,
    len: usize,
    marker: PhantomData<&'a O>,
}
impl<'a, O: Op> Iterator for SegIter<'a, O> {
    type Item = &'a O::Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let x = self.start.unwrap();
        self.start = x.next();
        self.len -= 1;
        let x = x.as_longlife_ref();
        Some(&x.value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}
impl<'a, O: Op> DoubleEndedIterator for SegIter<'a, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let x = self.end.unwrap();
        self.end = x.prev();
        self.len -= 1;
        let x = x.as_longlife_ref();
        Some(&x.value)
    }
}
impl<'a, O: Op> ExactSizeIterator for SegIter<'a, O> {}

fn into_range(range: impl RangeBounds<usize>, len: usize) -> (usize, usize) {
    let start = match range.start_bound() {
        Bound::Included(&i) => i,
        Bound::Excluded(&i) => i + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&i) => i + 1,
        Bound::Excluded(&i) => i,
        Bound::Unbounded => len,
    };
    (start, end)
}
#[cfg(test)]
mod test_seg {
    use super::Node;
    use super::Op;
    use super::Ptr;
    use super::Seg;
    use crate::balance::Color;
    use crate::balance::Tree;
    use rand::distributions::Alphanumeric;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    enum O {}
    impl Op for O {
        type Value = String;

        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            lhs.chars().chain(rhs.chars()).collect()
        }

        fn identity() -> Self::Value {
            String::new()
        }
    }

    impl Seg<O> {
        fn random(rng: &mut StdRng, black_height: u8) -> Self {
            fn random(rng: &mut StdRng, black_height: u8, parent_color: Color) -> Ptr<Node<O>> {
                let color = match parent_color {
                    Color::Red => Color::Black,
                    Color::Black => {
                        if rng.gen() {
                            Color::Red
                        } else {
                            Color::Black
                        }
                    }
                };
                if black_height == 1 && color == Color::Black {
                    return Ptr::new(Node::<O> {
                        value: char::from(rng.sample(Alphanumeric)).to_string(),
                        parent: None,
                        left: None,
                        right: None,
                        color,
                        len: 1,
                    });
                }
                let mut left = random(rng, black_height - u8::from(color == Color::Black), color);
                let mut right = random(rng, black_height - u8::from(color == Color::Black), color);
                let x = Ptr::new(Node {
                    value: O::mul(
                        &left.as_longlife_ref().value,
                        &right.as_longlife_ref().value,
                    ),
                    parent: None,
                    left: Some(left),
                    right: Some(right),
                    color,
                    len: left.len + right.len,
                });
                left.parent = Some(x);
                right.parent = Some(x);
                x
            }
            if black_height == 0 {
                Self::new()
            } else {
                Self {
                    tree: Tree {
                        root: Some(random(rng, black_height, Color::Black)),
                        black_height,
                    },
                }
            }
        }

        fn validate(&self) {
            fn validate(p: Option<Ptr<Node<O>>>) -> Result<(), String> {
                if let Some(p) = p {
                    if p.is_leaf() {
                        return Ok(());
                    }
                    validate(p.left)?;
                    let mut expected = String::new();
                    expected.push_str(&p.left.unwrap().value);
                    expected.push_str(&p.right.unwrap().value);
                    (p.value == expected).then_some(()).ok_or_else(|| {
                        format!(
                            "Value is incorrect at {:?}. Expected {}, but cached {}",
                            p, expected, &p.value
                        )
                    })?;
                    validate(p.right)?;
                }
                Ok(())
            }
            self.tree.validate();
            validate(self.tree.root).unwrap_or_else(|e| {
                panic!(
                    "{e}:\n Tree: {}",
                    self.tree.format_by(|p| format!("<{:?}:{}>", p, p.value))
                )
            });
        }
    }

    #[test]
    fn test_seg_from_iter() {
        let mut rng = StdRng::seed_from_u64(42);
        for len in 0..200 {
            let seg = (&mut rng)
                .sample_iter(&Alphanumeric)
                .map(|b| char::from(b).to_string())
                .take(len)
                .collect::<Seg<O>>();
            seg.validate();
        }
    }

    #[test]
    fn test_seg_nth_mut() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let black_height = rng.gen_range(1..=4);
            let mut seg = Seg::random(&mut rng, black_height);
            let mut vec = seg.iter().cloned().collect::<Vec<_>>();
            for _ in 0..200 {
                let i = rng.gen_range(0..seg.len());
                let x = (&mut rng)
                    .sample_iter(&Alphanumeric)
                    .take(1)
                    .map(char::from)
                    .collect::<String>();
                *seg.nth_mut(i) = x.clone();
                vec[i] = x;
                seg.validate();
                assert_eq!(seg.iter().cloned().collect::<Vec<_>>(), vec);
            }
        }
    }

    #[test]
    fn test_fold() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let black_height = rng.gen_range(0..=4);
            let seg = Seg::random(&mut rng, black_height);
            seg.tree.validate();
            seg.validate();
            let n = seg.len();
            let vec = seg.iter().cloned().collect::<Vec<_>>();
            for _ in 0..200 {
                let mut i = rng.gen_range(0..=n + 1);
                let mut j = rng.gen_range(0..=n);
                if i > j {
                    std::mem::swap(&mut i, &mut j);
                    j -= 1;
                }
                let result = seg.fold(i..j);
                let expected = vec[i..j].iter().flat_map(|s| s.chars()).collect::<String>();
                assert_eq!(result, expected, "fold({i}..{j})");
            }
        }
    }

    #[test]
    fn test_seg_insert_remove() {
        const LEN_LIM: usize = 60;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut used = [false; LEN_LIM];
            let mut seg = Seg::<O>::new();
            let mut vec = Vec::new();
            for _ in 0..200 {
                let i = rng.gen_range(0..LEN_LIM);
                // Remove
                if used[i] {
                    used[i] = false;
                    let position = used[..=i].iter().filter(|&&b| b).count();
                    let result = seg.remove(position);
                    let expected = vec.remove(position);
                    assert_eq!(result, expected);
                }
                // Insert
                else {
                    used[i] = true;
                    let s = char::from(rng.sample(Alphanumeric)).to_string();
                    let position = used[..i].iter().filter(|&&b| b).count();
                    seg.insert(position, s.clone());
                    vec.insert(position, s);
                }
                assert_eq!(seg.iter().cloned().collect::<Vec<_>>(), vec);
                seg.validate();
            }
        }
    }

    #[test]
    fn test_seg_append() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let left_h = rng.gen_range(0..=4);
            let right_h = rng.gen_range(0..=4);
            let mut left = Seg::random(&mut rng, left_h);
            let mut right = Seg::random(&mut rng, right_h);
            let expected = left
                .iter()
                .cloned()
                .chain(right.iter().cloned())
                .collect::<Vec<_>>();
            left.append(&mut right);
            left.validate();
            right.validate();
            assert_eq!(left.iter().cloned().collect::<Vec<_>>(), expected);
            assert!(right.is_empty());
        }
    }

    #[test]
    fn test_seg_split_off() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let h = rng.gen_range(0..=5);
            let mut seg = Seg::random(&mut rng, h);
            let i = rng.gen_range(0..=seg.len());
            let expected = seg.iter().cloned().collect::<Vec<_>>();
            let right = seg.split_off(i);
            seg.validate();
            right.validate();
            assert_eq!(seg.iter().cloned().collect::<Vec<_>>(), expected[..i]);
            assert_eq!(right.iter().cloned().collect::<Vec<_>>(), expected[i..]);
        }
    }
}
