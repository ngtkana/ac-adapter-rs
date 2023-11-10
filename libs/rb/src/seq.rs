#![allow(dead_code)]
use crate::balance::join;
use crate::balance::Balance;
use crate::balance::Color;
use crate::balance::Ptr;
use crate::balance::Tree;
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

    fn color(&mut self) -> &mut Color { &mut self.color }

    fn parent(&mut self) -> &mut Option<Ptr<Self>> { &mut self.parent }

    fn left(&mut self) -> &mut Option<Ptr<Self>> { &mut self.left }

    fn right(&mut self) -> &mut Option<Ptr<Self>> { &mut self.right }
}
impl<O: Op> Ptr<Node<O>> {
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

pub struct Seg<O: Op> {
    tree: Tree<Node<O>>,
}
impl<O: Op> Seg<O> {
    pub fn new() -> Self { Self { tree: Tree::new() } }

    pub fn len(&self) -> usize { self.tree.root.map_or(0, |root| root.len) }

    pub fn is_empty(&self) -> bool { self.tree.root.is_none() }

    pub fn iter(&self) -> SegIter<'_, O> {
        SegIter {
            start: self.tree.min(),
            end: self.tree.max(),
            len: self.len(),
            marker: PhantomData,
        }
    }

    pub fn display(&self) -> SegDisplay<'_, O> { SegDisplay(self) }

    pub fn table(&self) -> SegTable<'_, O> { SegTable(self) }

    pub fn nth(&self, index: usize) -> &O::Value { &self.nth_ptr(index).as_longlife_ref().value }

    pub fn nth_mut(&mut self, index: usize) -> Entry<'_, O> {
        Entry {
            p: self.nth_ptr(index),
            marker: PhantomData,
        }
    }

    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Value> {
        let (start, end) = into_range(range, self.len());
        assert!(
            start <= end && end <= self.len(),
            "Index out of range:\n range: {start}..{end}\n   len:{}",
            self.len(),
        );
        if start == end {
            return None;
        }
        let mut x = self.tree.root.unwrap();
        let mut offset = 0;
        loop {
            if x.is_leaf() {
                return Some(x.value.clone());
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
        Some(O::mul(
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
        ))
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
        let mut p;
        match index {
            0 => {
                p = Ptr::new(Node::new(O::mul(&new.value, &x.value), Color::Red, 1));
                self.tree.transplant(x, Some(p));
                p.left = Some(new);
                p.right = Some(x);
                new.parent = Some(p);
                x.parent = Some(p);
            }
            1 => {
                p = Ptr::new(Node::new(O::mul(&x.value, &new.value), Color::Red, 1));
                self.tree.transplant(x, Some(p));
                p.left = Some(x);
                p.right = Some(new);
                x.parent = Some(p);
                new.parent = Some(p);
            }
            _ => unreachable!(),
        }
        p.update();
        self.tree.fix_red(p);
    }

    pub fn append(&mut self, other: &mut Self) {
        if self.is_empty() {
            std::mem::swap(self, other);
        }
        if other.is_empty() {
            return;
        }
        self.tree = join(
            self.tree,
            |l, r| {
                Ptr::new(Node::new(
                    O::mul(&l.value, &r.value),
                    Color::Black,
                    l.len + r.len,
                ))
            },
            other.tree,
        );
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
    fn default() -> Self { Self::new() }
}
impl<O: Op> FromIterator<O::Value> for Seg<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut stack = Vec::new();
        for value in iter {
            stack.push((Ptr::new(Node::new(value, Color::Black, 1)), 1));
            while stack.len() >= 2 && stack[stack.len() - 2].1 == stack[stack.len() - 1].1 {
                let (mut right, right_h) = stack.pop().unwrap();
                let (mut left, left_h) = stack.pop().unwrap();
                debug_assert_eq!(left_h, right_h);
                let mut center = Ptr::new(Node::new(
                    O::mul(&left.value, &right.value),
                    Color::Black,
                    left.len + right.len,
                ));
                center.left = Some(left);
                center.right = Some(right);
                left.parent = Some(center);
                right.parent = Some(center);
                stack.push((center, left_h + 1));
            }
        }
        let Some((mut right, mut right_h)) = stack.pop() else { return Self::new() };
        while let Some((left, left_h)) = stack.pop() {
            let mut x = left;
            for _ in 0..left_h - right_h - 1 {
                x = x.right.unwrap();
            }
            let mut center = x.right.unwrap();
            let mut new = Ptr::new(Node::new(
                O::mul(&center.value, &right.value),
                Color::Black,
                center.len + right.len,
            ));
            new.left = Some(center);
            new.right = Some(right);
            x.right = Some(new);
            center.parent = Some(new);
            right.parent = Some(new);
            new.parent = Some(x);
            *x.color() = Color::Red;
            x.update();
            x.update_ancestors();
            right = left;
            right_h = left_h;
        }
        Self {
            tree: Tree {
                root: Some(right),
                black_height: right_h,
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

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}
pub struct Entry<'a, O: Op> {
    p: Ptr<Node<O>>,
    marker: PhantomData<&'a O>,
}
impl<'a, O: Op> ops::Deref for Entry<'a, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target { &self.p.as_longlife_ref().value }
}
impl<'a, O: Op> ops::DerefMut for Entry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.p.as_longlife_mut().value }
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
            write!(f, "{:width$}|", i, width = colomn_width)?;
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
                for (range, value) in row.iter() {
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
                    write!(f, "{:^width$}", value, width = width)?;
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

    fn size_hint(&self) -> (usize, Option<usize>) { (self.len, Some(self.len)) }
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
    use crate::balance::Balance;
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

        fn identity() -> Self::Value { String::new() }
    }

    impl Seg<O> {
        fn random(rng: &mut StdRng, black_height: u8) -> Self {
            fn update_all(mut p: Ptr<Node<O>>) {
                if p.left.is_some() {
                    update_all(p.left.unwrap());
                    update_all(p.right.unwrap());
                    p.update();
                }
            }
            let (tree, _) = Tree::random(
                rng,
                |rng, color| {
                    Node::new(
                        rng.sample_iter(&Alphanumeric)
                            .take(1)
                            .map(char::from)
                            .collect::<String>(),
                        color,
                        1,
                    )
                },
                black_height,
                false,
                false,
                true,
            );
            if let Some(root) = tree.root {
                update_all(root);
            }
            Self { tree }
        }

        fn validate_value(&self) {
            fn validate_value(p: Option<Ptr<Node<O>>>) -> Result<(), String> {
                if let Some(p) = p {
                    if p.is_leaf() {
                        return Ok(());
                    }
                    validate_value(p.left)?;
                    let mut expected = String::new();
                    expected.push_str(&p.left.unwrap().value);
                    expected.push_str(&p.right.unwrap().value);
                    (p.value == expected).then_some(()).ok_or_else(|| {
                        format!(
                            "Value is incorrect at {:?}. Expected {}, but cached {}",
                            p, expected, &p.value
                        )
                    })?;
                    validate_value(p.right)?;
                }
                Ok(())
            }
            validate_value(self.tree.root).unwrap_or_else(|e| {
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
            seg.tree.validate();
            seg.validate_value();
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
                seg.tree.validate();
                seg.validate_value();
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
            seg.validate_value();
            let n = seg.len();
            let vec = seg.iter().cloned().collect::<Vec<_>>();
            for _ in 0..200 {
                let mut i = rng.gen_range(0..=n + 1);
                let mut j = rng.gen_range(0..=n);
                if i > j {
                    std::mem::swap(&mut i, &mut j);
                    j -= 1;
                }
                let result = seg.fold(i..j).unwrap_or_default();
                let expected = vec[i..j].iter().flat_map(|s| s.chars()).collect::<String>();
                assert_eq!(result, expected, "fold({i}..{j})");
            }
        }
    }

    #[test]
    fn test_seg_insert() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut seg = Seg::<O>::new();
            let mut vec = Vec::new();
            for _ in 0..20 {
                let i = rng.gen_range(0..=seg.len());
                let s = (&mut rng)
                    .sample_iter(&Alphanumeric)
                    .take(1)
                    .map(char::from)
                    .collect::<String>();
                seg.insert(i, s.clone());
                vec.insert(i, s);
                assert_eq!(seg.iter().cloned().collect::<Vec<_>>(), vec);
                seg.validate_value();
            }
        }
    }
}
