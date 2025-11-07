use super::{CoreTree, Node, NodeMarker};

pub fn display<C: NodeMarker>(tree: &CoreTree<C>) -> String
where
    C::Data: std::fmt::Debug,
{
    fn display_recur<C: NodeMarker>(x: &Node<C>, s: &mut String, d: u8)
    where
        C::Data: std::fmt::Debug,
    {
        use std::fmt::Write;
        if let Some(l) = x.left.as_ref() {
            display_recur(l, s, d + 1);
        }
        writeln!(
            s,
            "{space1}●{space2} len={len} ht={ht}{rev} {data:?}",
            space1 = " ".repeat(d as usize),
            space2 = " ".repeat(4_usize.saturating_sub(d as usize)),
            len = x.len,
            ht = x.ht,
            rev = if x.rev { "[rev] " } else { "" },
            data = x.data,
        )
        .unwrap();
        if let Some(r) = x.right.as_ref() {
            display_recur(r, s, d + 1);
        }
    }
    let Some(x) = tree.root.as_ref() else { return "(empty)".to_owned() };
    let mut s = String::new();
    display_recur(x, &mut s, 1);
    s
}

pub fn validate<C: NodeMarker>(x: Option<&Node<C>>)
where
    C::Data: std::fmt::Debug,
{
    fn validate_recur<C: NodeMarker>(x: &Node<C>)
    where
        C::Data: std::fmt::Debug,
    {
        let lh = x.left.as_ref().map_or(0, |l| l.ht);
        let rh = x.right.as_ref().map_or(0, |r| r.ht);
        assert!(matches!(lh as i8 - rh as i8, -1..=1));
        assert_eq!(lh.max(rh) + 1, x.ht);
        if let Some(l) = x.left.as_ref() {
            validate_recur(l);
        }
        if let Some(r) = x.right.as_ref() {
            validate_recur(r);
        }
    }
    let Some(x) = x else { return };
    validate_recur(x);
}
