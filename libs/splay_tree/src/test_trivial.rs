use {
    super::{LazyOps, Nop, SplayTree},
    itertools::assert_equal,
    std::{cmp::Ordering, collections::HashSet, fmt::Debug},
};

enum I32Add {}
impl LazyOps for I32Add {
    type Value = i32;
    type Acc = i32;
    type Lazy = ();
    fn proj(&value: &Self::Value) -> Self::Acc {
        value
    }
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc {
        lhs + rhs
    }
    fn act_value(&(): &Self::Lazy, _value: &mut Self::Value) {}
    fn act_acc(&(): &Self::Lazy, _acc: &mut Self::Acc) {}
    fn compose(&(): &Self::Lazy, &mut (): &mut Self::Lazy) {}
}

#[test]
fn test_clone() {
    let splay = (0..10).collect::<SplayTree<Nop<i32>>>();
    let new = splay.clone();
    assert_eq!(splay, new);
    for i in 0..10 {
        splay.get(i);
        new.get(i);
        assert_ne!(splay.0.get(), new.0.get());
    }
}

#[test]
fn test_default() {
    let splay = SplayTree::<Nop<i32>>::new();
    assert!(splay.is_empty());
}

fn from_slice<T: Copy + Sized + Debug>(a: &[T]) -> SplayTree<Nop<T>> {
    a.iter().copied().collect()
}

#[test]
fn test_eq() {
    assert_eq!(from_slice(&[0, 1]), from_slice(&[0, 1]),);
    assert_ne!(from_slice(&[0, 1]), from_slice(&[0, 1, 2]),);
    assert_ne!(from_slice(&[0, 1, 2]), from_slice(&[0, 1]),);
    assert_ne!(from_slice(&[0, 1]), from_slice(&[0, 2]),);
    assert_ne!(from_slice(&[0, 1]), from_slice(&[2, 1]),);
}

#[test]
fn test_partial_cmp() {
    assert_eq!(
        from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[0.0, 1.0])),
        Some(Ordering::Equal)
    );
    assert_eq!(
        from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[0.0, 1.0, 2.0])),
        Some(Ordering::Less)
    );
    assert_eq!(
        from_slice(&[0.0, 1.0, 2.0]).partial_cmp(&from_slice(&[0.0, 1.0])),
        Some(Ordering::Greater)
    );
    assert_eq!(
        from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[0.0, 2.0])),
        Some(Ordering::Less)
    );
    assert_eq!(
        from_slice(&[0.0, 2.0]).partial_cmp(&from_slice(&[0.0, 1.0])),
        Some(Ordering::Greater)
    );
    assert_eq!(
        from_slice(&[0.0, 2.0]).partial_cmp(&from_slice(&[0.0, std::f64::NAN])),
        None,
    );
    assert_eq!(
        from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[2.0, std::f64::NAN])),
        Some(Ordering::Less)
    );
}

#[test]
fn test_hash() {
    #![allow(clippy::bool_assert_comparison)]
    #[allow(clippy::mutable_key_type)]
    let mut set = HashSet::new();
    set.insert(from_slice(&[0, 1]));
    assert_eq!(set.len(), 1);
    set.insert(from_slice(&[0, 1]));
    assert_eq!(set.len(), 1);
    set.insert(from_slice(&[0, 2]));
    assert_eq!(set.len(), 2);
    assert_eq!(set.remove(&from_slice(&[0, 3])), false);
    assert_eq!(set.remove(&from_slice(&[0, 2])), true);
    assert_eq!(set.len(), 1);
}

#[test]
fn test_len() {
    let mut splay = (0..10).collect::<SplayTree<Nop<i32>>>();
    assert_eq!(splay.len(), 10);
    splay.delete(3);
    assert_eq!(splay.len(), 9);
    splay.insert(4, 42);
    assert_eq!(splay.len(), 10);
}

#[test]
fn test_entry() {
    let mut splay = (0..5).collect::<SplayTree<I32Add>>();
    *splay.entry(2).unwrap() = 42;
    assert!(splay.entry(1000).is_none());
    assert_eq!(splay.fold(..), Some(1 + 42 + 3 + 4));
}

#[test]
fn test_fold_all() {
    let mut splay = (0..5).collect::<SplayTree<I32Add>>();
    assert_eq!(splay.fold(..).unwrap(), 10);
    splay.delete(3);
    assert_eq!(splay.fold(..).unwrap(), 7);
    splay.insert(4, 12);
    assert_eq!(splay.fold(..).unwrap(), 19);
}

#[test]
fn test_iter() {
    let splay = (0..10).collect::<SplayTree<Nop<i32>>>();
    assert_equal(splay.iter().copied(), 0..10);
    assert_equal(splay.iter().rev().copied(), (0..10).rev());
}
