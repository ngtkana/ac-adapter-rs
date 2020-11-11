use std::{cmp::Reverse, collections::BinaryHeap, iter};

pub fn prufer2tree(prufer: &[usize]) -> Vec<Vec<usize>> {
    let n = prufer.len() + 2;
    assert!(prufer.iter().all(|&x| x < n));

    let b = prufer
        .iter()
        .copied()
        .chain(iter::once(n - 1))
        .collect::<Vec<_>>();
    let mut m = vec![0; n];
    b.iter().for_each(|&y| m[y] += 1);

    let mut heap = m
        .iter()
        .enumerate()
        .filter(|&(_, &x)| x == 0)
        .map(|(i, _)| Reverse(i))
        .collect::<BinaryHeap<_>>();
    let mut a = Vec::new();
    for &y in &b {
        a.push(heap.pop().unwrap().0);
        m[y] -= 1;
        if m[y] == 0 {
            heap.push(Reverse(y));
        }
    }

    let mut g = vec![Vec::new(); n];
    a.iter().zip(b.iter()).for_each(|(&x, &y)| {
        g[x].push(y);
        g[y].push(x);
    });
    g
}
