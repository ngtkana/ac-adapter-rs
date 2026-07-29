use std::{collections::VecDeque, mem::replace};

pub fn hopcroft_karp(g: &[Vec<usize>]) -> Vec<usize> {
    let n = g.len();
    let mut queue = VecDeque::new();
    let mut f = vec![usize::MAX; n];
    let mut label = vec![usize::MAX; n];
    for x in (0..n).filter(|&i| !g[i].is_empty()) {
        queue.push_back(x);
        label[x] = 0;
    }
    loop {
        let orig_count = queue.len();
        while let Some(x) = queue.pop_front() {
            for &y in &g[x] {
                if label[y] == usize::MAX {
                    label[y] = label[x] + 1;
                    let z = f[y];
                    if z != usize::MAX && label[z] == usize::MAX {
                        label[z] = label[x] + 2;
                        queue.push_back(z);
                    }
                }
            }
        }
        for x in 0..n {
            if label[x] == 0 && !primal(x, &mut label, g, &mut f) {
                queue.push_back(x);
            }
        }
        if orig_count == queue.len() || queue.is_empty() {
            return f;
        }
        label.fill(usize::MAX);
        for &x in &queue {
            label[x] = 0;
        }
    }
}

fn primal(x: usize, label: &mut [usize], g: &[Vec<usize>], f: &mut [usize]) -> bool {
    let d = replace(&mut label[x], usize::MAX);
    for &y in &g[x] {
        if d + 1 == label[y] {
            let z = f[y];
            if z == usize::MAX || (d + 2 == label[z] && primal(z, label, g, f)) {
                f[y] = x;
                return true;
            }
        }
    }
    false
}
