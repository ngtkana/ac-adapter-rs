use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{collections::VecDeque, fmt::Display, mem::replace};

#[derive(Debug, Default)]
struct Recorder {
    aug_path_count: Vec<usize>,
    call_primal_count: Vec<usize>,
}

const ITERATION: usize = 100;
const EPOCH_LEN: usize = 30;

fn main() {
    let mut rng = StdRng::seed_from_u64(42);
    for (n, m) in [
        (1_000, 1_000),
        (1_000, 3_000),
        (1_000, 10_000),
        (30_000, 30_000),
        (30_000, 100_000),
        (30_000, 300_000),
    ] {
        let mut epoch_count = vec![];
        let mut matching_count = vec![];
        let mut call_primal_count = vec![];
        let mut epochwise_call_primal_count = vec![vec![]; EPOCH_LEN];

        for _ in 0..ITERATION {
            let g = gen_case(&mut rng, n, m);

            let mut recorder = Recorder::default();
            let _h = bipartite_matching(&g, &mut recorder);

            epoch_count.push(recorder.aug_path_count.len() as f64);
            matching_count.push(recorder.aug_path_count.iter().sum::<usize>() as f64);
            call_primal_count.push(recorder.call_primal_count.iter().sum::<usize>() as f64);
            for epoch in 0..EPOCH_LEN {
                epochwise_call_primal_count[epoch].push(
                    recorder
                        .call_primal_count
                        .get(epoch)
                        .map_or(0., |&x| x as f64),
                );
            }
        }

        println!("Case: n = {n}, m = {m}");
        println!("Epoch count: {}", Stats(&epoch_count));
        println!("Matching count: {}", Stats(&matching_count));
        println!("Call primal count (sum): {}", Stats(&call_primal_count));
        for epoch in 0..EPOCH_LEN {
            println!(
                "Call primal count (epoch {epoch}): {}",
                Stats(&epochwise_call_primal_count[epoch])
            );
        }
        println!();
    }
}

struct Stats<'a>(&'a [f64]);
impl Display for Stats<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(items) = self;
        write!(
            f,
            "[min, average, max] = [{}, {}, {}]",
            min(items),
            average(items),
            max(items)
        )
    }
}

fn average(items: &[f64]) -> f64 {
    items.iter().sum::<f64>() / items.len() as f64
}

fn min(items: &[f64]) -> f64 {
    items.iter().fold(f64::INFINITY, |x, y| x.min(*y))
}

fn max(items: &[f64]) -> f64 {
    items.iter().fold(f64::NEG_INFINITY, |x, y| x.max(*y))
}

fn gen_case(rng: &mut impl Rng, n: usize, m: usize) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; 2 * n];
    for _ in 0..m {
        let (i, j) = loop {
            let i = rng.gen_range(0..n);
            let j = rng.gen_range(n..2 * n);
            if g[i].contains(&j) {
                continue;
            }
            break (i, j);
        };
        g[i].push(j);
    }
    g
}

fn bipartite_matching(g: &[Vec<usize>], recorder: &mut Recorder) -> Vec<usize> {
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
        recorder.call_primal_count.push(0);
        for x in 0..n {
            if label[x] == 0 && !primal(x, &mut label, g, &mut f, recorder) {
                queue.push_back(x);
            }
        }
        recorder.aug_path_count.push(orig_count - queue.len());
        if orig_count == queue.len() || queue.is_empty() {
            return f;
        }
        label.fill(usize::MAX);
        for &x in &queue {
            label[x] = 0;
        }
    }
}

fn primal(
    x: usize,
    label: &mut [usize],
    g: &[Vec<usize>],
    f: &mut [usize],
    recorder: &mut Recorder,
) -> bool {
    *recorder.call_primal_count.last_mut().unwrap() += 1;
    let d = replace(&mut label[x], usize::MAX);
    for &y in &g[x] {
        if d + 1 == label[y] {
            let z = f[y];
            if z == usize::MAX || (d + 2 == label[z] && primal(z, label, g, f, recorder)) {
                f[y] = x;
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng, rngs::StdRng, seq::SliceRandom};

    fn naive(g: &[Vec<usize>]) -> Vec<usize> {
        let n = g.len();
        let Some(i) = (0..n).find(|&i| !g[i].is_empty()) else {
            return vec![usize::MAX; n];
        };
        let mut g = g.to_vec();
        let gi = std::mem::take(&mut g[i]);
        let mut cands = vec![];
        cands.push(naive(&g));
        for j in gi {
            let mut g = g.clone();
            for g in &mut g {
                g.retain(|&x| x != j);
            }
            let mut result = naive(&g);
            result[j] = i;
            cands.push(result);
        }
        cands
            .into_iter()
            .max_by_key(|result| result.iter().filter(|&&x| x != usize::MAX).count())
            .unwrap()
    }

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..=16);
            let l = rng.gen_range(0..=n);
            let r = n - l;
            let m = rng.gen_range(0..=l * r);

            let mut is_left = vec![false; n];
            is_left[..l].fill(true);
            is_left.shuffle(&mut rng);

            let mut g = vec![vec![]; n];
            for _ in 0..m {
                loop {
                    let i = rng.gen_range(0..n);
                    let j = rng.gen_range(0..n);
                    if !is_left[i] || is_left[j] || g[i].contains(&j) {
                        continue;
                    }
                    g[i].push(j);
                    break;
                }
            }

            let result = bipartite_matching(&g, &mut Recorder::default());
            let expected = naive(&g);
            assert_eq!(
                result.iter().filter(|&&x| x != usize::MAX).count(),
                expected.iter().filter(|&&x| x != usize::MAX).count(),
                "result = {result:?}, expected = {expected:?}, is_left = {is_left:?}, g = {g:?}",
            );
        }
    }
}

// lg {{{
// https://ngtkana.github.io/ac-adapter-rs/lg/index.html
#[allow(unused_imports)]
#[allow(dead_code)]
mod lg {
    mod map {
        use crate::lg::align_of;
        use crate::lg::format;
        use crate::lg::table::Align;
        use crate::lg::table::Cell;
        use crate::lg::table::Table;
        use std::collections;
        use std::collections::BTreeMap;
        use std::collections::HashMap;
        use std::fmt;
        use std::iter;
        use std::slice;
        use std::vec;
        pub fn vmap<'a, K, V, M>(title: &str, map: M) -> Table
        where
            M: Copy + Map<'a, K = K, V = V>,
            K: fmt::Debug,
            V: fmt::Debug,
        {
            Table {
                table: iter::once(vec![
                    Cell {
                        text: String::new(),
                        align: Align::Left,
                    },
                    Cell {
                        text: title.to_string(),
                        align: Align::Center,
                    },
                ])
                .chain(map.map_iter().map(|(k, v)| {
                    let v = format(&v);
                    vec![
                        Cell {
                            text: format(&k),
                            align: Align::Center,
                        },
                        Cell {
                            align: align_of(&v),
                            text: v,
                        },
                    ]
                }))
                .collect(),
            }
        }
        pub fn hmap<'a, K, V, M>(title: &str, map: M) -> Table
        where
            M: Copy + Map<'a, K = K, V = V>,
            K: fmt::Debug,
            V: fmt::Debug,
        {
            Table {
                table: vec![
                    iter::once(Cell {
                        text: String::new(),
                        align: Align::Left,
                    })
                    .chain(map.map_iter().map(|(k, _)| Cell {
                        text: format(&k),
                        align: Align::Center,
                    }))
                    .collect(),
                    iter::once(Cell {
                        text: title.to_string(),
                        align: Align::Left,
                    })
                    .chain(map.map_iter().map(|(_, v)| {
                        let v = format(&v);
                        Cell {
                            align: align_of(&v),
                            text: v,
                        }
                    }))
                    .collect(),
                ],
            }
        }
        pub fn deconstruct_ref_tuple<K, V>((k, v): &(K, V)) -> (&K, &V) {
            (k, v)
        }
        pub trait Map<'a>: 'a {
            type K;
            type V;
            type I: Iterator<Item = (&'a Self::K, &'a Self::V)>;
            fn map_iter(self) -> Self::I;
        }
        impl<'a, K, V, S> Map<'a> for &'a HashMap<K, V, S> {
            type I = collections::hash_map::Iter<'a, K, V>;
            type K = K;
            type V = V;
            fn map_iter(self) -> Self::I {
                self.iter()
            }
        }
        impl<'a, K, V> Map<'a> for &'a BTreeMap<K, V> {
            type I = collections::btree_map::Iter<'a, K, V>;
            type K = K;
            type V = V;
            fn map_iter(self) -> Self::I {
                self.iter()
            }
        }
        impl<'a, K, V> Map<'a> for &'a [(K, V)] {
            type I = iter::Map<slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>;
            type K = K;
            type V = V;
            fn map_iter(self) -> Self::I {
                self.iter().map(deconstruct_ref_tuple)
            }
        }
        impl<'a, K, V> Map<'a> for &'a Vec<(K, V)> {
            type I = iter::Map<slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>;
            type K = K;
            type V = V;
            fn map_iter(self) -> Self::I {
                self.iter().map(deconstruct_ref_tuple)
            }
        }
        impl<'a, const N: usize, K, V> Map<'a> for &'a [(K, V); N] {
            type I = iter::Map<slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>;
            type K = K;
            type V = V;
            fn map_iter(self) -> Self::I {
                self.iter().map(deconstruct_ref_tuple)
            }
        }
    }
    mod table {
        use core::fmt;
        const GRAY: &str = "\x1b[48;2;127;127;127;37m";
        const RESET: &str = "\x1b[0m";
        pub struct Table {
            pub table: Vec<Vec<Cell>>,
        }
        pub struct Cell {
            pub text: String,
            pub align: Align,
        }
        pub enum Align {
            Left,
            Center,
            Right,
        }
        impl fmt::Display for Table {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                struct ColumnFormat<'a> {
                    pre: &'a str,
                    width: usize,
                    post: &'a str,
                }
                let Self { table } = self;
                let w = table[0].len();
                assert!(table.iter().all(|row| row.len() == w));
                let column_format = (0..w)
                    .map(|j| ColumnFormat {
                        pre: " ",
                        width: table
                            .iter()
                            .map(|row| row[j].text.len().max(1))
                            .max()
                            .unwrap(),
                        post: if j == 0 { " │" } else { " " },
                    })
                    .collect::<Vec<_>>();
                for (i, row) in table.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{GRAY}")?;
                    }
                    for (&ColumnFormat { pre, width, post }, Cell { text, align }) in
                        column_format.iter().zip(row)
                    {
                        write!(f, "{pre}")?;
                        match align {
                            Align::Left => write!(f, "{text:<width$}")?,
                            Align::Center => write!(f, "{text:^width$}")?,
                            Align::Right => write!(f, "{text:>width$}")?,
                        }
                        write!(f, "{post}")?;
                    }
                    if i == 0 {
                        write!(f, "{RESET}")?;
                    }
                    writeln!(f)?;
                }
                Ok(())
            }
        }
    }
    mod vec2 {
        use crate::lg::align_of;
        use crate::lg::format;
        use crate::lg::table::Align;
        use crate::lg::table::Cell;
        use crate::lg::table::Table;
        use std::fmt;
        use std::iter;
        pub fn vec2<'a, T, R, S>(title: &str, vec2: &'a S) -> Table
        where
            T: fmt::Debug + 'a,
            R: ?Sized,
            &'a R: Copy + IntoIterator<Item = &'a T> + 'a,
            &'a S: Copy + IntoIterator<Item = &'a R>,
        {
            let w = vec2
                .into_iter()
                .map(|row| row.into_iter().count())
                .max()
                .unwrap();
            Table {
                table: iter::once(
                    iter::once(Cell {
                        text: title.to_string(),
                        align: Align::Left,
                    })
                    .chain((0..w).map(|i| Cell {
                        text: i.to_string(),
                        align: Align::Center,
                    }))
                    .collect(),
                )
                .chain(vec2.into_iter().enumerate().map(|(j, row)| {
                    iter::once(Cell {
                        text: j.to_string(),
                        align: Align::Center,
                    })
                    .chain(row.into_iter().map(|v| {
                        let v = format(&v);
                        Cell {
                            align: align_of(&v),
                            text: v,
                        }
                    }))
                    .chain(iter::repeat_with(|| Cell {
                        text: String::new(),
                        align: Align::Left,
                    }))
                    .take(1 + w)
                    .collect()
                }))
                .collect(),
            }
        }
    }
    mod vecs {
        use super::table::Cell;
        use super::table::Table;
        use crate::lg::align_of;
        use crate::lg::table::Align;
        use std::iter;
        pub fn hvec(vecs: &[(String, Vec<String>)]) -> Table {
            let w = vecs.iter().map(|(_, row)| row.len()).max().unwrap();
            Table {
                table: iter::once(
                    iter::once(Cell {
                        text: String::new(),
                        align: Align::Left,
                    })
                    .chain((0..w).map(|i| Cell {
                        text: i.to_string(),
                        align: Align::Center,
                    }))
                    .collect(),
                )
                .chain(vecs.iter().map(|(title, row)| {
                    iter::once(Cell {
                        text: title.to_string(),
                        align: Align::Center,
                    })
                    .chain(row.iter().map(|v| Cell {
                        align: align_of(v),
                        text: v.clone(),
                    }))
                    .chain(iter::repeat_with(|| Cell {
                        text: String::new(),
                        align: Align::Left,
                    }))
                    .take(1 + w)
                    .collect()
                }))
                .collect(),
            }
        }
        pub fn vvec(vecs: &[(String, Vec<String>)]) -> Table {
            let h = vecs.iter().map(|(_, col)| col.len()).max().unwrap();
            Table {
                table: iter::once(
                    iter::once(Cell {
                        text: String::new(),
                        align: Align::Center,
                    })
                    .chain(vecs.iter().map(|(title, _)| Cell {
                        text: title.to_string(),
                        align: Align::Center,
                    }))
                    .collect(),
                )
                .chain((0..h).map(|i| {
                    iter::once(Cell {
                        text: i.to_string(),
                        align: Align::Center,
                    })
                    .chain(vecs.iter().map(|(_, vec)| {
                        let v = vec.get(i).map_or("", String::as_str);
                        Cell {
                            align: align_of(v),
                            text: v.to_string(),
                        }
                    }))
                    .collect()
                }))
                .collect(),
            }
        }
    }
    pub use map::hmap;
    pub use map::vmap;
    use std::borrow::Borrow;
    use std::fmt;
    use table::Align;
    pub use vec2::vec2;
    pub use vecs::hvec;
    pub use vecs::vvec;
    pub fn bools<B, I>(iter: I) -> String
    where
        B: Borrow<bool>,
        I: IntoIterator<Item = B>,
    {
        format!(
            "[{}]",
            iter.into_iter()
                .map(|b| ['.', '#'][usize::from(*(b.borrow()))])
                .collect::<String>(),
        )
    }
    pub fn align_of(s: &str) -> Align {
        // To improve this: https://doc.rust-lang.org/reference/tokens.html#floating-point-literals
        match s.parse::<f64>() {
            Ok(_) => Align::Right,
            Err(_) => Align::Left,
        }
    }
    #[macro_export]
    macro_rules! lg {
        (@contents $head:expr $(, $tail:expr)*) => {{
            $crate::__lg_internal!($head);
            $(
                eprint!(",");
                $crate::__lg_internal!($tail);
            )*
            eprintln!();
        }};
        ($($expr:expr),* $(,)?) => {{
            eprint!("{} \u{276f}", line!());
            $crate::lg!(@contents $($expr),*)
        }};
    }
    #[doc(hidden)]
    #[macro_export]
    macro_rules! __lg_internal {
        ($value:expr) => {{
            match $value {
                head => {
                    eprint!(" {} = {}", stringify!($value), $crate::lg::format(&head));
                }
            }
        }};
    }
    #[macro_export]
    macro_rules! table {
        ($vec2:expr) => {
            eprint!(
                "{}",
                $crate::lg::vec2($crate::lg::remove_ampersand(stringify!($vec2)), $vec2)
            );
        };
    }
    #[macro_export]
    macro_rules! vmap {
        ($map:expr) => {
            eprint!(
                "{}",
                $crate::lg::vmap($crate::lg::remove_ampersand(stringify!($map)), $map)
            );
        };
    }
    #[macro_export]
    macro_rules! hmap {
        ($map:expr) => {
            eprint!(
                "{}",
                $crate::lg::hmap($crate::lg::remove_ampersand(stringify!($map)), $map)
            );
        };
    }
    #[macro_export]
    macro_rules! vvec {
        ($($(@field $field:ident)* $vecs:expr),+ $(,)?) => {
            let mut vecs = Vec::new();
            $(
                let name = $crate::lg::remove_ampersand(stringify!($vecs));
                #[allow(unused_mut, unused_assignments)]
                let mut has_field = false;
                $(
                    #[allow(unused_mut, unused_assignments)]
                    {
                        let mut name = name.to_owned();
                        has_field = true;
                        name.push_str(".");
                        name.push_str(stringify!($field));
                        let values = (&$vecs).into_iter().map(|v| $crate::lg::format(&v.$field)).collect::<Vec<_>>();
                        vecs.push((name, values))
                    }
                )*
                if !has_field {
                    let values = (&$vecs).into_iter().map(|v| $crate::lg::format(&v)).collect::<Vec<_>>();
                    vecs.push((name.to_owned(), values))
                }
            )+
            eprint!("{}", $crate::lg::vvec(&vecs));
        };
    }
    #[macro_export]
    macro_rules! hvec {
        ($($(@field $field:ident)* $vecs:expr),+ $(,)?) => {
            let mut vecs = Vec::new();
            $(
                let name = $crate::lg::remove_ampersand(stringify!($vecs));
                #[allow(unused_mut, unused_assignments)]
                let mut has_field = false;
                $(
                    #[allow(unused_mut, unused_assignments)]
                    {
                        let mut name = name.to_owned();
                        has_field = true;
                        name.push_str(".");
                        name.push_str(stringify!($field));
                        let values = (&$vecs).into_iter().map(|v| $crate::lg::format(&v.$field)).collect::<Vec<_>>();
                        vecs.push((name, values))
                    }
                )*
                if !has_field {
                    let values = (&$vecs).into_iter().map(|v| $crate::lg::format(&v)).collect::<Vec<_>>();
                    vecs.push((name.to_owned(), values))
                }
            )+
            eprint!("{}", $crate::lg::hvec(&vecs));
        };
    }
    pub fn remove_ampersand(mut s: &str) -> &str {
        while let Some(t) = s.strip_prefix('&') {
            s = t;
        }
        s
    }
    pub fn format<T: fmt::Debug>(t: &T) -> String {
        let s = format!("{t:?}")
            .replace("340282366920938463463374607431768211455", "*") // u128
            .replace("170141183460469231731687303715884105727", "*") // i128
            .replace("18446744073709551615", "*") // u64
            .replace("9223372036854775807", "*") // i64
            .replace("-9223372036854775808", "*") // i64
            .replace("4294967295", "*") // u32
            .replace("2147483647", "*") // i32
            .replace("-2147483648", "*") // i32
            .replace("None", "*")
            .replace("true", "#")
            .replace("false", ".");
        let mut s = s.as_str();
        while s.starts_with("Some(") {
            s = s.strip_prefix("Some(").unwrap();
            s = s.strip_suffix(')').unwrap();
        }
        while s.len() > 2 && s.starts_with('"') && s.ends_with('"') {
            s = s.strip_prefix('"').unwrap();
            s = s.strip_suffix('"').unwrap();
        }
        s.to_owned()
    }
}
// }}}
