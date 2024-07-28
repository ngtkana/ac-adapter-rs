mod map;
mod table;
mod vec2;
mod vecs;

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
                eprint!(" {} = {}", stringify!($value), $crate::format(&head));
            }
        }
    }};
}

#[macro_export]
macro_rules! table {
    ($vec2:expr) => {
        eprintln!(
            "{}",
            $crate::vec2($crate::remove_ampersand(stringify!($vec2)), $vec2)
        );
    };
}

#[macro_export]
macro_rules! vmap {
    ($map:expr) => {
        eprintln!(
            "{}",
            $crate::vmap($crate::remove_ampersand(stringify!($map)), $map)
        );
    };
}

#[macro_export]
macro_rules! hmap {
    ($map:expr) => {
        eprintln!(
            "{}",
            $crate::hmap($crate::remove_ampersand(stringify!($map)), $map)
        );
    };
}

#[macro_export]
macro_rules! vvec {
    ($($(@field $field:ident)* $vecs:expr),+ $(,)?) => {
        let mut vecs = Vec::new();
        $(
            let name = $crate::remove_ampersand(stringify!($vecs));
            #[allow(unused_mut, unused_assignments)]
            let mut has_field = false;
            $(
                #[allow(unused_mut, unused_assignments)]
                {
                    let mut name = name.to_owned();
                    has_field = true;
                    name.push_str(".");
                    name.push_str(stringify!($field));
                    let values = (&$vecs).into_iter().map(|v| $crate::format(&v.$field)).collect::<Vec<_>>();
                    vecs.push((name, values))
                }
            )*
            if !has_field {
                let values = (&$vecs).into_iter().map(|v| $crate::format(&v)).collect::<Vec<_>>();
                vecs.push((name.to_owned(), values))
            }
        )+
        eprintln!("{}", $crate::vvec(&vecs));
    };
}

#[macro_export]
macro_rules! hvec {
    ($($(@field $field:ident)* $vecs:expr),+ $(,)?) => {
        let mut vecs = Vec::new();
        $(
            let name = $crate::remove_ampersand(stringify!($vecs));
            #[allow(unused_mut, unused_assignments)]
            let mut has_field = false;
            $(
                #[allow(unused_mut, unused_assignments)]
                {
                    let mut name = name.to_owned();
                    has_field = true;
                    name.push_str(".");
                    name.push_str(stringify!($field));
                    let values = (&$vecs).into_iter().map(|v| $crate::format(&v.$field)).collect::<Vec<_>>();
                    vecs.push((name, values))
                }
            )*
            if !has_field {
                let values = (&$vecs).into_iter().map(|v| $crate::format(&v)).collect::<Vec<_>>();
                vecs.push((name.to_owned(), values))
            }
        )+
        eprintln!("{}", $crate::hvec(&vecs));
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

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::BTreeSet;
    use std::iter::empty;

    #[test]
    fn test_macro_invocation() {
        vmap!(&[(0, 0)]);
        hmap!(&[(0, 0)]);
        hvec!(&[0]);
        hvec!(&[0], &["a", "b"]);
        vvec!(&[0]);
        vvec!(&[0], &["a", "b"]);
        lg!(4);

        let a = [0..3, 4..6];
        hvec!(&a);
        hvec!(
            &a,
            @field start @field end &a,
            @field start &a,
            @field end &a,
        );
        vvec!(&a);
        vvec!(
            @field start &a,
            @field end &a,
        );
    }

    #[test]
    fn test_bools_format() {
        assert_eq!(bools([false]).as_str(), "[.]");
        assert_eq!(bools([true]).as_str(), "[#]");
        assert_eq!(bools([false, true]).as_str(), "[.#]");
        assert_eq!(bools([true, false]).as_str(), "[#.]");
    }

    #[test]
    fn test_bools_generics() {
        assert_eq!(bools(<[bool; 0]>::default()).as_str(), "[]");
        assert_eq!(bools(<[bool; 0]>::default()).as_str(), "[]");
        assert_eq!(bools(<[&bool; 0]>::default()).as_str(), "[]");
        assert_eq!(bools(<[bool; 0]>::default().as_slice()).as_str(), "[]");
        assert_eq!(bools(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<&bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<&mut bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(BTreeSet::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(empty::<bool>()).as_str(), "[]");
        assert_eq!(bools(empty::<bool>()).as_str(), "[]");
        assert_eq!(bools(empty::<&bool>()).as_str(), "[]");
        assert_eq!(bools(empty::<&bool>()).as_str(), "[]");
    }
}
