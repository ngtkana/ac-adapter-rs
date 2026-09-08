//! 変数の値を見出し付きで標準エラー出力に出す、競プロ用デバッグユーティリティ。
//!
//! `lg!` は式をそのまま `名前 = 値` の形に整形するだけだが、`table!`/`vmap!`/`hmap!`/`hvec!`/`vvec!` は
//! 2 次元配列やマップを罫線付きの表に組んで出す。見出しには `stringify!` で得たソースコード上の式の文字列を使い、
//! 値は `format` を通す。`format` は `u32::MAX` や `i64::MIN` のような番兵値を `*` に、`bool` を `#`/`.` に
//! 変換するため、「未到達を表す番兵値」や「訪問済みフラグ」の配列を目視でそのまま読める。
//!
//! # 仕様
//!
//! - `lg!`: 複数の式を `行番号 ❯ 式1 = 値1, 式2 = 値2` の形式で 1 行出力
//! - `table!`: 2 次元配列を罫線付きの表として出力
//! - `vmap!` / `hmap!`: マップを縦 / 横の表として出力
//! - `vvec!` / `hvec!`: 複数の `Vec` を並べて縦 / 横の表として出力（`@field` で構造体のフィールドを抽出可能）
//! - `format`: `Debug` 文字列を番兵値・`bool`・`Option`・引用符について整形
//! - `bools`: `bool` の列を `[.#..]` のようなビット列表記に変換
//!
//! # 例
//!
//! ```
//! use lg::lg;
//! let a = 42;
//! let v = vec![1, 2, 3];
//! lg!(a, v);
//! ```

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

/// `bool` の列を `[.#..]` の形式に変換する。真を `#`、偽を `.` で表す。
///
/// # 例
///
/// ```
/// use lg::bools;
/// assert_eq!(bools([true, false, true]), "[#.#]");
/// ```
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

/// 表のセルの寄せ方向を、文字列が数値として解釈できるかで決める。
///
/// 浮動小数点として parse できれば右寄せ、できなければ左寄せにする。数値の列を右揃えで見やすくするための判定。
pub fn align_of(s: &str) -> Align {
    // To improve this: https://doc.rust-lang.org/reference/tokens.html#floating-point-literals
    match s.parse::<f64>() {
        Ok(_) => Align::Right,
        Err(_) => Align::Left,
    }
}

/// 複数の式を評価し、`行番号 ❯ 式1 = 値1, 式2 = 値2` の形式で標準エラー出力に 1 行出す。
///
/// 各値は `format` で整形する。競プロのデバッグで、複数の変数を毎回 `eprintln!` を書かずに確認する用途に使う。
///
/// # 例
///
/// ```
/// use lg::lg;
/// let a = 1;
/// let b = vec![2, 3];
/// lg!(a, b); // 標準エラーに `<行番号> ❯ a = 1, b = [2, 3]` を出力
/// ```
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

/// `lg!` の内部実装。1 個の式を `式 = 値` の形式で出力する。外部から直接使わない。
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

/// 2 次元配列（`Vec<Vec<T>>` など、行の集まりを 2 重にイテレートできる型）を罫線付きの表として標準エラー出力に出す。
///
/// 見出しには式のソース文字列（先頭の `&` は除く）を使い、各セルの値は `format` で整形する。
///
/// # 例
///
/// ```
/// use lg::table;
/// let v = vec![vec![1, 2], vec![3, 4]];
/// table!(&v);
/// ```
#[macro_export]
macro_rules! table {
    ($vec2:expr) => {
        eprint!(
            "{}",
            $crate::vec2($crate::remove_ampersand(stringify!($vec2)), $vec2)
        );
    };
}

/// マップ（`HashMap`, `BTreeMap`, `&[(K, V)]` など）を表にして標準エラー出力に出す。要素ごとに 1 行、`キー | 値` の形式で縦に並べる。
///
/// # 例
///
/// ```
/// use lg::vmap;
/// let m = [(0, "a"), (1, "b")];
/// vmap!(&m);
/// ```
#[macro_export]
macro_rules! vmap {
    ($map:expr) => {
        eprint!(
            "{}",
            $crate::vmap($crate::remove_ampersand(stringify!($map)), $map)
        );
    };
}

/// マップ（`HashMap`, `BTreeMap`, `&[(K, V)]` など）を表にして標準エラー出力に出す。1 行目にキーを、2 行目に値を横に並べる。
///
/// # 例
///
/// ```
/// use lg::hmap;
/// let m = [(0, "a"), (1, "b")];
/// hmap!(&m);
/// ```
#[macro_export]
macro_rules! hmap {
    ($map:expr) => {
        eprint!(
            "{}",
            $crate::hmap($crate::remove_ampersand(stringify!($map)), $map)
        );
    };
}

/// 複数の `Vec`（またはイテレート可能な列）を、それぞれ 1 列とする表にして標準エラー出力に出す。列見出しには式のソース文字列を、行見出しにはインデックスを使う。
///
/// `@field name expr` を前置すると、要素が構造体のときに指定フィールドだけを抽出して列にできる。
///
/// # 例
///
/// ```
/// use lg::vvec;
/// let a = [1, 2, 3];
/// let b = [4, 5, 6];
/// vvec!(&a, &b);
/// ```
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
        eprint!("{}", $crate::vvec(&vecs));
    };
}

/// 複数の `Vec`（またはイテレート可能な列）を、それぞれ 1 行とする表にして標準エラー出力に出す。行見出しには式のソース文字列を、列見出しにはインデックスを使う。
///
/// `@field name expr` を前置すると、要素が構造体のときに指定フィールドだけを抽出して行にできる。
///
/// # 例
///
/// ```
/// use lg::hvec;
/// let a = [1, 2, 3];
/// let b = [4, 5, 6];
/// hvec!(&a, &b);
/// ```
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
        eprint!("{}", $crate::hvec(&vecs));
    };
}

/// 文字列先頭の `&` をすべて取り除く。
///
/// マクロが `stringify!(&&x)` のような参照付きの式を見出しに使う際、表示を `x` に揃えるために使う。
///
/// # 例
///
/// ```
/// use lg::remove_ampersand;
/// assert_eq!(remove_ampersand("&&x"), "x");
/// ```
pub fn remove_ampersand(mut s: &str) -> &str {
    while let Some(t) = s.strip_prefix('&') {
        s = t;
    }
    s
}

/// 値を `Debug` で文字列化し、読みやすく整形する。
///
/// 次の変換を順に適用する。
///
/// - `u32::MAX`, `u64::MAX`, `u128::MAX`, `i32::MIN`/`MAX`, `i64::MIN`/`MAX`, `i128::MAX` を番兵値とみなし `*` に置換
/// - `None` を `*` に、`Some(x)` を `x` に置換（入れ子も再帰的に剥がす）
/// - `true`/`false` を `#`/`.` に置換
/// - 文字列を囲む `"` を除去
///
/// # 例
///
/// ```
/// use lg::format;
/// assert_eq!(format(&Some(3)), "3");
/// assert_eq!(format(&u32::MAX), "*");
/// assert_eq!(format(&true), "#");
/// ```
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
