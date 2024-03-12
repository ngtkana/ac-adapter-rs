//! Provides a macro [`lg`] and formatting utils.
use std::borrow::Borrow;
use std::fmt;
use std::iter::once;

/// Print the values with the line number.
///
/// # Examples
///
/// ```rust
/// # use lg::*;
/// let x = 42;
/// let y = 43;
/// lg!(x);
/// lg!(x, y);
/// lg!(42, x, 43, y);
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
        eprint!("{}\u{276f}", line!());
        $crate::lg!(@contents $($expr),*)
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __lg_internal {
    ($value:expr) => {{
        match $value {
            head => {
                eprint!(
                    " {} = {}",
                    stringify!($value),
                    $crate::__quiet(format!("{:?}", &head))
                );
            }
        }
    }};
}

/// Print many 1D arrays side-by-side with the line number.
///
/// # Examples
/// ```rust
/// # use lg::*;
/// let a = [1, 2, 3];
/// let b = [4, 5, 6];
/// let c = [7, 8, 9];
/// rows! {
///   "id", // the name of the index
///   @"a" => a,
///   b,
///   @"c" => c,
/// }
/// ```
#[macro_export]
macro_rules! rows {
    {
        $index_label:literal,
        $(@offset $offset:expr,)?
        $(@verticalbar $verticalbar:expr,)*
        $($(@$label:literal =>)? $values:expr),* $(,)?
    } => {{
        #![allow(unused_assignments)]
        let mut rows = $crate::Rows::default();
        rows.line_number(line!());
        $(rows.offset($offset);)?
        $(rows.verticalbar($verticalbar);)*
        rows.index_label($index_label);
        $({
            let mut label = stringify!($values).to_string();
            if label.starts_with("&") {
                label = label[1..].to_string();
            }
            $({
                let label_: &'static str = $label;
                label = label_.to_string();
            })?
            rows.row(label, $values);
        })*
        eprintln!("{}", rows.to_string_table());
    }};
}

/// Print the 2D array with the line number.
///
/// # Examples
/// ```rust
/// # use lg::*;
/// let a = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
/// table! {
///    @"a" => a,
/// }
/// table! {
///   a,
/// }
/// ```
#[macro_export]
macro_rules! table {
    {
        $(@$name:literal => )? $values:expr $(,)?
    } => {{
        #![allow(unused_assignments)]
        let mut name = stringify!($values).to_string();
        if name.starts_with("&") {
            name = name[1..].to_string();
        }
        $({
            let name_: &'static str = $name;
            name = name_.to_string();
        })?
        let mut rows = $crate::Rows::default();
        rows.line_number(line!());
        rows.table_name(name);
        #[allow(array_into_iter)]
        for (i, row) in $values.into_iter().enumerate() {
            rows.row(i.to_string(), row);
        }
        eprintln!("{}", rows.to_string_table());
    }};
}

#[doc(hidden)]
pub fn __quiet(s: impl AsRef<str>) -> String {
    s.as_ref()
        .replace("340282366920938463463374607431768211455", "*") // u128
        .replace("170141183460469231731687303715884105727", "*") // i128
        .replace("18446744073709551615", "*") // u64
        .replace("9223372036854775807", "*") // i64
        .replace("-9223372036854775808", "*") // i64
        .replace("4294967295", "*") // u32
        .replace("2147483647", "*") // i32
        .replace("-2147483648", "*") // i32
        .replace("None", "*")
        .replace("Some", "")
        .replace("true", "#")
        .replace("false", ".")
        .replace(['"', '\''], "")
}

#[doc(hidden)]
#[derive(Default)]
pub struct Rows {
    line_number: String,
    index_label: String,
    offset: usize,
    verticalbars: Vec<usize>,
    table_name: String,
    rows: Vec<Row>,
}
impl Rows {
    pub fn line_number(&mut self, line_number: u32) -> &mut Self {
        self.line_number = format!("{}", line_number);
        self
    }

    pub fn index_label(&mut self, index_label: impl Into<String>) -> &mut Self {
        self.index_label = index_label.into();
        self
    }

    pub fn offset(&mut self, offset: usize) -> &mut Self {
        self.offset = offset;
        self
    }

    pub fn verticalbar(&mut self, verticalbar: impl IntoIterator<Item = usize>) -> &mut Self {
        self.verticalbars.extend(verticalbar);
        self
    }

    pub fn table_name(&mut self, table_name: impl Into<String>) -> &mut Self {
        self.table_name = table_name.into();
        self
    }

    pub fn row(
        &mut self,
        label: impl Into<String>,
        values: impl IntoIterator<Item = impl fmt::Debug>,
    ) -> &mut Self {
        self.rows.push(Row {
            label: label.into(),
            values: values
                .into_iter()
                .map(|value| __quiet(format!("{:?}", value)))
                .collect(),
        });
        self
    }

    pub fn to_string_table(self) -> StringTable {
        let Self {
            line_number,
            index_label,
            offset,
            verticalbars,
            table_name,
            rows,
        } = self;
        let w = rows
            .iter()
            .map(|row| row.values.len())
            .max()
            .unwrap_or_default();
        let mut verticalbar_count = vec![0; w + 1];
        for &v in &verticalbars {
            if (offset..=offset + w).contains(&v) {
                verticalbar_count[v - offset] += 1;
            }
        }

        StringTable {
            head: StringRow {
                label: format!(
                    "{line_number}❯ {table_name}{index_label}",
                    index_label = if index_label.is_empty() {
                        String::new()
                    } else {
                        format!("[{}]", index_label)
                    }
                ),
                values: (offset..offset + w)
                    .map(|index| index.to_string())
                    .collect(),
            },
            body: rows
                .iter()
                .map(|row| StringRow {
                    label: row.label.clone(),
                    values: row.values.clone(),
                })
                .collect(),
            verticalbar_count,
        }
    }
}

struct Row {
    label: String,
    values: Vec<String>,
}

#[doc(hidden)]
pub struct StringTable {
    head: StringRow,
    body: Vec<StringRow>,
    verticalbar_count: Vec<usize>,
}
impl fmt::Display for StringTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            head,
            body,
            verticalbar_count,
        } = self;
        let w = body
            .iter()
            .map(|row| row.values.len())
            .max()
            .unwrap_or_default();
        let label_width = once(head.label.chars().count())
            .chain(body.iter().map(|row| row.label.chars().count()))
            .max()
            .unwrap();
        let value_width = (0..w)
            .map(|j| {
                once(j.to_string().len())
                    .chain(
                        body.iter()
                            .map(|row| row.values.get(j).map_or(0, |s| s.chars().count())),
                    )
                    .max()
                    .unwrap()
            })
            .collect::<Vec<_>>();

        // Heading
        gray(f)?;
        write!(
            f,
            "{}",
            head.to_string(label_width, &value_width, verticalbar_count, true)
        )?;
        resetln(f)?;

        // Body
        for row in body {
            write!(
                f,
                "{}",
                row.to_string(label_width, &value_width, verticalbar_count, false)
            )?;
            writeln!(f)?;
        }
        Ok(())
    }
}

struct StringRow {
    label: String,
    values: Vec<String>,
}
impl StringRow {
    fn to_string(
        &self,
        label_width: usize,
        value_width: &[usize],
        varticalbars_count: &[usize],
        label_align_left: bool,
    ) -> String {
        let Self { label, values } = self;
        let w = value_width.len();
        let mut s = String::new();
        s.push_str(&if label_align_left {
            format!("{label:<label_width$} |")
        } else {
            format!("{label:^label_width$} |")
        });
        for j in 0..w {
            let value_width = value_width[j];
            s.push_str("|".repeat(varticalbars_count[j]).as_str());
            if varticalbars_count[j] == 0 && j != 0 && value_width <= 1 {
                s.push(' ');
            }
            match values.get(j) {
                Some(value) => {
                    s.push_str(&format!(" {value:>value_width$}",));
                }
                None => {
                    s.push_str(" ".repeat(value_width + 1).as_str());
                }
            }
        }
        s
    }
}

const GRAY: &str = "\x1b[48;2;127;127;127;37m";
const RESET: &str = "\x1b[0m";

fn gray(f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{GRAY}")
}
fn resetln(f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(f, "{RESET}")
}

/// Format a iterator of [`bool`]s.
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

#[cfg(test)]
mod test {
    use super::*;
    use indoc::indoc;
    use std::collections::BTreeSet;
    use std::collections::HashMap;
    use std::iter::empty;

    #[test]
    fn test_invoke_lg() {
        let x = 42;
        let y = 43;
        lg!(x);
        lg!(x, y);
        lg!(42, x, 43, y);
    }

    #[test]
    fn test_quiet() {
        assert_eq!(__quiet(std::u32::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i32::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i32::MIN.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::u64::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i64::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i64::MIN.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::u128::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i128::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(format!("{:?}", Some(42))).as_str(), "(42)");
        assert_eq!(__quiet(format!("{:?}", None::<i32>)).as_str(), "*");
    }

    macro_rules! assert_fmt_eq {
        ($left:expr, $right:expr $(,)?) => {
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if *left_val != *right_val {
                        panic!(
                            "assertion failed: `(left == right)`\n\nleft:\n{}\nright:\n{}\n",
                            *left_val, *right_val
                        )
                    }
                }
            }
        };
    }

    fn string_table<T: Borrow<[&'static str]>>(table: &[T]) -> StringTable {
        let w = table
            .iter()
            .map(|row| row.borrow().len())
            .max()
            .unwrap_or_default();
        StringTable {
            head: StringRow {
                label: table[0].borrow()[0].to_string(),
                values: table[0].borrow()[1..]
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect(),
            },
            body: table[1..]
                .iter()
                .map(|row| StringRow {
                    label: row.borrow()[0].to_string(),
                    values: row.borrow()[1..]
                        .iter()
                        .map(std::string::ToString::to_string)
                        .collect(),
                })
                .collect(),
            verticalbar_count: vec![0; w + 1],
        }
    }

    fn format_table<T: Borrow<[&'static str]>>(table: &[T]) -> String {
        format!("{}", string_table(table))
    }

    #[test]
    fn test_string_table_simple() {
        #[rustfmt::skip]
        let result = format_table(&[
           ["head", "aa", "bb", "cc"],
           ["row1", "11", "22", "33"],
           ["row2", "44", "55", "66"],
        ]);
        let expected = indoc! {"
            \x1b[48;2;127;127;127;37mhead | aa bb cc\x1b[0m
            row1 | 11 22 33
            row2 | 44 55 66
        "};
        assert_fmt_eq!(result, expected);
    }

    #[test]
    fn test_string_table_with_short_value_in_first() {
        #[rustfmt::skip]
        let result = format_table(&[
           ["head", "a", "bb", "cc"],
           ["row1", "1", "22", "33"],
           ["row2", "4", "55", "66"],
        ]);
        let expected = indoc! {"
            \x1b[48;2;127;127;127;37mhead | a bb cc\x1b[0m
            row1 | 1 22 33
            row2 | 4 55 66
        "};
        assert_fmt_eq!(result, expected);
    }

    #[test]
    fn test_string_table_with_short_value_in_middle() {
        #[rustfmt::skip]
        let result = format_table(&[
           ["head", "aa", "b", "cc"],
           ["row1", "11", "2", "33"],
           ["row2", "44", "5", "66"],
        ]);
        let expected = indoc! {"
            \x1b[48;2;127;127;127;37mhead | aa  b cc\x1b[0m
            row1 | 11  2 33
            row2 | 44  5 66
        "};
        assert_fmt_eq!(result, expected);
    }

    #[test]
    fn test_string_table_with_short_row_in_head() {
        #[rustfmt::skip]
        let result = format_table(&[
           vec!["head", "aa", "bb"],
           vec!["row1", "11", "22", "33"],
           vec!["row2", "44", "55", "66"],
        ]);
        let expected = indoc! {"
            \x1b[48;2;127;127;127;37mhead | aa bb   \x1b[0m
            row1 | 11 22 33
            row2 | 44 55 66
        "};
        assert_fmt_eq!(result, expected);
    }

    #[test]
    fn test_string_table_with_short_row_in_middle() {
        #[rustfmt::skip]
        let result = format_table(&[
           vec!["head", "aa", "bb", "cc"],
           vec!["row1", "11", "22", "33"],
           vec!["row2", "44", "55"],
           vec!["row3", "77", "88", "99"],
        ]);
        let expected = indoc! {"
            \x1b[48;2;127;127;127;37mhead | aa bb cc\x1b[0m
            row1 | 11 22 33
            row2 | 44 55   
            row3 | 77 88 99
        "};
        assert_fmt_eq!(result, expected);
    }

    #[test]
    fn test_invoke_rows() {
        rows! {
            "i",
            @"a" => [1, 2, 3],
            @"b" => [4, 5, 6],
            @"c" => [7, 8, 9],
        }
    }

    #[test]
    fn test_invoke_rows_with_index() {
        rows! {
            "i",
            @offset 10,
            @"a" => [1, 2, 3],
            @"b" => [4, 5, 6],
            @"c" => [7, 8, 9],
        }
    }

    #[test]
    fn test_invoke_rows_with_various_types() {
        rows! {
            "i",
            @"a" => [1, 2, 3],
            @"b" => BTreeSet::from([4, 5, 6]),
            @"c" => vec![7, 8, 9],
            @"d" => HashMap::from([("x", 10), ("y", 11), ("z", 12)]),
        }
    }

    #[test]
    fn test_invoke_rows_without_name() {
        rows! {
            "index",
            [1, 2, 3],
            @"b" => [4, 5, 6],
            [7, 8, 9],
        }
    }

    #[test]
    fn test_invoke_table() {
        table! {
            @"a" => [
                [1, 2, 3],
                [4, 5, 6],
                [7, 8, 9],
            ]
        }
    }

    #[test]
    fn test_invoke_table_without_name() {
        table! {
            [
                [1, 2, 3],
                [4, 5, 6],
                [7, 8, 9],
            ]
        }
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
