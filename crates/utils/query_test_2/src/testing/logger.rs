use super::Test;
use crate::{config, Query};
use std::{fmt::Debug, marker::PhantomData};

pub(super) struct Logger<'a, T, Q: Query> {
    pub tester: &'a T,
    pub param: Q::Param,
    pub output: Option<Q::Output>,
    pub expected: Option<Q::Output>,
    pub marker: PhantomData<Q>,
}
impl<'a, T: Test, Q: Query> Logger<'a, T, Q>
where
    Q::Param: Debug + Clone,
    Q::Output: Debug + Clone,
    T::Brute: Debug + Clone,
    T::Fast: Debug + Clone,
{
    pub fn mutate(&self) {
        use config::Passing;
        match self.tester.config().passing {
            Passing::Short => self.mutate_short(),
            Passing::Verbose => self.mutate_verbose(),
        }
    }
    pub fn passing(&self) {
        use config::Passing;
        match self.tester.config().passing {
            Passing::Short => self.passing_short(),
            Passing::Verbose => self.passing_verbose(),
        }
    }
    pub fn failing(&self) {
        use ItemCell::*;
        self.table(vec![
            Vec::new(),
            vec![FailingMsg],
            vec![Query],
            vec![OutputWithExpected],
            vec![Brute],
            vec![Fast],
            Vec::new(),
        ])
        .print();
    }
    fn mutate_short(&self) {
        use ItemCell::*;
        self.table(vec![vec![Query, Brute]]).print();
    }
    fn mutate_verbose(&self) {
        use ItemCell::*;
        self.table(vec![vec![Query], vec![Brute], vec![Fast], Vec::new()])
            .print();
    }
    fn passing_short(&self) {
        use ItemCell::*;
        self.table(vec![vec![Query, Output]]).print();
    }
    fn passing_verbose(&self) {
        use ItemCell::*;
        self.table(vec![
            vec![Query],
            vec![OutputWithExpected],
            vec![Brute],
            vec![Fast],
            Vec::new(),
        ])
        .print();
    }
    fn table(&self, table: Vec<Vec<ItemCell>>) -> items::Table {
        items::Table(
            table
                .into_iter()
                .map(|row| {
                    row.into_iter()
                        .map(|item_cell| self.format(item_cell))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
        )
    }
    fn format(&self, item_cell: ItemCell) -> String {
        use ItemCell::*;
        match item_cell {
            N => String::new(),
            FailingMsg => items::failing_msg(),
            Failing => items::failing(),
            Passing => items::passing(),
            Query => items::query::<Q>(self.param.clone()).to_string(),
            Output => items::output(self.output.as_ref().unwrap().clone()).to_string(),
            Brute => items::brute(self.tester.brute().clone()).to_string(),
            Fast => items::fast(self.tester.fast().clone()).to_string(),
            OutputWithExpected => match self.expected {
                Some(ref expected) => format!(
                    "{} ({})",
                    items::output(self.output.clone()),
                    items::expected(expected.clone())
                ),
                None => items::output(self.output.clone()),
            },
        }
    }
}

#[allow(dead_code)]
enum ItemCell {
    N,
    FailingMsg,
    Failing,
    Passing,
    Query,
    Output,
    Brute,
    Fast,
    OutputWithExpected,
}

mod items {
    use crate::Query;
    use std::fmt::{self, Debug, Display};
    use yansi::{Color, Paint};

    macro_rules! msg_fn {
        ($vis:vis fn $struct_name:ident { name: $item_name:expr, color: $color:expr, } $($tt:tt)*) => {
            $vis fn $struct_name() -> String {
                Paint::new($item_name).fg($color).bold().to_string()
            }
            msg_fn!{$($tt)*}
        };
        () => ();
    }
    macro_rules! item_fn {
        ($vis:vis fn $fn_name:ident { name: $item_name:expr, color: $color:expr, } $($tt:tt)*) => {
            $vis fn $fn_name<T: Debug>(payload: T) -> String {
                Item {
                    name: $item_name,
                    color: $color,
                    payload: format!("{:?}", payload),
                }
                .to_string()
            }
            item_fn!{$($tt)*}
        };
        () => ();
    }
    pub(super) fn query<Q: Query>(payload: Q::Param) -> String
    where
        Q::Param: Debug,
    {
        Item {
            name: "Query",
            color: Color::Magenta,
            payload: format!("{} {:?}", Q::NAME, payload),
        }
        .to_string()
    }
    msg_fn! {
        pub(super) fn failing_msg {
            name: "Failed in a test!",
            color: Color::Red,
        }
        pub(super) fn failing {
            name: "Failing",
            color: Color::Red,
        }
        pub(super) fn passing {
            name: "Passing",
            color: Color::Green,
        }
    }
    item_fn! {
        pub(super) fn output {
            name: "Output",
            color: Color::Blue,
        }
        pub(super) fn expected {
            name: "Expected",
            color: Color::Yellow,
        }
        pub(super) fn fast {
            name: "Fast",
            color: Color::Blue,
        }
        pub(super) fn brute {
            name: "Brute",
            color: Color::Yellow,
        }
    }

    pub(super) struct Item {
        name: &'static str,
        color: Color,
        payload: String,
    }
    impl Display for Item {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "{:>8}: {}",
                Paint::new(self.name).fg(self.color).bold(),
                self.payload
            )
        }
    }
    pub(super) struct Table(pub Vec<Vec<String>>);
    impl Table {
        pub fn print(&self) {
            print!("{}", self);
        }
    }
    impl Display for Table {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            for row in &self.0 {
                let mut ckd = false;
                for item in row {
                    if std::mem::replace(&mut ckd, true) {
                        write!(f, "\t")?;
                    }
                    write!(f, "{}", item)?;
                }
                writeln!(f,)?;
            }
            Ok(())
        }
    }
}
