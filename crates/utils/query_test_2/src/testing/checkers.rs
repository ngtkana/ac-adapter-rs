use crate::config;
use std::fmt::{Debug, Display};
use yansi::{Color, Paint};

const INIT_FG_COLOR: Color = Color::Green;
const PRE_FG_COLOR: Color = Color::Black;
const UNCHECKED_FG_COLOR: Color = Color::Black;
const FAILING_FG_COLOR: Color = Color::Red;
const PASSING_FG_COLOR: Color = Color::Green;
const BRUTE_FG_COLOR: Color = Color::Blue;
const FAST_FG_COLOR: Color = Color::Yellow;
const QUERY_FG_COLOR: Color = Color::Magenta;
const EXPECTED_FG_COLOR: Color = Color::Blue;
const RESULT_FG_COLOR: Color = Color::Yellow;

fn paint_init() -> Paint<&'static str> {
    Paint::new("Initialized an instance")
        .fg(INIT_FG_COLOR)
        .bold()
}
fn paint_pre() -> Paint<&'static str> {
    Paint::new("Preparing for").fg(PRE_FG_COLOR).bold()
}
fn paint_unchecked() -> Paint<&'static str> {
    Paint::new("Unchecked").fg(UNCHECKED_FG_COLOR).bold()
}
fn paint_failing() -> Paint<&'static str> {
    Paint::new("Test failed!").fg(FAILING_FG_COLOR).bold()
}
fn paint_passing() -> Paint<&'static str> {
    Paint::new("Passing").fg(PASSING_FG_COLOR).bold()
}
fn paint_brute() -> Paint<&'static str> {
    Paint::new("Brute").fg(BRUTE_FG_COLOR).bold()
}
fn paint_fast() -> Paint<&'static str> {
    Paint::new("Fast").fg(FAST_FG_COLOR).bold()
}
fn paint_query() -> Paint<&'static str> {
    Paint::new("Query").fg(QUERY_FG_COLOR).bold()
}
fn paint_expected() -> Paint<&'static str> {
    Paint::new("Expected").fg(EXPECTED_FG_COLOR).bold()
}
fn paint_result() -> Paint<&'static str> {
    Paint::new("Result").fg(RESULT_FG_COLOR).bold()
}
trait Colon {
    fn colon<U: std::fmt::Debug>(&self, u: U) -> String;
}
impl<T: Display> Colon for Paint<T> {
    fn colon<U: Debug>(&self, u: U) -> String {
        format!("{}: {:?}", self, &u)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Status {
    Failing,
    Passing,
}

pub(super) struct InitPrinter<B, F> {
    pub(super) brute: B,
    pub(super) fast: F,
}
impl<B, F> InitPrinter<B, F>
where
    B: Debug,
    F: Debug,
{
    pub fn print(&self, unchecked: config::Initizlize) {
        use config::Initizlize::*;
        match unchecked {
            Short => self.short(),
        }
    }
    fn short(&self) {
        println!();
        println!("{}", paint_init());
        println!("\t{brute}", brute = paint_brute().colon(&self.brute));
        println!("\t{fast}", fast = paint_fast().colon(&self.fast),);
        println!();
    }
}

#[allow(dead_code)]
pub(super) struct Preprinter<B, F, Q> {
    pub(super) brute: B,
    pub(super) fast: F,
    pub(super) query_name: &'static str,
    pub(super) param: Q,
}
impl<B, F, Q> Preprinter<B, F, Q>
where
    B: Debug,
    F: Debug,
    Q: Debug,
{
    pub fn preprint(&self, pre: config::Pre) {
        use config::Pre::*;
        match pre {
            Short => self.short(),
        }
    }
    fn short(&self) {
        print!(
            "{}",
            paint_pre().colon(format!("({} {:?})", self.query_name, self.param))
        );
        println!();
    }
}

pub(super) struct Checker<B, F, Q, O> {
    pub(super) brute: B,
    pub(super) fast: F,
    pub(super) query_name: &'static str,
    pub(super) param: Q,
    pub(super) expected: O,
    pub(super) result: O,
}
impl<B, F, Q, O> Checker<B, F, Q, O>
where
    B: Debug,
    F: Debug,
    Q: Debug,
    O: Debug + PartialEq,
{
    pub fn check(&self, config: config::Config) {
        if self.expected != self.result {
            use config::Checked::*;
            match config.failing {
                Verbose => self.verbose(Status::Failing),
                Short => self.short(),
            }
            panic!("Failed in a test.");
        } else {
            use config::Checked::*;
            match config.passing {
                Verbose => self.verbose(Status::Passing),
                Short => self.short(),
            }
        }
    }
    fn print_status(status: Status) {
        use Status::*;
        match status {
            Failing => println!("{}", paint_failing()),
            Passing => println!("{}", paint_passing()),
        }
    }
    fn short(&self) {
        println!(
            "{query}\t{expected}\t{result}",
            query = paint_query().colon((self.query_name, &self.param)),
            expected = paint_expected().colon(&self.expected),
            result = paint_result().colon(&self.result)
        );
    }
    fn verbose(&self, status: Status) {
        Self::print_status(status);
        self.short();
        println!("\t{}", paint_brute().colon(&self.brute));
        println!("\t{}", paint_fast().colon(&self.fast));
        println!();
    }
}

pub(super) struct UnChecker<B, F, Q> {
    pub(super) brute: B,
    pub(super) fast: F,
    pub(super) query_name: &'static str,
    pub(super) param: Q,
}
impl<B, F, Q> UnChecker<B, F, Q>
where
    B: Debug,
    F: Debug,
    Q: Debug,
{
    pub fn uncheck(&self, unchecked: config::Unchecked) {
        use config::Unchecked::*;
        match unchecked {
            Verbose => self.verbose(),
            Short => self.short(),
        }
    }
    fn short(&self) {
        println!(
            "{query}",
            query = paint_query().colon((self.query_name, &self.param)),
        );
    }
    fn verbose(&self) {
        print!("{}\t", paint_unchecked());
        println!(
            "{query}\t{brute}\t{fast}",
            query = paint_query().colon((self.query_name, &self.param)),
            brute = paint_brute().colon(&self.brute),
            fast = paint_fast().colon(&self.fast),
        );
    }
}
