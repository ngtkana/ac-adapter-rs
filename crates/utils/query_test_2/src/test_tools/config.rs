#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Config {
    pub pre: Option<Pre>,
    pub initialize: Initizlize,
    pub passing: Checked,
    pub failing: Checked,
    pub unchecked: Unchecked,
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Initizlize {
    Short,
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Pre {
    Short,
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Checked {
    Verbose,
    Short,
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Unchecked {
    Verbose,
    Short,
}
