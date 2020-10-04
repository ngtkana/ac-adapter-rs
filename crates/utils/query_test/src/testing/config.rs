#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Config {
    pub passing: Passing,
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Passing {
    Verbose,
    Short,
}
