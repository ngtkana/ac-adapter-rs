pub trait SieveKind {
    type SieveValue: Copy;
    fn new() -> Vec<Self::SieveValue>;
    fn construct(len: usize) -> Vec<Self::SieveValue>;
    fn is_prime(index: usize, b: Self::SieveValue) -> bool;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Boolean {}
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Usize {}

impl SieveKind for Boolean {
    type SieveValue = bool;
    fn new() -> Vec<Self::SieveValue> {
        Vec::new()
    }
    fn construct(len: usize) -> Vec<Self::SieveValue> {
        construct_is_prime_table(len)
    }
    fn is_prime(_index: usize, b: Self::SieveValue) -> bool {
        b
    }
}

impl SieveKind for Usize {
    type SieveValue = usize;
    fn new() -> Vec<Self::SieveValue> {
        Vec::new()
    }
    fn construct(len: usize) -> Vec<Self::SieveValue> {
        construct_least_prime_divisor_table(len)
    }
    fn is_prime(index: usize, b: Self::SieveValue) -> bool {
        index == b
    }
}

pub fn construct_is_prime_table(n: usize) -> Vec<bool> {
    let mut is_prime = vec![true; n];
    (0..2.min(n)).for_each(|i| is_prime[i] = false);
    for p in (2..).take_while(|&p| p * p < n) {
        if !is_prime[p] {
            continue;
        }
        let mut i = p * p;
        while i < n {
            is_prime[i] = false;
            i += p;
        }
    }
    is_prime
}

pub fn construct_least_prime_divisor_table(n: usize) -> Vec<usize> {
    let mut lpd = vec![std::usize::MAX; n];
    for p in 2..n {
        if lpd[p] != std::usize::MAX {
            continue;
        }
        lpd[p] = p;
        let mut i = p * p;
        while i < n {
            lpd[i] = p;
            i += p;
        }
    }
    lpd
}

#[cfg(test)]
mod tests {
    use {super::construct_is_prime_table, test_case::test_case};

    #[test_case(0 => Vec::<bool>::new())]
    #[test_case(1 => vec![false])]
    #[test_case(2 => vec![false, false])]
    #[test_case(3 => vec![false, false, true])]
    #[test_case(4 => vec![false, false, true, true])]
    #[test_case(5 => vec![false, false, true, true, false])]
    fn test_construct_is_prime_table(n: usize) -> Vec<bool> {
        construct_is_prime_table(n)
    }
}
