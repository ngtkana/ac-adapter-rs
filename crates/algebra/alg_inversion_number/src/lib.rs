use alg_traits::{Assoc, Identity};

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct InversionValue {
    pub zeros: u64,
    pub ones: u64,
    pub inversion: u64,
}
impl InversionValue {
    pub fn from_bool(src: bool) -> Self {
        match src {
            false => InversionValue {
                zeros: 1,
                ones: 0,
                inversion: 0,
            },
            true => InversionValue {
                zeros: 0,
                ones: 1,
                inversion: 0,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct InversionMerge {}
impl Assoc for InversionMerge {
    type Value = InversionValue;
    fn op(lhs: InversionValue, rhs: InversionValue) -> InversionValue {
        InversionValue {
            zeros: lhs.zeros + rhs.zeros,
            ones: lhs.ones + rhs.ones,
            inversion: lhs.inversion + rhs.inversion + lhs.ones * rhs.zeros,
        }
    }
}
impl Identity for InversionMerge {
    fn identity() -> InversionValue {
        InversionValue {
            zeros: 0,
            ones: 0,
            inversion: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;

    #[test]
    fn test_identity() {
        assert_eq!(
            InversionMerge::identity(),
            InversionValue {
                zeros: 0,
                ones: 0,
                inversion: 0,
            }
        );
    }

    #[test_case("" => (0, 0, 0))]
    #[test_case("0" => (1, 0, 0))]
    #[test_case("1" => (0, 1, 0))]
    #[test_case("00" => (2, 0, 0))]
    #[test_case("01" => (1, 1, 0))]
    #[test_case("10" => (1, 1, 1))]
    #[test_case("11" => (0, 2, 0))]
    #[test_case("010010" => (4, 2, 4))]
    #[test_case("101101" => (2, 4, 4))]
    fn test_aggr(src: &str) -> (u64, u64, u64) {
        let InversionValue {
            zeros,
            ones,
            inversion,
        } = src
            .chars()
            .map(|c| match c {
                '0' => false,
                '1' => true,
                _ => panic!(),
            })
            .map(InversionValue::from_bool)
            .fold(InversionMerge::identity(), InversionMerge::op);
        (zeros, ones, inversion)
    }
}
