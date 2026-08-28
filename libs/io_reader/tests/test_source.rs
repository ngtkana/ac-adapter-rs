use io_reader::{Array, Bools, Char, Expect, I32, Source, Str, Tuple2, U32, Usize1, Vector, input};

#[test]
fn test_empty() {
    let mut source = Source::from("");
    assert_eq!(source.next_token(), None);
}

#[test]
fn test_tokenize() {
    let mut source = Source::from("a  bc\n de\t f\r\rg");
    let mut result = vec![];
    while let Some(token) = source.next_token() {
        result.push(token.to_string());
    }
    assert_eq!(result, ["a", "bc", "de", "f", "g"]);
}

#[test]
fn test_primitive() {
    let mut source = Source::from("1 2 token -3");
    input! {
        @from [source]
        a: U32,
        b: U32,
        s: Str,
        c: I32,
    }
    assert_eq!(a, 1);
    assert_eq!(b, 2);
    assert_eq!(s, "token");
    assert_eq!(c, -3);
}

#[test]
fn test_usize1() {
    let mut source = Source::from("1 2 3");
    input! {
        @from [source]
        a: Usize1,
        b: Usize1,
        c: Usize1,
    }
    assert_eq!(a, 0);
    assert_eq!(b, 1);
    assert_eq!(c, 2);
}

#[test]
fn test_vector() {
    let mut source = Source::from("1 2 3");
    input! {
        @from [source]
        a: Vector(U32, 3),
    }
    assert_eq!(a, [1, 2, 3]);
}

#[test]
fn test_array() {
    let mut source = Source::from("1 2 3");
    input! {
        @from [source]
        a: Array::<2, _>(U32),
        b: Array::<1, _>(U32),
    }
    assert_eq!(a, [1, 2]);
    assert_eq!(b, [3]);
}

#[test]
fn test_tuple() {
    let mut source = Source::from("10 a four");
    input! {
        @from [source]
        a: Tuple2(U32, Char),
        b: Str,
    }
    assert_eq!(a, (10, 'a'));
    assert_eq!(b, "four");
}

#[test]
fn test_bools() {
    let mut source = Source::from(".#\n#.\n");
    input! {
        @from [source]
        a: Vector(Bools::<'.', '#'>, 2),
    }
    assert_eq!(a, [vec![false, true], vec![true, false]]);
}

#[test]
fn test_expcted() {
    let mut source = Source::from(".#\n#.\n");
    input! {
        @from [source]
        _: Expect(".#"),
        _: Expect("#."),
    }
}
