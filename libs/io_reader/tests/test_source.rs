use io_reader::{Array, Bools, Char, I32, Parser, Source, Str, Tuple2, U32, Usize1, Vector};

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
    let a = U32.read(&mut source);
    let b = I32.read(&mut source);
    let s = Str.read(&mut source);
    let c = I32.read(&mut source);
    assert_eq!(a, 1);
    assert_eq!(b, 2);
    assert_eq!(s, "token");
    assert_eq!(c, -3);
}

#[test]
fn test_usize1() {
    let mut source = Source::from("1 2 3");
    let a = Usize1.read(&mut source);
    let b = Usize1.read(&mut source);
    let c = Usize1.read(&mut source);
    assert_eq!(a, 0);
    assert_eq!(b, 1);
    assert_eq!(c, 2);
}

#[test]
fn test_vector() {
    let mut source = Source::from("1 2 3");
    let a = Vector(U32, 3).read(&mut source);
    assert_eq!(a, [1, 2, 3]);
}

#[test]
fn test_array() {
    let mut source = Source::from("1 2 3");
    let a = Array::<2, _>(U32).read(&mut source);
    let b = Array::<1, _>(I32).read(&mut source);
    assert_eq!(a, [1, 2]);
    assert_eq!(b, [3]);
}

#[test]
fn test_tuple() {
    let mut source = Source::from("10 a four");
    let a = Tuple2(U32, Char).read(&mut source);
    let b = Str.read(&mut source);
    assert_eq!(a, (10, 'a'));
    assert_eq!(b, "four");
}

#[test]
fn test_bools() {
    let mut source = Source::from(".#\n#.\n");
    let a = Vector(Bools::<'.', '#'>, 2).read(&mut source);
    assert_eq!(a, [vec![false, true], vec![true, false]]);
}
