use io_reader::{Str, U32, Usize, Usize1, Vector, input};

#[test]
fn test_read_bind() {
    input! {
        from "42 abc",
        x = U32,
        s = Str,
    }
    assert_eq!(x, 42);
    assert_eq!(s, "abc");
}

#[test]
fn test_mutability() {
    input! {
        from "5 10 11 12 13 14 5 4",
        n = Usize,
        mut a = Vector(U32, n),
        i = Usize1,
        x = U32,
    }
    a[i] += x;
    assert_eq!(a, [10, 11, 12, 13, 18]);
}
