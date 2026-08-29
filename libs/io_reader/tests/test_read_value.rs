use io_reader::{Char, Source, Str, U32, read_value};

#[test]
fn test_read_value() {
    let mut source = Source::from("a  12\n bcd");
    assert_eq!(read_value! { @from [&mut source] Char }, 'a');
    assert_eq!(read_value! { @from [&mut source] U32 }, 12);
    assert_eq!(read_value! { @from [&mut source] Str }, "bcd");
}
