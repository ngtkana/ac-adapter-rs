use io_reader::{I32, read_bind};

fn main() {
    read_bind! {
        a = I32,
    }
    read_bind! {
        b = I32,
    }
    println!("a={a}, b={b}");
}
