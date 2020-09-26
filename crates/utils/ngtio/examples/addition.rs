use ngtio::prelude::*;

fn main() {
    let mut buf = reader();
    loop {
        let x = buf.u32();
        let y = buf.u32();
        println!("{} + {} = {}", x, y, x + y);
    }
}
