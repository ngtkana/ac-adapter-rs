fn main() {
    let mut buf = ngtio::with_stdin();
    loop {
        let x = buf.u32();
        let y = buf.u32();
        println!("{} + {} = {}", x, y, x + y);
    }
}
