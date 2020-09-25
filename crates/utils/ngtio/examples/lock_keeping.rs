use ngtio::prelude::*;

fn main() {
    let mut buf = LockKeeping::new().tokenizer();
    loop {
        let token = buf.token();
        println!("Token: {}", token);
    }
}
