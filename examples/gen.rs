use rand::{self, Rng};
use std::io::Write;

fn main() {
    let file = std::fs::File::create("./input.txt").unwrap();
    let mut file = std::io::BufWriter::new(file);
    let mut rng = rand::thread_rng();

    const N: usize = 1000;

    for _ in 0..N {
        let c: u8 = rng.gen_range(b'a'..=b'z');
        write!(file, "{}", c as char).unwrap();
    }
    writeln!(file, "").unwrap();
}
