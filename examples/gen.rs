use rand::{self, Rng};
use std::io::Write;

fn main() {
    let mut file = std::fs::File::create("./input.txt").unwrap();
    let mut rng = rand::thread_rng();

    const N: usize = 100;

    for _ in 0..N {
        let c: u8 = rng.gen_range(97..123);
        write!(file, "{}", c as char).unwrap();
    }
    writeln!(file, "").unwrap();
}