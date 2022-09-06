use rand::{self, Rng};
use std::io::Write;

fn main() {
    let mut file = std::fs::File::create("./big_input_file.txt").unwrap();
    let mut rng = rand::thread_rng();

    const N: usize = 10_000_000;

    writeln!(file, "{}", N).unwrap();

    for _ in 0..N {
        writeln!(file, "{}", rng.gen::<i64>()).unwrap();
    }
}