use rand::{self, Rng};
use std::io::Write;

fn main() {
    let file = std::fs::File::create("./input.txt").unwrap();
    let mut file = std::io::BufWriter::new(file);
    let mut rng = rand::thread_rng();

    const N: usize = 1000_000_0;
    writeln!(file, "{}", N).unwrap();

    for _ in 0..N {
        let (w, v): (i64, i64) = (rng.gen(), rng.gen());

        writeln!(file, "{} {}", w, v).unwrap();
    }
}