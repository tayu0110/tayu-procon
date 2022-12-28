use iolib::scan;
use wavelet_matrix::WaveletMatrix;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    scan!(n: usize, q: usize, a: [i64; n]);

    let wm = WaveletMatrix::from_vec(&a);
    for _ in 0..q {
        scan!(l: usize, r: usize, x: i64);
        writeln!(stdout, "{}", wm.range_freq(l, r, x, x + 1)).unwrap();
    }
}
