use iolib::scan;
use wavelet_matrix::WaveletMatrix;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    scan!(n: usize, q: usize, a: [i64; n], p: [(usize, usize, usize); q]);

    let wm = WaveletMatrix::from_vec(&a);

    for (l, r, k) in p {
        writeln!(stdout, "{}", wm.kth_smallest(l, r, k)).unwrap();
    }
}
