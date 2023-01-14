// https://judge.yosupo.jp/problem/many_aplusb
use iolib::scan;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    scan!(t: usize);

    for _ in 0..t {
        scan!(a: usize, b: usize);
        writeln!(stdout, "{}", a + b).ok();
    }
}
