use iolib::scan;
use string::zalgorithm;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());
    scan!(s: String);

    let res = zalgorithm(s);
    write!(stdout, "{}", res[0]).unwrap();
    for res in res.into_iter().skip(1) {
        write!(stdout, " {}", res).unwrap();
    }
    writeln!(stdout, "").unwrap();
}
