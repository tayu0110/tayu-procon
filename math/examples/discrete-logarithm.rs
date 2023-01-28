// https://judge.yosupo.jp/problem/discrete_logarithm_mod
use iolib::scan;
use math::mod_log_with_lower_bound_constraint;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(t: usize);

    for _ in 0..t {
        scan!(x: i64, y: i64, m: i64);

        if let Some(res) = mod_log_with_lower_bound_constraint(x, y, m, 0) {
            writeln!(out, "{}", res).unwrap();
        } else {
            writeln!(out, "-1").unwrap();
        }
    }
}
