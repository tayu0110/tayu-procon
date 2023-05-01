// https://judge.yosupo.jp/problem/many_aplusb
use iolib::{putln, scan};

fn main() {
    scan!(t: usize);

    let tm = std::time::SystemTime::now();

    let mut read_time = 0;
    let mut write_time = 0;
    for _ in 0..t {
        let s = tm.elapsed().unwrap().as_micros();
        scan!(a: usize, b: usize);
        let t = tm.elapsed().unwrap().as_micros();
        putln!(a + b);
        let u = tm.elapsed().unwrap().as_micros();

        read_time += t - s;
        write_time += u - t;
    }

    eprintln!("{}", read_time);
    eprintln!("{}", write_time);
}
