use tayu_procon::scan;

fn main() {
    scan!(n: usize, z: [(i64, i64); n]);

    for (w, v) in z {
        println!("{} {}", w, v);
    }
}
