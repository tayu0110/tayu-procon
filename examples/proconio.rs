use proconio::input;

fn main() {
    input! {n: usize, z: [(i64, i64); n]};

    for (w, v) in z {
        println!("{} {}", w, v);
    }
}
