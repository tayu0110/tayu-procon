use tayu_procon::scani;

fn main() {
    scani!(n: usize, z: [[(i64, i64); 2]; n]);

    for w in z {
        println!("{:?}", w);
    }
}
