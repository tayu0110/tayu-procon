use tayu_procon::{
    scan
};

fn main() {
    scan!(n: usize, z: [[[i64; 10]; 10]; n / 100]);

    for w in z {
        println!("{:?}", w);
    }
}