use proconio::{
    input
};

fn main() {
    input! {n: usize, p: [i64; n]};

    for v in p {
        println!("{}", v);
    }
}