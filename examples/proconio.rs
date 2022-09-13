use proconio::{
    input
};

fn main() {
    input! {n: usize, p: [[[i64; 10]; 10]; n / 100]};

    for v in p {
        println!("{:?}", v);
    }
}