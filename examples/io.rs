use tayu_procon::{
    scan
};

fn main() {
    scan!(n: usize, v: [i64; n]);

    for w in v {
        println!("{}", w);
    }
}