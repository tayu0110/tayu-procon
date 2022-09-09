use tayu_procon::{
    scani
};

fn main() {
    scani!(n: usize, v: [i64; n]);

    for w in v {
        println!("{}", w);
    }
}