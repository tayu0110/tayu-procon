// https://judge.yosupo.jp/problem/double_ended_priority_queue
use cpio::{putln, scan};
use ds::IntervalHeap;

fn main() {
    scan!(n: usize, q: usize, s: [i32; n]);

    let mut nt = IntervalHeap::from_vec(s);

    for _ in 0..q {
        scan!(ty: u8);
        if ty == 0 {
            scan!(x: i32);
            nt.push(x);
        } else if ty == 1 {
            putln!(nt.pop_min().unwrap());
        } else {
            putln!(nt.pop_max().unwrap());
        }
    }
}
