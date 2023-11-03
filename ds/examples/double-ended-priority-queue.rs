// https://judge.yosupo.jp/problem/double_ended_priority_queue
use ds::IntervalHeap;
use iolib::{putln, scan};

fn main() {
    scan!(n: usize, q: usize, s: [i32; n]);

    let mut nt = IntervalHeap::from_vec(s);

    // for bug of scan! ...
    if n == 0 {
        scan!(_dum: u32);
    }

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
