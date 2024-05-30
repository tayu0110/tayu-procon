// https://yukicoder.me/problems/447
use cpio::*;
use math::MathInt;

fn main() {
    scan!(x1: u64, y1: u64, x2: u64, y2: u64, x3: u64, y3: u64);

    if let Some(Some((res, lcm))) = x1.crt(y1, x2, y2).map(|(c, lcm)| c.crt(lcm, x3, y3)) {
        if res == 0 {
            putln!(lcm);
        } else {
            putln!(res);
        }
    } else {
        putln!(-1);
    }
}
