// https://judge.yosupo.jp/problem/sort_points_by_argument
use geometry::sort_by_arg_atan2;
use iolib::{putitln, scan};

fn main() {
    scan!(n: usize, p: [(i64, i64); n]);

    let res = sort_by_arg_atan2(p);
    for (x, y) in res {
        putitln!([x, y].into_iter(), sep = ' ');
    }
}
