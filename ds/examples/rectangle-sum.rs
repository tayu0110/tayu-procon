// https://judge.yosupo.jp/problem/rectangle_sum
use ds::StaticRectangleSum;
use iolib::*;

fn main() {
    scan!(n: usize, q: usize, mut points: [(usize, usize, usize); n], queries: [(usize, usize, usize, usize); q]);
    points.sort_unstable();

    let wm = points
        .iter()
        .map(|&(_, y, w)| (y, w))
        .collect::<StaticRectangleSum<usize, usize>>();

    for (l, d, r, u) in queries {
        let (l, r) = (
            points.partition_point(|v| v.0 < l),
            points.partition_point(|v| v.0 < r),
        );
        putln!(wm.sum_of_weight(d..u, l..r));
    }
}
