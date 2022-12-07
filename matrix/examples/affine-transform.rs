// https://atcoder.jp/contests/abc189/tasks/abc189_e
use matrix::AffineTransformation;
use proconio::input;

fn main() {
    input! {n: usize, p: [(i64, i64); n], m: usize}

    let mut op = vec![AffineTransformation::<i64>::new()];
    for _ in 0..m {
        input! {t: usize}
        let last = (*op.last().unwrap()).clone();
        if t == 1 {
            op.push(last.rotate_clockwise());
        } else if t == 2 {
            op.push(last.rotate_counterclockwise());
        } else if t == 3 {
            input! {p: i64}
            let nop = last.translation(-p, 0).reflection(true, false).translation(p, 0);
            op.push(nop);
        } else {
            input! {p: i64}
            let nop = last.translation(0, -p).reflection(false, true).translation(0, p);
            op.push(nop);
        }
    }

    input! {q: usize, q: [(usize, usize); q]}

    for (a, b) in q {
        let (x, y) = p[b - 1];
        let nop = &op[a];
        let (nx, ny) = nop.transform(x, y);

        println!("{} {}", nx, ny);
    }
}
