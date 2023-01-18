// https://atcoder.jp/contests/abc284/tasks/abc284_f
use iolib::scan;
use string::prepare;

fn main() {
    scan!(n: usize, t: String);

    let rev_t = t.chars().rev().collect::<String>();

    let gen = prepare(2 * n);

    let rh = gen(&t);
    let rev_rh = gen(&rev_t);

    for i in 0..=n {
        let sf_hash = rh.get_hash(0, i);
        let sb_hash = rh.get_hash(i + n, 2 * n);

        let tf_hash = rev_rh.get_hash(n - i, n);
        let tb_hash = rev_rh.get_hash(n, 2 * n - i);

        if tf_hash == sf_hash && tb_hash == sb_hash {
            println!("{} {}", rev_t.chars().skip(n - i).take(n).collect::<String>(), i);
            return;
        }
    }

    println!("-1");
}
