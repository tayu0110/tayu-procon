// https://judge.yosupo.jp/problem/bipartitematching
use flow::hopcroft_karp;
use iolib::*;

fn main() {
    scan!(_: usize, _: usize, m: usize, e: [(usize, usize); m]);

    let res = hopcroft_karp(&e);
    putln!(res.len());
    for (c, d) in res {
        putitln!([c, d].into_iter(), sep = ' ');
    }
}
