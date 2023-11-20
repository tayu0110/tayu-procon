// https://judge.yosupo.jp/problem/unionfind
use iolib::{putln, scan};
use unionfind::UnionFind;

fn main() {
    scan!(n: usize, q: usize);

    let mut uf = UnionFind::new(n);
    for _ in 0..q {
        scan!(t: u8, u: u32, v: u32);
        if t == 0 {
            uf.merge(u as usize, v as usize);
        } else {
            putln!(uf.is_same(u as usize, v as usize) as u8);
        }
    }
}
