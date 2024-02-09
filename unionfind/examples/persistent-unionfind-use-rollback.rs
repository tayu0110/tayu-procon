// https://judge.yosupo.jp/problem/persistent_unionfind
use iolib::*;
use unionfind::RollbackableUnionFind;

fn solve(
    now: usize,
    par: usize,
    t: &[Vec<(usize, usize, usize)>],
    query: &[Vec<(usize, usize, usize)>],
    res: &mut [u8],
    uf: &mut RollbackableUnionFind,
) {
    for &(i, u, v) in &query[now] {
        res[i] = uf.is_same(u, v) as u8;
    }
    for &(to, u, v) in &t[now] {
        if to != par {
            uf.merge(u, v);
            solve(to, now, t, query, res, uf);
            uf.undo_once();
        }
    }
}

fn main() {
    scan!(n: usize, q: usize);

    let mut t = vec![vec![]; q + 1];
    let mut query = vec![vec![]; q + 1];
    for i in 0..q {
        scan!(ty: u8, k: i32, u: usize, v: usize);
        let k = (k + 1) as usize;
        if ty == 0 {
            t[k].push((i + 1, u, v));
        } else {
            query[k].push((i, u, v));
        }
    }

    let mut res = vec![u8::MAX; q];
    let mut uf = RollbackableUnionFind::new(n);
    solve(0, 0, &t, &query, &mut res, &mut uf);
    putitln!(res.into_iter().filter(|&r| r != u8::MAX));
}
