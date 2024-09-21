use std::{cmp::Reverse, collections::HashMap, iter::once};

// https://atcoder.jp/contests/abc372/tasks/abc372_e
use cpio::*;
use ds::{DynamicSortedSequence, MapMonoid};
use unionfind::UnionFind;

struct T;
impl MapMonoid for T {
    type M = Reverse<i32>;
    type Act = ();
    fn e() -> Self::M {
        Reverse(0)
    }
    fn op(l: &Self::M, _: &Self::M) -> Self::M {
        *l
    }
    fn id() -> Self::Act {}
    fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}
    fn map(m: &Self::M, _: &Self::Act) -> Self::M {
        *m
    }
}

fn main() {
    scan!(n: usize, q: usize);

    let mut map = (0..n)
        .map(|i| {
            (
                i,
                once(Reverse(i as i32 + 1)).collect::<DynamicSortedSequence<T>>(),
            )
        })
        .collect::<HashMap<_, _>>();
    let mut uf = UnionFind::new(n);
    for _ in 0..q {
        scan!(ty: u8);

        if ty == 1 {
            scan!(u: usize, v: usize);

            if !uf.is_same(u - 1, v - 1) {
                let mut su = map.remove(&uf.root(u - 1)).unwrap();
                let mut sv = map.remove(&uf.root(v - 1)).unwrap();
                if su.len() < sv.len() {
                    (su, sv) = (sv, su);
                }
                su.extend(sv);
                uf.merge(u - 1, v - 1);
                map.insert(uf.root(u - 1), su);
            }
        } else {
            scan!(v: usize, k: usize);
            let seq = map.get(&uf.root(v - 1)).unwrap();
            if seq.len() < k {
                putln!(-1);
            } else {
                putln!(seq.get(k - 1).unwrap().0);
            }
        }
    }
}
