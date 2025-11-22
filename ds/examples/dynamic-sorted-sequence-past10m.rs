// https://atcoder.jp/contests/past202203-open/tasks/past202203_m
use std::{cmp::Reverse, collections::HashMap};

use cpio::*;
use ds::{DynamicSortedSequence, MapMonoid};

struct T;
impl MapMonoid for T {
    type Act = ();
    type M = Reverse<u32>;
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
    scan!(n: usize, q: usize, mut p: [u32; n]);

    let mut map = HashMap::new();
    for (i, &p) in p.iter().enumerate() {
        map.insert(p, i);
    }
    let mut seq = p
        .iter()
        .cloned()
        .map(Reverse)
        .collect::<DynamicSortedSequence<T>>();
    for _ in 0..q {
        scan!(ty: usize);

        if ty == 1 {
            scan!(a: usize, x: u32);
            seq.remove_once(&Reverse(p[a - 1]));
            seq.insert(Reverse(x));
            p[a - 1] = x;
            map.insert(x, a - 1);
        } else if ty == 2 {
            scan!(a: usize);
            let index = seq.first_index_of(&Reverse(p[a - 1])).unwrap();
            putln!(index + 1);
        } else {
            scan!(r: usize);
            let Reverse(p) = seq.get(r - 1).unwrap();
            putln!(map.get(p).unwrap() + 1);
        }
    }
}
