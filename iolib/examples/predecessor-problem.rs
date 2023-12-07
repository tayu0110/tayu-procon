// https://judge.yosupo.jp/problem/predecessor_problem
use iolib::{putln, scan};
use std::collections::BTreeSet;

fn main() {
    scan!(_: usize, q: usize, t: String);

    let mut set = t
        .bytes()
        .enumerate()
        .filter_map(|(i, c)| (c == b'1').then_some(i as u32))
        .collect::<BTreeSet<_>>();
    for _ in 0..q {
        scan!(c: u8, k: u32);

        match c {
            0 => {
                set.insert(k);
            }
            1 => {
                set.remove(&k);
            }
            2 => {
                putln!(set.contains(&k) as u8);
            }
            3 => {
                putln!(*set.range(k..).next().unwrap_or(&u32::MAX) as i32);
            }
            4 => {
                putln!(*set.range(..=k).next_back().unwrap_or(&u32::MAX) as i32);
            }
            _ => unreachable!(),
        }
    }
}
