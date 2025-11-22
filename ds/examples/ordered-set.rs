use cpio::*;
use ds::{DynamicSortedSequence, MapMonoid};

struct T;
impl MapMonoid for T {
    type M = i32;
    type Act = ();
    fn e() -> Self::M {
        0
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
    scan!(n: usize, q: usize, a: [i32; n], query: [(u8, i32); q]);
    let mut set = a.into_iter().collect::<DynamicSortedSequence<T>>();

    for (t, x) in query {
        if t == 0 {
            if !set.contains(&x) {
                set.insert(x);
            }
        } else if t == 1 {
            set.remove_once(&x);
        } else if t == 2 {
            putln!(*set.get(x as usize - 1).unwrap_or(&-1));
        } else if t == 3 {
            if let Some(&max) = set.range(..=x).next_back() {
                putln!(set.first_index_of(&max).unwrap() + 1);
            } else {
                putln!(0);
            }
        } else if t == 4 {
            putln!(*set.range(..=x).next_back().unwrap_or(&-1));
        } else {
            putln!(*set.range(x..).next().unwrap_or(&-1));
        }
    }
}
