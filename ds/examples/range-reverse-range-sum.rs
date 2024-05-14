use ds::{DynamicSequence, MapMonoid};
use iolib::*;

struct U64Add;

impl MapMonoid for U64Add {
    type M = u64;
    type Act = ();

    fn e() -> Self::M {
        0
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        l + r
    }

    fn id() -> Self::Act {}
    fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}
    fn map(m: &Self::M, _: &Self::Act) -> Self::M {
        *m
    }
}

fn main() {
    scan!(n: usize, q: usize, a: [u64; n], query: [(u8, usize, usize); q]);

    let mut seq = a.into_iter().collect::<DynamicSequence<U64Add>>();

    for (ty, l, r) in query {
        if ty == 0 {
            seq.reverse(l..r);
        } else {
            putln!(seq.fold(l..r));
        }
    }
}
