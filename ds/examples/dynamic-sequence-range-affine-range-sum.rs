// https://judge.yosupo.jp/problem/dynamic_sequence_range_affine_range_sum
use ds::{DynamicSequence, MapMonoid};
use iolib::*;
use static_modint::{Mod998244353, StaticModint};

type Modint = StaticModint<Mod998244353>;

struct M32Affine;

impl MapMonoid for M32Affine {
    type M = (Modint, Modint);
    type Act = (Modint, Modint);
    fn e() -> Self::M {
        (Modint::zero(), Modint::zero())
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        (l.0 + r.0, l.1 + r.1)
    }
    fn id() -> Self::Act {
        (Modint::one(), Modint::zero())
    }
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
        (
            r.0 * l.0,
            Modint::new(r.0.val() as u64 * l.1.val() as u64 + r.1.val() as u64),
        )
    }
    fn map(m: &Self::M, act: &Self::Act) -> Self::M {
        (
            Modint::new(
                act.0.val() as u64 * m.0.val() as u64 + act.1.val() as u64 * m.1.val() as u64,
            ),
            m.1,
        )
    }
}

fn main() {
    scan!(n: usize, q: usize, a: [u32; n]);

    let mut ds = a
        .into_iter()
        .map(|a| (Modint::raw(a), Modint::one()))
        .collect::<DynamicSequence<M32Affine>>();

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(i: usize, x: u32);
            ds.insert(i, (Modint::raw(x), Modint::one()));
        } else if ty == 1 {
            scan!(i: usize);
            ds.remove(i);
        } else if ty == 2 {
            scan!(l: usize, r: usize);
            ds.reverse(l..r);
        } else if ty == 3 {
            scan!(l: usize, r: usize, b: u32, c: u32);
            ds.apply_range(l..r, &(Modint::raw(b), Modint::raw(c)));
        } else {
            scan!(l: usize, r: usize);
            putln!(ds.fold(l..r).0.val());
        }
    }
}
