// https://atcoder.jp/contests/arc008/tasks/arc008_4
use iolib::{putln, scan};
use segtree::{DynamicSegmentTree, Monoid};

struct Affine {
    a: f64,
    b: f64,
}

impl Monoid for Affine {
    type M = Self;
    fn id() -> Self::M {
        Self { a: 1.0, b: 0.0 }
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        Self { a: r.a * l.a, b: r.a * l.b + r.b }
    }
}

fn main() {
    scan!(n: usize, m: usize);

    let mut st = DynamicSegmentTree::<Affine>::new(0..n as isize);
    let mut min = 1.0f64;
    let mut max = 1.0f64;
    for _ in 0..m {
        scan!(p: isize, a: f64, b: f64);
        st.set(p - 1, Affine { a, b });

        let f = st.fold(..);
        min = min.min(f.a + f.b);
        max = max.max(f.a + f.b);
    }

    putln!(min);
    putln!(max);
}
