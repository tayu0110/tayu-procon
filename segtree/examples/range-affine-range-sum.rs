// https://judge.yosupo.jp/problem/range_affine_range_sum
use iolib::{putln, scan};
use segtree::RangeAffineRangeSum;
use static_modint::{Mod998244353, StaticModint};

fn main() {
    scan!(n: usize, q: usize, a: [u32; n]);
    let mut st =
        RangeAffineRangeSum::<Mod998244353>::new(a.into_iter().map(StaticModint::raw).collect());

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(l: usize, r: usize, b: u32, c: u32);
            st.apply_range(l, r, (StaticModint::raw(b), StaticModint::raw(c)));
        } else {
            scan!(l: usize, r: usize);
            let (res, _) = st.prod(l, r);
            putln!(res.val());
        }
    }
}
