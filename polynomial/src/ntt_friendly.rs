use convolution::hadamard;
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use number_theoretic_transform::NumberTheoreticTransform;

use crate::Polynomial;

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

pub(crate) fn is_ntt_friendly_mod<M: Modulo>(len: usize) -> bool {
    let tz = (M::N - 1).trailing_zeros();
    len <= 1 << tz
}

#[target_feature(enable = "avx", enable = "avx2")]
pub(crate) unsafe fn doubling_step_for_inv<M: Modulo>(
    poly: &Polynomial<M>,
    mut g: Polynomial<M>,
) -> Polynomial<M> {
    let size = g.deg();
    let mut f = poly.prefix(size << 1);
    g.resize(size << 1);
    let hg = {
        let mut g_ntt = g.prefix(size << 1);
        g_ntt.coef.ntt();
        f.coef.ntt();
        hadamard(&mut f.coef, &g_ntt.coef);
        f.coef.intt();
        f.coef[..size].fill(Modint::zero());
        f.coef.ntt();
        hadamard(&mut f.coef, &g_ntt.coef);
        f.coef.intt();
        f
    };
    let mut git = g.coef[size..2 * size].chunks_exact_mut(8);
    let mut hgit = hg.coef[size..].chunks_exact(8);
    for (p, v) in git.by_ref().zip(hgit.by_ref()) {
        (Modintx8::load(p.as_ptr()) - Modintx8::load(v.as_ptr())).store(p.as_mut_ptr());
    }
    git.into_remainder()
        .iter_mut()
        .zip(hgit.remainder())
        .for_each(|(p, v)| *p -= *v);
    g
}

// reference: https://judge.yosupo.jp/submission/70211
#[target_feature(enable = "avx", enable = "avx2")]
pub(crate) unsafe fn exp<M: Modulo>(poly: &Polynomial<M>, deg: usize) -> Option<Polynomial<M>> {
    let mut written = 0;
    let mut now = 1;
    let mut res = Polynomial::one();
    let mut inv = Polynomial::one();
    let mut table = unsafe { Polynomial::gen_inverse_table(deg.next_power_of_two()) };
    while now < deg {
        let mut f = res.prefix(now << 1);
        let mut g = inv.prefix(now << 1);
        f.coef.ntt();
        g.coef.ntt();

        let mut w = poly.prefix(now).derivative() << 1u32;
        hadamard(&mut table[written..now], &w.coef[written..now]);
        written = now;

        w.coef.ntt();
        hadamard(&mut w.coef, &f.prefix(now).coef);
        w.coef.intt();
        w = (res.derivative() << 1u32) - w;

        w.resize(now << 1);
        w.coef.ntt();
        hadamard(&mut w.coef, &g.coef);
        w.coef.intt();

        let mut z = poly.prefix(now << 1) - table[..now].into();
        hadamard(&mut w.coef[..now], &table[now..now << 1]);
        z.coef[now..]
            .iter_mut()
            .zip(w.coef)
            .for_each(|(s, t)| *s -= t);
        z.coef.ntt();
        hadamard(&mut z.coef, &f.coef);
        z.coef.intt();
        res.coef.extend(&z.coef[now..]);

        now <<= 1;
        if now < deg {
            inv = doubling_step_for_inv(&res, inv);
        }
    }
    Some(res.prefix(deg))
}

#[target_feature(enable = "avx", enable = "avx2")]
pub(crate) unsafe fn gen_subproduct_tree<M: Modulo>(xs: Vec<Modint<M>>) -> Vec<Polynomial<M>> {
    let len = xs.len();
    let m = len.next_power_of_two();
    let mut subproduct_tree = vec![Polynomial::empty(); m * 2];
    for i in 0..m {
        subproduct_tree[m + i] = vec![Modint::one(), -*xs.get(i).unwrap_or(&Modint::zero())].into();
    }

    for i in (1..m).rev() {
        let new_deg = (subproduct_tree[i << 1].deg() - 1) << 1;
        subproduct_tree[i << 1].resize(new_deg);
        subproduct_tree[(i << 1) | 1].resize(new_deg);
        subproduct_tree[i << 1].coef.ntt();
        subproduct_tree[(i << 1) | 1].coef.ntt();
        subproduct_tree[i] = {
            let mut poly = subproduct_tree[i << 1].clone();
            hadamard(&mut poly.coef, &subproduct_tree[(i << 1) | 1].coef);
            poly
        };
        subproduct_tree[i].coef.intt();
        let k = subproduct_tree[i].coef[0] - Modint::one();
        subproduct_tree[i].coef.push(k);
        subproduct_tree[i].coef[0] = Modint::one();
    }
    subproduct_tree
}

#[target_feature(enable = "avx", enable = "avx2")]
pub(crate) unsafe fn transposed_uptree<M: Modulo>(
    m: usize,
    mut subproduct_tree: Vec<Polynomial<M>>,
) -> Vec<Polynomial<M>> {
    for i in 1..m {
        let (a, b) = subproduct_tree.split_at_mut(i << 1);
        let n = a[i].deg() >> 1;
        a[i].coef.ntt();
        for b in b.iter_mut().take(2) {
            hadamard(&mut b.coef, &a[i].coef);
            b.coef.intt();
            *b >>= n;
        }
        b.swap(0, 1);
    }
    subproduct_tree
}

#[target_feature(enable = "avx", enable = "avx2")]
pub(crate) unsafe fn interpolation<M: Modulo>(
    m: usize,
    mut keep: Vec<Polynomial<M>>,
    mut subproduct_tree: Vec<Polynomial<M>>,
) -> Polynomial<M> {
    for i in 1..m {
        let n = keep[i << 1].deg() >> 1;
        keep[i << 1].coef.intt();
        keep[i << 1].resize(n + 1);
        keep[i << 1].reverse();
        keep[(i << 1) | 1].coef.intt();
        keep[(i << 1) | 1].resize(n + 1);
        keep[(i << 1) | 1].reverse();
    }

    for i in (1..m).rev() {
        let (r, l) = (
            subproduct_tree.pop().unwrap(),
            subproduct_tree.pop().unwrap(),
        );
        let (kr, kl) = (keep.pop().unwrap(), keep.pop().unwrap());
        if l.deg() == 0 && r.deg() == 0 {
            subproduct_tree[i] = l;
            keep[i].coef.clear();
            continue;
        }
        if r.deg() == 0 {
            subproduct_tree[i] = l;
            keep[i] = kl;
            continue;
        }
        if kl.deg() != kr.deg() {
            let new_deg = kl.deg() + kr.deg() - 1;
            let sh = keep[i].deg() - new_deg;
            keep[i] >>= sh;
        }
        subproduct_tree[i] = l * kr + r * kl;
    }
    subproduct_tree.pop().unwrap()
}
