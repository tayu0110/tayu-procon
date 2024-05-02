// https://judge.yosupo.jp/problem/dynamic_graph_vertex_add_component_sum
use ds::{MapMonoid, OnlineDynamicConnectivity};
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
    let tm = std::time::SystemTime::now();
    scan!(n: usize, q: usize, a: [u64; n]);

    let mut dc: OnlineDynamicConnectivity<U64Add> =
        OnlineDynamicConnectivity::from_edges_with_values(n, [], a.into_iter().enumerate());

    let mut link = 0u128;
    let mut cut = 0u128;
    let mut update_by = 0u128;
    let mut fold = 0u128;

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(u: usize, v: usize);
            link = link.wrapping_sub(tm.elapsed().unwrap().as_millis());
            dc.link(u, v).ok();
            link = link.wrapping_add(tm.elapsed().unwrap().as_millis());
        } else if ty == 1 {
            scan!(u: usize, v: usize);
            cut = cut.wrapping_sub(tm.elapsed().unwrap().as_millis());
            dc.cut(u, v);
            cut = cut.wrapping_add(tm.elapsed().unwrap().as_millis());
        } else if ty == 2 {
            scan!(u: usize, x: u64);
            update_by = update_by.wrapping_sub(tm.elapsed().unwrap().as_millis());
            dc.update_by(u, |&m| m + x);
            update_by = update_by.wrapping_add(tm.elapsed().unwrap().as_millis());
        } else {
            scan!(v: usize);
            fold = fold.wrapping_sub(tm.elapsed().unwrap().as_millis());
            putln!(dc.fold(v));
            fold = fold.wrapping_add(tm.elapsed().unwrap().as_millis());
        }
    }

    eprintln!("link: {link}");
    eprintln!("cut: {cut}");
    eprintln!("update_by: {update_by}");
    eprintln!("fold: {fold}");
}
