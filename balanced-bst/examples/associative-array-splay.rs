// https://judge.yosupo.jp/problem/associative_array
use balanced_bst::SplayTreeMap;
use iolib::{putln, scan};

fn main() {
    scan!(q: usize);

    let mut tree = SplayTreeMap::new();

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(k: u64, v: u64);
            tree.insert(k, v);
        } else {
            scan!(k: u64);
            putln!(*tree.get(&k).unwrap_or(&0));
        }
    }
}
