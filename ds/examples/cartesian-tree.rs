use cpio::*;
use ds::CartesianTree;

fn main() {
    scan!(n: usize, a: [usize; n]);

    let ct = CartesianTree::new(a);
    putln!(
        ct.parlist()
            .into_iter()
            .enumerate()
            .map(|(i, p)| p.unwrap_or(i)),
        @sep = " "
    );
}
