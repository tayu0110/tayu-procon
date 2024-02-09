use ds::CartesianTree;
use iolib::*;

fn main() {
    scan!(n: usize, a: [usize; n]);

    let ct = CartesianTree::new(a);
    putitln!(
        ct.parlist()
            .into_iter()
            .enumerate()
            .map(|(i, p)| p.unwrap_or(i)),
        sep = ' '
    );
}
