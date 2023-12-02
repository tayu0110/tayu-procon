use iolib::{putln, scan};
use utility::CumSum2D;

fn main() {
    scan!(n: usize, q: usize, p: [String; n]);

    let cum = p
        .into_iter()
        .map(|p| p.chars().map(|c| (c == 'B') as usize).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let cum = CumSum2D::new(cum);

    for _ in 0..q {
        scan!(a: usize, b: usize, c: usize, d: usize);

        putln!(cum.sum_as_infinite_grid(a..c + 1, b..d + 1));
    }
}
