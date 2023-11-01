use convolution_simd::arbitrary_convolution;
use iolib::{putln, putvec_with_spaceln, scan};

const MOD: u64 = 258280327;

fn main() {
    scan!(n: usize, f: [u64; n + 1], m: usize, g: [u64; m + 1]);
    let (mut f, mut g) = (f, g);
    for v in vec![&mut f, &mut g] {
        while let Some(p) = v.pop() {
            if p != 0 {
                v.push(p);
                break;
            }
        }
    }

    if f.is_empty() || g.is_empty() {
        putln!(0);
        putln!(0);
        return;
    }

    let f = f.into_iter().map(|f| (f % MOD) as u32).collect();
    let g = g.into_iter().map(|g| (g % MOD) as u32).collect();

    let fg = arbitrary_convolution::<MOD>(f, g);

    putln!(fg.len() - 1);
    putvec_with_spaceln!(fg);
}
