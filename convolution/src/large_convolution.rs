use super::convolution;
use super::hadamard_u32;
use montgomery_modint::{Mod998244353, MontgomeryModint, MontgomeryModintx8};
use number_theoretic_transform::NumberTheoreticTransform;
use std::arch::x86_64::_mm256_storeu_si256;
use std::ptr::copy_nonoverlapping;

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

// reference: https://judge.yosupo.jp/submission/68990
pub fn convolution_large(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    const THRESHOLD: usize = 1 << 23;
    let deg = a.len() + b.len() - 1;
    if deg <= THRESHOLD {
        return convolution::<Mod998244353>(a, b);
    }
    let n = deg.next_power_of_two();
    let width = THRESHOLD >> 1;
    a.resize((a.len() + 7) >> 3 << 3, 0);
    b.resize((b.len() + 7) >> 3 << 3, 0);

    let x = a
        .chunks(width)
        .map(|a| {
            let mut x = vec![0u32; THRESHOLD];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            <[u32] as NumberTheoreticTransform<Mod998244353>>::ntt(&mut x);
            x
        })
        .collect::<Vec<_>>();
    let y = b
        .chunks(width)
        .map(|a| {
            let mut x = vec![0u32; THRESHOLD];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            <[u32] as NumberTheoreticTransform<Mod998244353>>::ntt(&mut x);
            x
        })
        .collect::<Vec<_>>();

    let mut res = vec![Modint::<Mod998244353>::zero(); n];
    let mut p = vec![Modint::zero(); THRESHOLD];
    for s in 0..(x.len() + y.len() - 1) {
        for i in 0..=s {
            if let (Some(x), Some(y)) = (x.get(i), y.get(s - i)) {
                let mut x = x.clone();
                hadamard_u32::<Mod998244353>(&mut x, y);
                p.iter_mut()
                    .zip(x)
                    .for_each(|(p, v)| *p += Modint::from_rawval(v));
            }
        }
        unsafe {
            p.intt();
            for (res, p) in res[(s * width)..]
                .chunks_exact_mut(8)
                .zip(p.chunks_exact_mut(8))
            {
                (Modintx8::load(res.as_ptr()) + Modintx8::load(p.as_ptr())).store(res.as_mut_ptr());
                Modintx8::zero().store(p.as_mut_ptr())
            }
        }
    }

    unsafe {
        for v in res.chunks_exact_mut(8).take((deg + 7) >> 3) {
            let res = Modintx8::load(v.as_ptr());
            _mm256_storeu_si256(v.as_mut_ptr() as _, res.val());
        }
        res.into_iter().take(deg).map(|v| v.val).collect()
    }
}
