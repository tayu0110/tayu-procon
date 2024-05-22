use criterion::{criterion_group, criterion_main, Criterion};
use montgomery_modint::{Mod998244353, MontgomeryModint};
use number_theoretic_transform::{
    bit_reverse,
    gentleman_sande::{gentleman_sande_radix_4_butterfly, gentleman_sande_radix_4_butterfly_inv},
    FftCache,
};

type Modint = MontgomeryModint<Mod998244353>;

pub fn ntt_gentleman_sande_radix_4(a: &mut [Modint]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);
    let cache = FftCache::new();
    unsafe { gentleman_sande_radix_4_butterfly(deg, a, &cache) }
    bit_reverse(deg, a);
}

pub fn intt_gentleman_sande_radix_4(a: &mut [Modint]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);
    let cache = FftCache::new();
    unsafe { gentleman_sande_radix_4_butterfly_inv(deg, a, &cache) }
    bit_reverse(deg, a);
    let inv = Modint::new(deg as u32).inv();
    a.iter_mut().for_each(|c| *c *= inv)
}

fn gentleman_sande_radix_4_bench(b: &mut Criterion) {
    b.bench_function("Gentleman Sande Radix-4", |b| {
        b.iter(|| {
            for i in 15..=20 {
                let n = 1 << i;
                let mut data: Vec<Modint> = (1..=n).map(Modint::new).collect();
                ntt_gentleman_sande_radix_4(&mut data);
                intt_gentleman_sande_radix_4(&mut data);
            }
        })
    });
}

criterion_group!(benches, gentleman_sande_radix_4_bench);
criterion_main!(benches);
