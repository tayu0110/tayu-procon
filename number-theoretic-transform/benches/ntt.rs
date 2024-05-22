use criterion::{criterion_group, criterion_main, Criterion};
use montgomery_modint::{Mod998244353, MontgomeryModint};
use number_theoretic_transform::NumberTheoreticTransform;

fn simple_ntt_bench(b: &mut Criterion) {
    b.bench_function("NTT", |b| {
        b.iter(|| {
            type Modint = MontgomeryModint<Mod998244353>;
            for i in 15..=20 {
                let mut data = (0..1 << i).map(Modint::new).collect::<Vec<_>>();
                data.ntt();
                data.intt();
            }
        })
    });
}

criterion_group!(benches, simple_ntt_bench);
criterion_main!(benches);
