use criterion::{black_box, criterion_group, criterion_main, Criterion};
use math::MathInt;

fn divisors_enumeration_bench(b: &mut Criterion) {
    b.bench_function("Divisor Enumeration", |b| {
        b.iter(|| {
            for i in 1u32..=1000000 {
                let mut divs = black_box(i).divisors();
                divs.sort_unstable();
                black_box(divs);
            }
        })
    });
}

criterion_group!(benches, divisors_enumeration_bench);
criterion_main!(benches);
