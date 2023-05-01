use crate::fft_cache::FftCache;
use montgomery_modint::{Modulo, MontgomeryModint};

type Modint<M> = MontgomeryModint<M>;

#[inline]
fn cooley_tukey_radix_2_kernel<M: Modulo>(deg: usize, width: usize, offset: usize, a: &mut [Modint<M>], rate: &[Modint<M>]) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    for block in 0..blocks {
        let top = block * width;
        if rot == Modint::one() {
            for now in top..top + offset {
                let c = a[now + offset];
                a[now + offset] = a[now] - c;
                a[now] += c;
            }
        } else {
            for now in top..top + offset {
                let c = a[now + offset];
                a[now + offset] = (a[now] - c) * rot;
                a[now] += c;
            }
        }
        if top + width != deg {
            rot *= rate[block.trailing_ones() as usize];
        }
    }
}

#[inline]
pub fn cooley_tukey_radix_2_butterfly<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    let rate = &cache.rate2;
    for i in 0..log {
        let width = 1 << (i + 1);
        let offset = width >> 1;
        cooley_tukey_radix_2_kernel(deg, width, offset, a, &rate);
    }
}

#[inline]
pub fn cooley_tukey_radix_2_butterfly_inv<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    let rate = &cache.irate2;
    for i in 0..log {
        let width = 1 << (i + 1);
        let offset = width >> 1;
        cooley_tukey_radix_2_kernel(deg, width, offset, a, &rate);
    }
}

#[cfg(test)]
mod tests {
    use super::super::common::bit_reverse;
    use super::*;
    use super::{cooley_tukey_radix_2_butterfly, cooley_tukey_radix_2_butterfly_inv};
    use montgomery_modint::{Mod998244353, MontgomeryModint};
    use test::Bencher;

    type Modint = MontgomeryModint<Mod998244353>;

    pub fn ntt_cooley_tukey_radix_2(a: &mut [Modint]) {
        let deg = a.len();
        let log = deg.trailing_zeros() as usize;
        debug_assert_eq!(a.len(), 1 << log);
        bit_reverse(deg, a);
        let cache = FftCache::<Mod998244353>::new();
        cooley_tukey_radix_2_butterfly(deg, log, a, &cache);
    }
    pub fn intt_cooley_tukey_radix_2(a: &mut [Modint]) {
        let deg = a.len();
        let log = deg.trailing_zeros() as usize;
        debug_assert_eq!(a.len(), 1 << log);
        bit_reverse(deg, a);
        let cache = FftCache::<Mod998244353>::new();
        cooley_tukey_radix_2_butterfly_inv(deg, log, a, &cache);
        let inv = Modint::new(deg as u32).inv();
        a.iter_mut().for_each(|c| *c *= inv)
    }

    #[test]
    fn cooley_tukey_radix_2_test() {
        for i in 1..=13 {
            let n = 1 << i;
            let data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
            let mut data1 = data.clone();
            ntt_cooley_tukey_radix_2(&mut data1);
            intt_cooley_tukey_radix_2(&mut data1);
            assert_eq!(data, data1);
        }
    }

    #[bench]
    fn cooley_tukey_radix_2_bench(b: &mut Bencher) {
        b.iter(|| {
            for i in 15..=20 {
                let n = 1 << i;
                let mut data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
                ntt_cooley_tukey_radix_2(&mut data);
                intt_cooley_tukey_radix_2(&mut data);
            }
        })
    }
}
