use super::cooley_tukey::cooley_tukey_radix_4_butterfly_inv;
use super::fft_cache::FftCache;
use super::gentleman_sande::gentleman_sande_radix_4_butterfly;
use montgomery_modint::{Modulo, MontgomeryModint};

type Modint<M> = MontgomeryModint<M>;

pub struct Ntt<M: Modulo> {
    cache: FftCache<M>,
}

impl<M: Modulo> Ntt<M> {
    pub const fn new() -> Self { Self { cache: FftCache::new() } }

    pub fn convolution(&self, mut a: Vec<Modint<M>>, mut b: Vec<Modint<M>>) -> Vec<Modint<M>> {
        let deg = a.len() + b.len() - 1;
        let n = deg.next_power_of_two();
        let log = n.trailing_zeros() as usize;

        a.resize(n, Modint::zero());
        b.resize(n, Modint::zero());

        gentleman_sande_radix_4_butterfly(n, log, &mut a, &self.cache);
        gentleman_sande_radix_4_butterfly(n, log, &mut b, &self.cache);

        a.iter_mut().zip(b.into_iter()).for_each(|(a, b)| *a *= b);

        cooley_tukey_radix_4_butterfly_inv(n, log, &mut a, &self.cache);

        let ninv = Modint::new(n as u32).inv();
        a.resize(deg, Modint::zero());
        a.iter_mut().for_each(|v| *v *= ninv);
        a
    }
}
