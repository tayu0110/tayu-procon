#![feature(test)]

extern crate test;

pub mod common;
pub mod cooley_tukey;
pub mod fft_cache;
pub mod gentleman_sande;

use cooley_tukey::cooley_tukey_radix_4_butterfly_inv;
use fft_cache::FftCache;
use gentleman_sande::gentleman_sande_radix_4_butterfly;
use montgomery_modint::{Modulo, MontgomeryModint};

type Modint<M> = MontgomeryModint<M>;

pub fn convolution<M: Modulo>(mut a: Vec<Modint<M>>, mut b: Vec<Modint<M>>) -> Vec<Modint<M>> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;

    a.resize(n, Modint::zero());
    b.resize(n, Modint::zero());

    let cache = FftCache::new();

    gentleman_sande_radix_4_butterfly(n, log, &mut a, &cache);
    gentleman_sande_radix_4_butterfly(n, log, &mut b, &cache);

    a.iter_mut().zip(b.into_iter()).for_each(|(a, b)| *a *= b);

    cooley_tukey_radix_4_butterfly_inv(n, log, &mut a, &cache);

    let ninv = Modint::new(n as u32).inv();
    a.resize(deg, Modint::zero());
    a.iter_mut().for_each(|v| *v *= ninv);
    a
}

#[cfg(test)]
mod tests {}
