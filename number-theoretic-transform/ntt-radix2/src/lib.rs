#![feature(test)]

extern crate test;

pub mod common;
pub mod cooley_tukey;
pub mod fft_cache;
pub mod gentleman_sande;

// use cooley_tukey::cooley_tukey_radix_2_butterfly_inv;
// use fft_cache::FftCache;
// use gentleman_sande::gentleman_sande_radix_2_butterfly;
// use montgomery_modint::{Mod1811939329, Mod2013265921, Mod2281701377, Mod2483027969, Mod2885681153, Mod3221225473, Mod3489660929, Modulo, MontgomeryModint};

// type Modint<M> = MontgomeryModint<M>;

#[cfg(test)]
mod tests {}
