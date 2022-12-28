mod common;
pub mod cooley_tukey;
mod fft_cache;
pub mod gentleman_sande;
mod simd;

use cooley_tukey::cooley_tukey_radix_8_butterfly_inv_montgomery_modint;
use fft_cache::FftCache;
use gentleman_sande::gentleman_sande_radix_8_butterfly_montgomery_modint;
use modint::{Mod998244353, MontgomeryModint};
use simd::{cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2, gentleman_sande_radix_4_butterfly_montgomery_modint_avx2};

type Mint998244353 = MontgomeryModint<Mod998244353>;

pub fn convolution(mut a: Vec<Mint998244353>, mut b: Vec<Mint998244353>) -> Vec<Mint998244353> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;

    a.resize(n, Mint998244353::zero());
    b.resize(n, Mint998244353::zero());

    let cache = FftCache::<Mint998244353>::new(log);

    if is_x86_feature_detected!("avx2") {
        unsafe {
            gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(n, log, &mut a, &cache);
            gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(n, log, &mut b, &cache);
        }
    } else {
        gentleman_sande_radix_8_butterfly_montgomery_modint(n, log, &mut a, &cache);
        gentleman_sande_radix_8_butterfly_montgomery_modint(n, log, &mut b, &cache);
    }

    a.iter_mut().zip(b.into_iter()).for_each(|(a, b)| *a *= b);

    if is_x86_feature_detected!("avx2") {
        unsafe {
            cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2(n, log, &mut a, &cache);
        }
    } else {
        cooley_tukey_radix_8_butterfly_inv_montgomery_modint(n, log, &mut a, &cache);
    }

    let ninv = Mint998244353::new(n as u32).inv();
    a.resize(deg, Mint998244353::zero());
    a.iter_mut().for_each(|v| *v *= ninv);
    a
}

#[cfg(test)]
mod tests {
    use super::convolution;
    use modint::{Mod998244353, MontgomeryModint};

    #[test]
    fn convolution_test() {
        type Mint998244353 = MontgomeryModint<Mod998244353>;
        let a = vec![Mint998244353::new(1), Mint998244353::new(2), Mint998244353::new(3), Mint998244353::new(4)];
        let b = vec![Mint998244353::new(1), Mint998244353::new(2), Mint998244353::new(4), Mint998244353::new(8)];
        let c = convolution(a, b);
        assert_eq!(
            c,
            vec![
                Mint998244353::new(1),
                Mint998244353::new(4),
                Mint998244353::new(11),
                Mint998244353::new(26),
                Mint998244353::new(36),
                Mint998244353::new(40),
                Mint998244353::new(32)
            ]
        );
    }
}
