// reference1: https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
// reference2: https://www.kurims.kyoto-u.ac.jp/~ooura/fftman/ftmn1_2.html#sec1_2_1
// In a normal Decimation In Frequency (DIF) FFT, the array starts the operation in normal order and are reordered into bit-reversal order according to the signal flow.
// However, the same result can be obtained by first re-ordering the array in bit-reversal order, then proceeding in order of reversal signal flow with multiplying twiddle factors that is a power of the bit-reversal order to each block.
// This method greatly reduces the amount of cache required for the twiddle factors and improves performance by making memory accesses continuous and localized.
// Similar results are obtained for the Decimation In Time (DIT) FFT.
// The normal DIF requires bit-reversal reordering after the operation (or before in the case of DIT), but when FFT and IFFT are executed in pairs, the bit-reversal reordering can be canceled by proceeding in the order of DIF and IDIT.
// In this implementation, the correct result can be obtained by proceeding in the order of DIT and IDIF.
// The implementation was based on the AtCoder Library (reference1), and reference2 was used to understand the semantics of the implementation.

pub mod cooley_tukey;
mod fft_cache;
pub mod gentleman_sande;
mod traits;
pub mod utility;

use cooley_tukey::cooley_tukey_radix_4_butterfly_inv;
pub use fft_cache::FftCache;
use gentleman_sande::gentleman_sande_radix_4_butterfly;
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use montgomery_modint::MontgomeryModintx8;
use montgomery_modint::{Modulo, MontgomeryModint};
use std::mem::transmute;
pub use traits::NumberTheoreticTransform;
pub use utility::*;

type Modint<M> = MontgomeryModint<M>;
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
type Modintx8<M> = MontgomeryModintx8<M>;

impl<M: Modulo> NumberTheoreticTransform<M> for [MontgomeryModint<M>] {
    #[inline]
    fn ntt(&mut self) {
        let n = self.len();
        assert_eq!(n, 1 << n.trailing_zeros());
        assert!(n <= (1 << (M::N - 1).trailing_zeros()));

        unsafe { gentleman_sande_radix_4_butterfly(n, self, &Self::CACHE) }
    }

    #[inline]
    fn intt(&mut self) {
        let n = self.len();
        assert_eq!(n, 1 << n.trailing_zeros());
        assert!(n <= (1 << (M::N - 1).trailing_zeros()));

        unsafe { cooley_tukey_radix_4_butterfly_inv(n, self, &Self::CACHE) }

        let ninv = Modint::new(n as u32).inv();
        if n >= 8 && is_x86_feature_detected!("avx") && is_x86_feature_detected!("avx2") {
            let ninv = Modintx8::<M>::splat(ninv);
            for v in self.chunks_exact_mut(8) {
                unsafe {
                    let res = Modintx8::load(v.as_ptr()) * ninv;
                    res.store(v.as_mut_ptr());
                }
            }
        } else {
            self.iter_mut().for_each(|a| *a *= ninv);
        }
    }
}

impl<M: Modulo> NumberTheoreticTransform<M> for [u32] {
    #[inline]
    fn ntt(&mut self) {
        unsafe {
            utility::u32tomint::<M>(self);
            let converted = transmute::<&mut [u32], &mut [Modint<M>]>(self);
            converted.ntt();
        }
    }

    #[inline]
    fn intt(&mut self) {
        unsafe {
            let converted = transmute::<&mut [u32], &mut [Modint<M>]>(self);
            converted.intt();
            utility::minttou32::<M>(converted);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use montgomery_modint::{Mod998244353, MontgomeryModint};

    #[test]
    fn self_change_ntt_test() {
        type Modint = MontgomeryModint<Mod998244353>;
        for i in 15..=20 {
            let mut data = (1..=1 << i).map(Modint::new).collect::<Vec<_>>();
            let expect = data.clone();
            data.ntt();
            data.intt();
            assert_eq!(data, expect);
        }
    }

    #[test]
    fn self_change_ntt_u32_test() {
        for i in 15..=20 {
            let mut data = (1u32..=1 << i).collect::<Vec<_>>();
            let expect = data.clone();
            <[u32] as NumberTheoreticTransform<Mod998244353>>::ntt(&mut data);
            <[u32] as NumberTheoreticTransform<Mod998244353>>::intt(&mut data);
            assert_eq!(data, expect);
        }
    }
}
