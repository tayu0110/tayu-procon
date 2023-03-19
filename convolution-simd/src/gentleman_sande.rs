use super::common::*;
use super::FftCache;
use montgomery_modint::{Modulo, MontgomeryModint};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    _mm256_castsi256_si128, _mm256_loadu_si256, _mm256_set1_epi32, _mm256_set_epi32, _mm256_set_m128i, _mm256_setr_epi32, _mm256_shuffle_epi32, _mm256_storeu_si256, _mm256_unpackhi_epi32,
    _mm256_unpacklo_epi32, _mm256_unpacklo_epi64, _mm_loadu_si128, _mm_setr_epi32,
};

type Modint<M> = MontgomeryModint<M>;

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn radix_2_kernel_gentleman_sande_avx2<M: Modulo>(width: usize, a: &mut [Modint<M>]) {
    // offset = width >> 1;
    assert_eq!(width >> 1, 1);
    for a in a.chunks_exact_mut(2) {
        let c1 = *a.get_unchecked(1);
        *a.get_unchecked_mut(1) = *a.get_unchecked(0) - c1;
        *a.get_unchecked_mut(0) += c1;
    }
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
#[target_feature(enable = "avx")]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_kernel_gentleman_sande_avx2<M: Modulo>(deg: usize, width: usize, a: &mut [Modint<M>], twiddle: &[Modint<M>]) {
    let log = width.trailing_zeros();
    let exp = deg >> log;

    // Constants for Montgomery Operation
    let modulo = _mm256_set1_epi32(M::MOD as i32);
    let modulo_inv = _mm256_set1_epi32(M::MOD_INV as i32);
    let prim_root = _mm256_set1_epi32(twiddle[deg >> 2].val as i32);

    let offset = width >> 2;
    if offset == 1 {
        let prim_root = twiddle[(twiddle.len() - 1) >> 2];
        for a in a.chunks_exact_mut(4) {
            let (c0, c1, c2, c3) = (*a.get_unchecked(0), *a.get_unchecked(1), *a.get_unchecked(2), *a.get_unchecked(3));
            let (c0, c1, c2, c3) = {
                let c0pc2 = c0 + c2;
                let c0mc2 = c0 - c2;
                let c1pc3 = c1 + c3;
                let c1mc3 = c1 - c3;
                let c1mc3im = c1mc3 * prim_root;
                (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
            };
            *a.get_unchecked_mut(0) = c0;
            *a.get_unchecked_mut(2) = c1;
            *a.get_unchecked_mut(1) = c2;
            *a.get_unchecked_mut(3) = c3;
        }
    } else if offset == 2 {
        let w = _mm256_set_epi32(
            twiddle[exp * 3].val as i32,
            twiddle[0].val as i32,
            twiddle[exp].val as i32,
            twiddle[0].val as i32,
            twiddle[exp * 2].val as i32,
            twiddle[0].val as i32,
            Modint::<M>::one().val as i32,
            Modint::<M>::one().val as i32,
        );
        for top in (0..deg).step_by(8) {
            let c0 = _mm_setr_epi32(a[top].val as i32, 0, a[top + 1].val as i32, 0);
            let c1 = _mm_setr_epi32(a[top + 2].val as i32, 0, a[top + 3].val as i32, 0);
            let c2 = _mm_setr_epi32(a[top + 4].val as i32, 0, a[top + 5].val as i32, 0);
            let c3 = _mm_setr_epi32(a[top + 6].val as i32, 0, a[top + 7].val as i32, 0);

            let (c0, c1, c2, c3) = radix_4_innerx2_sse(c0, c1, c2, c3, _mm256_castsi256_si128(modulo), _mm256_castsi256_si128(modulo_inv), _mm256_castsi256_si128(prim_root));

            // c0       = [c00, 0, c10, 0, 0, 0, 0, 0], c1 = [c01, 0, c11, 0, 0, 0, 0, 0]
            // c01      = [c00, 0, c10, 0, c01, 0, c11, 0]
            let c01 = _mm256_set_m128i(c1, c0);
            // c2       = [c02, 0, c12, 0, 0, 0, 0, 0], c3 = [c03, 0, c13, 0, 0, 0, 0, 0]
            // c23      = [c02, 0, c12, 0, c03, 0, c13, 0]
            let c23 = _mm256_set_m128i(c3, c2);
            // c0123    = [c00, c02, c10, c12, c01, c03, c11, c13]
            let c0123 = _mm256_unpacklo_epi64(_mm256_unpacklo_epi32(c01, c23), _mm256_unpackhi_epi32(c01, c23));
            // c0123    = [c00, c10, c02, c12, c01, c11, c03, c13]
            let c0123 = _mm256_shuffle_epi32(c0123, 0b11_01_10_00);
            let c0123 = montgomery_multiplication_u32x8(w, c0123, modulo, modulo_inv);

            _mm256_storeu_si256(a[top..top + 8].as_mut_ptr() as *mut _, c0123);
        }
    } else if offset == 4 {
        let w02 = _mm256_setr_epi32(
            M::R as i32,
            M::R as i32,
            M::R as i32,
            M::R as i32,
            twiddle[0].val as i32,
            twiddle[exp * 2].val as i32,
            twiddle[exp * 4].val as i32,
            twiddle[exp * 6].val as i32,
        );
        let w13 = _mm256_setr_epi32(
            twiddle[0].val as i32,
            twiddle[exp].val as i32,
            twiddle[exp * 2].val as i32,
            twiddle[exp * 3].val as i32,
            twiddle[0].val as i32,
            twiddle[exp * 3].val as i32,
            twiddle[exp * 6].val as i32,
            twiddle[exp * 9].val as i32,
        );

        for a in a.chunks_exact_mut(16) {
            let c0 = _mm_loadu_si128(a[0..4].as_ptr() as *const _);
            let c1 = _mm_loadu_si128(a[4..8].as_ptr() as *const _);
            let c2 = _mm_loadu_si128(a[8..12].as_ptr() as *const _);
            let c3 = _mm_loadu_si128(a[12..16].as_ptr() as *const _);

            let (c0, c1, c2, c3) = radix_4_innerx4_sse(c0, c1, c2, c3, _mm256_castsi256_si128(modulo), _mm256_castsi256_si128(modulo_inv), _mm256_castsi256_si128(prim_root));

            let c02 = _mm256_set_m128i(c2, c0);
            let c02 = montgomery_multiplication_u32x8(w02, c02, modulo, modulo_inv);
            _mm256_storeu_si256(a[..8].as_mut_ptr() as *mut _, c02);

            let c13 = _mm256_set_m128i(c3, c1);
            let c13 = montgomery_multiplication_u32x8(w13, c13, modulo, modulo_inv);
            _mm256_storeu_si256(a[8..16].as_mut_ptr() as *mut _, c13);
        }
    } else {
        for top in (0..deg).step_by(width) {
            let mut exp_now = 0;
            for (((v0, v1), v2), v3) in a[top..top + offset]
                .chunks_exact(8)
                .zip(a[top + offset..top + offset * 2].chunks_exact(8))
                .zip(a[top + offset * 2..top + offset * 3].chunks_exact(8))
                .zip(a[top + offset * 3..top + offset * 4].chunks_exact(8))
            {
                let c0 = _mm256_loadu_si256(v0.as_ptr() as *const _);
                let c1 = _mm256_loadu_si256(v1.as_ptr() as *const _);
                let c2 = _mm256_loadu_si256(v2.as_ptr() as *const _);
                let c3 = _mm256_loadu_si256(v3.as_ptr() as *const _);

                let (c0, c1, c2, c3) = radix_4_innerx8(c0, c1, c2, c3, modulo, modulo_inv, prim_root);
                _mm256_storeu_si256(v0.as_ptr() as *mut _, c0);

                let w1 = _mm256_setr_epi32(
                    twiddle.get_unchecked(exp_now).val as i32,
                    twiddle.get_unchecked(exp_now + exp).val as i32,
                    twiddle.get_unchecked(exp_now + exp * 2).val as i32,
                    twiddle.get_unchecked(exp_now + exp * 3).val as i32,
                    twiddle.get_unchecked(exp_now + exp * 4).val as i32,
                    twiddle.get_unchecked(exp_now + exp * 5).val as i32,
                    twiddle.get_unchecked(exp_now + exp * 6).val as i32,
                    twiddle.get_unchecked(exp_now + exp * 7).val as i32,
                );
                _mm256_storeu_si256(v2.as_ptr() as *mut _, montgomery_multiplication_u32x8(w1, c1, modulo, modulo_inv));

                let w2 = _mm256_setr_epi32(
                    twiddle.get_unchecked(exp_now * 2).val as i32,
                    twiddle.get_unchecked((exp_now + exp) * 2).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 2) * 2).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 3) * 2).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 4) * 2).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 5) * 2).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 6) * 2).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 7) * 2).val as i32,
                );
                _mm256_storeu_si256(v1.as_ptr() as *mut _, montgomery_multiplication_u32x8(w2, c2, modulo, modulo_inv));

                let w3 = _mm256_setr_epi32(
                    twiddle.get_unchecked(exp_now * 3).val as i32,
                    twiddle.get_unchecked((exp_now + exp) * 3).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 2) * 3).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 3) * 3).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 4) * 3).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 5) * 3).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 6) * 3).val as i32,
                    twiddle.get_unchecked((exp_now + exp * 7) * 3).val as i32,
                );
                _mm256_storeu_si256(v3.as_ptr() as *mut _, montgomery_multiplication_u32x8(w3, c3, modulo, modulo_inv));

                exp_now += exp << 3;
            }
        }
    }
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
#[target_feature(enable = "avx")]
#[target_feature(enable = "avx2")]
pub unsafe fn gentleman_sande_radix_4_butterfly_montgomery_modint_avx2<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<Modint<M>>) {
    let twiddle = cache.twiddle_factors();
    assert_eq!(twiddle[(twiddle.len() - 1) >> 2], cache.prim_root(2));
    for i in (0..log >> 1 << 1).step_by(2) {
        let width = deg >> i;
        radix_4_kernel_gentleman_sande_avx2(deg, width, a, twiddle);
    }

    if log & 1 != 0 {
        let width = deg >> (log - 1);
        radix_2_kernel_gentleman_sande_avx2(width, a);
    }
}

#[cfg(test)]
mod tests_gentleman_sande {
    use super::super::FftCache;
    use super::{gentleman_sande_radix_4_butterfly_montgomery_modint_avx2, radix_2_kernel_gentleman_sande_avx2, radix_4_kernel_gentleman_sande_avx2};
    use montgomery_modint::{Mod998244353, MontgomeryModint};

    type Modint = MontgomeryModint<Mod998244353>;

    #[inline]
    pub fn bit_reverse<T>(deg: usize, log: usize, a: &mut [T]) {
        for i in 0..deg {
            let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
            if i <= rev_i {
                a.swap(i, rev_i);
            }
        }
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn gentleman_sande_radix_4_butterfly_inv_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Modint], cache: &FftCache<Modint>) {
        let twiddle = cache.twiddle_factors_inv();
        for i in (0..log >> 1 << 1).step_by(2) {
            let width = deg >> i;
            radix_4_kernel_gentleman_sande_avx2(deg, width, a, twiddle);
        }

        if log & 1 != 0 {
            let width = deg >> (log - 1);
            radix_2_kernel_gentleman_sande_avx2(width, a);
        }
    }

    macro_rules! impl_fft_inner {
        ( $t:ty, $butterfly:ident, $deg:ident, $log:ident, $a:ident, $cache:ident, $epilogue:expr ) => {{
            unsafe {
                $butterfly($deg, $log, $a, &($cache));
            }
            bit_reverse($deg, $log, $a);
            $epilogue($deg, $a);
        }};
    }

    macro_rules! impl_fft_template {
        ( $t:ty, $fname:ident, $butterfly:ident, $inner:expr ) => {
            pub fn $fname(a: &mut [$t]) {
                let deg = a.len();
                let log = deg.trailing_zeros() as usize;
                debug_assert_eq!(a.len(), 1 << log);
                let cache = FftCache::<$t>::new(log);
                impl_fft_inner!($t, $butterfly, deg, log, a, cache, $inner);
            }
        };
    }

    macro_rules! impl_fft {
        ( $t:ty, $fname:ident, $butterfly:ident, $fname_inv:ident, $butterfly_inv:ident, $inner_inv:expr) => {
            impl_fft_template!($t, $fname, $butterfly, {});
            impl_fft_template!($t, $fname_inv, $butterfly_inv, $inner_inv);
        };
    }

    macro_rules! impl_fft_all_radix {
        ( $t:ty, $rad8:ident, $butterfly8:ident, $rad8inv:ident, $butterfly8inv:ident, $inner_inv:expr) => {
            impl_fft!($t, $rad8, $butterfly8, $rad8inv, $butterfly8inv, $inner_inv);
        };
    }

    impl_fft_all_radix!(
        Modint,
        fft_gentleman_sande_radix_4_montgomery_modint,
        gentleman_sande_radix_4_butterfly_montgomery_modint_avx2,
        ifft_gentleman_sande_radix_4_montgomery_modint,
        gentleman_sande_radix_4_butterfly_inv_montgomery_modint_avx2,
        |deg: usize, a: &mut [Modint]| {
            let inv = Modint::new(deg as u32).inv();
            a.iter_mut().for_each(|c| *c *= inv)
        }
    );

    const N: u32 = 1 << 13;

    #[test]
    fn gentleman_sande_radix_4_montgomery_modint_test() {
        let data: Vec<Modint> = (1..=N).map(|v| Modint::new(v)).collect();
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        ifft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        assert_eq!(data, data1);

        let data = [Modint::from(817609646), Modint::from(512965573), Modint::zero(), Modint::zero()];
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        ifft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        assert_eq!(data, data1);
    }
}
