use super::common::*;
use super::FftCache;
use modint::{Modulo, MontgomeryModint};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    _mm256_castsi256_si128, _mm256_extracti128_si256, _mm256_load_si256, _mm256_loadu_si256, _mm256_set1_epi32, _mm256_set_epi32, _mm256_set_m128i, _mm256_shuffle_epi32, _mm256_storeu_si256,
    _mm256_unpackhi_epi32, _mm256_unpacklo_epi32, _mm256_unpacklo_epi64,
};

type Modint<M> = MontgomeryModint<M>;

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn radix_2_kernel_cooley_tukey_avx2<M: Modulo>(width: usize, a: &mut [Modint<M>]) {
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
pub unsafe fn radix_4_kernel_cooley_tukey_avx2<M: Modulo>(deg: usize, width: usize, a: &mut [Modint<M>], twiddle: &[Modint<M>]) {
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
            let (c0, c1, c2, c3) = (*a.get_unchecked(0), *a.get_unchecked(2), *a.get_unchecked(1), *a.get_unchecked(3));
            let (c0, c1, c2, c3) = {
                let c0pc2 = c0 + c2;
                let c0mc2 = c0 - c2;
                let c1pc3 = c1 + c3;
                let c1mc3 = c1 - c3;
                let c1mc3im = c1mc3 * prim_root;
                (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
            };
            *a.get_unchecked_mut(0) = c0;
            *a.get_unchecked_mut(1) = c1;
            *a.get_unchecked_mut(2) = c2;
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

        for a in a.chunks_exact_mut(8) {
            let c0213 = _mm256_loadu_si256(a.as_ptr() as *const _);
            let c0213 = montgomery_multiplication_u32x8(w, c0213, modulo, modulo_inv);

            let (c0, c1) = {
                let c01 = _mm256_shuffle_epi32(c0213, 0b11_01_10_00);
                (_mm256_castsi256_si128(c01), _mm256_extracti128_si256(c01, 1))
            };
            let (c2, c3) = {
                let c23 = _mm256_shuffle_epi32(c0213, 0b01_11_00_10);
                (_mm256_castsi256_si128(c23), _mm256_extracti128_si256(c23, 1))
            };

            let (c0, c1, c2, c3) = radix_4_innerx4_sse(c0, c1, c2, c3, _mm256_castsi256_si128(modulo), _mm256_castsi256_si128(modulo_inv), _mm256_castsi256_si128(prim_root));

            // c0       = [c00, 0, c10, 0, 0, 0, 0, 0], c2 = [c02, 0, c12, 0, 0, 0, 0, 0]
            // c02      = [c00, 0, c10, 0, c02, 0, c12, 0]
            let c02 = _mm256_set_m128i(c2, c0);
            // c1       = [c01, 0, c11, 0, 0, 0, 0, 0], c3 = [c03, 0, c13, 0, 0, 0, 0, 0]
            // c13      = [c01, 0, c11, 0, c03, 0, c13, 0]
            let c13 = _mm256_set_m128i(c3, c1);
            // c0123    = [c00, c01, c10, c11, c02, c03, c12, c13]
            let c0123 = _mm256_unpacklo_epi64(_mm256_unpacklo_epi32(c02, c13), _mm256_unpackhi_epi32(c02, c13));
            // c0123    = [c00, c10, c01, c11, c02, c12, c03, c13]
            let c0123 = _mm256_shuffle_epi32(c0123, 0b11_01_10_00);

            _mm256_storeu_si256(a.as_mut_ptr() as *mut _, c0123);
        }
    } else if offset == 4 {
        let w02 = &mut AlignedArrayu32x8 { val: [Modint::<M>::one().val; 8] }.val;
        let w13 = &mut AlignedArrayu32x8 { val: [0; 8] }.val;
        for (i, exp_now) in (0..4).map(|i| (i, (i * exp))) {
            w13[i] = twiddle[exp_now].val;
            w02[i + 4] = twiddle[exp_now * 2].val;
            w13[i + 4] = twiddle[exp_now * 3].val;
        }
        let w02 = _mm256_load_si256(w02.as_mut_ptr() as *mut _);
        let w13 = _mm256_load_si256(w13.as_mut_ptr() as *mut _);

        for a in a.chunks_exact_mut(16) {
            let c02 = _mm256_loadu_si256(a[0..8].as_ptr() as *const _);
            let c13 = _mm256_loadu_si256(a[8..].as_ptr() as *const _);

            let c02 = montgomery_multiplication_u32x8(w02, c02, modulo, modulo_inv);
            let c13 = montgomery_multiplication_u32x8(w13, c13, modulo, modulo_inv);

            let (c0, c1, c2, c3) = (
                _mm256_castsi256_si128(c02),
                _mm256_castsi256_si128(c13),
                _mm256_extracti128_si256(c02, 1),
                _mm256_extracti128_si256(c13, 1),
            );

            let (c0, c1, c2, c3) = radix_4_innerx4_sse(c0, c1, c2, c3, _mm256_castsi256_si128(modulo), _mm256_castsi256_si128(modulo_inv), _mm256_castsi256_si128(prim_root));

            _mm256_storeu_si256(a[0..8].as_mut_ptr() as *mut _, _mm256_set_m128i(c1, c0));
            _mm256_storeu_si256(a[8..].as_mut_ptr() as *mut _, _mm256_set_m128i(c3, c2));
        }
    } else {
        let w1 = &mut AlignedArrayu32x8 { val: [0; 8] }.val;
        let w2 = &mut AlignedArrayu32x8 { val: [0; 8] }.val;
        let w3 = &mut AlignedArrayu32x8 { val: [0; 8] }.val;
        for top in (0..deg).step_by(width) {
            let mut exp_now = 0;
            for (((v0, v1), v2), v3) in a[top..top + offset]
                .chunks_exact(8)
                .zip(a[top + offset * 2..top + offset * 3].chunks_exact(8))
                .zip(a[top + offset..top + offset * 2].chunks_exact(8))
                .zip(a[top + offset * 3..top + offset * 4].chunks_exact(8))
            {
                let c0 = _mm256_loadu_si256(v0.as_ptr() as *const _);
                let c1 = _mm256_loadu_si256(v1.as_ptr() as *const _);
                let c2 = _mm256_loadu_si256(v2.as_ptr() as *const _);
                let c3 = _mm256_loadu_si256(v3.as_ptr() as *const _);

                for i in 0..8 {
                    *w1.get_unchecked_mut(i) = twiddle.get_unchecked(exp_now).val;
                    *w2.get_unchecked_mut(i) = twiddle.get_unchecked(exp_now * 2).val;
                    *w3.get_unchecked_mut(i) = twiddle.get_unchecked(exp_now * 3).val;
                    exp_now += exp;
                }
                let (w1, w2, w3) = (
                    _mm256_load_si256(w1.as_ptr() as *const _),
                    _mm256_load_si256(w2.as_ptr() as *const _),
                    _mm256_load_si256(w3.as_ptr() as *const _),
                );

                let c1 = montgomery_multiplication_u32x8(w1, c1, modulo, modulo_inv);
                let c2 = montgomery_multiplication_u32x8(w2, c2, modulo, modulo_inv);
                let c3 = montgomery_multiplication_u32x8(w3, c3, modulo, modulo_inv);

                let (c0, c1, c2, c3) = radix_4_innerx8(c0, c1, c2, c3, modulo, modulo_inv, prim_root);

                _mm256_storeu_si256(v0.as_ptr() as *mut _, c0);
                _mm256_storeu_si256(v2.as_ptr() as *mut _, c1);
                _mm256_storeu_si256(v1.as_ptr() as *mut _, c2);
                _mm256_storeu_si256(v3.as_ptr() as *mut _, c3);
            }
        }
    }
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
#[target_feature(enable = "avx")]
#[target_feature(enable = "avx2")]
pub unsafe fn cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<Modint<M>>) {
    let twiddle = cache.twiddle_factors_inv();
    assert_eq!(twiddle[(twiddle.len() - 1) >> 2], cache.prim_root_inv(2));
    let start = if log & 1 != 0 {
        radix_2_kernel_cooley_tukey_avx2(1 << 1, a);
        1
    } else {
        0
    };
    for i in (start..log).step_by(2) {
        let width = 1 << (i + 2);
        radix_4_kernel_cooley_tukey_avx2(deg, width, a, twiddle);
    }
}

#[cfg(test)]
mod tests_cooley_tukey {
    use super::super::FftCache;
    use super::{cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2, radix_2_kernel_cooley_tukey_avx2, radix_4_kernel_cooley_tukey_avx2};
    use modint::{Mod998244353, MontgomeryModint};

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
    pub unsafe fn cooley_tukey_radix_4_butterfly_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Modint], cache: &FftCache<Modint>) {
        let twiddle = cache.twiddle_factors();
        let start = if log & 1 != 0 {
            radix_2_kernel_cooley_tukey_avx2(1 << 1, a);
            1
        } else {
            0
        };
        for i in (start..log).step_by(2) {
            let width = 1 << (i + 2);
            radix_4_kernel_cooley_tukey_avx2(deg, width, a, twiddle);
        }
    }

    macro_rules! impl_fft_inner {
        ( $t:ty, $butterfly:ident, $deg:ident, $log:ident, $a:ident, $cache:ident, $epilogue:expr ) => {{
            unsafe {
                $butterfly($deg, $log, $a, &($cache));
            }
            $epilogue($deg, $a);
        }};
    }

    macro_rules! impl_fft_template {
        ( $t:ty, $fname:ident, $butterfly:ident, $inner:expr ) => {
            pub fn $fname(a: &mut [$t]) {
                let deg = a.len();
                let log = deg.trailing_zeros() as usize;
                debug_assert_eq!(a.len(), 1 << log);
                bit_reverse(deg, log, a);
                let cache = FftCache::<$t>::new(log);
                impl_fft_inner!($t, $butterfly, deg, log, a, cache, $inner)
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
        fft_cooley_tukey_radix_4_montgomery_modint_avx2,
        cooley_tukey_radix_4_butterfly_montgomery_modint_avx2,
        ifft_cooley_tukey_radix_4_montgomery_modint_avx2,
        cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2,
        |deg: usize, a: &mut [Modint]| {
            let inv = Modint::new(deg as u32).inv();
            a.iter_mut().for_each(|c| *c *= inv)
        }
    );

    const N: u32 = 1 << 13;

    #[test]
    fn cooley_tukey_radix_4_montgomery_modint_test() {
        let data: Vec<Modint> = (1..=N).map(|v| Modint::new(v)).collect();
        let mut data1 = data.clone();
        fft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        ifft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        assert_eq!(data, data1);

        let data = [Modint::from(817609646), Modint::from(512965573), Modint::zero(), Modint::zero()];
        let mut data1 = data.clone();
        fft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        ifft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        assert_eq!(data, data1);
    }
}
