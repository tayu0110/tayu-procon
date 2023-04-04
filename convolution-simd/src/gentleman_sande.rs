use super::common::*;
use crate::fft_cache::FftCache;
use montgomery_modint::{Modulo, MontgomeryModint};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{_mm256_loadu_si256, _mm256_set1_epi32, _mm256_storeu_si256};

type Modint<M> = MontgomeryModint<M>;

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn gentleman_sande_radix_2_kernel<M: Modulo>(deg: usize, width: usize, offset: usize, a: &mut [Modint<M>], rate: &[Modint<M>]) {
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
#[target_feature(enable = "avx2")]
unsafe fn gentleman_sande_radix_4_kernel<M: Modulo>(deg: usize, width: usize, offset: usize, im: Modint<M>, a: &mut [Modint<M>], rate: &[Modint<M>]) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    let imag = _mm256_set1_epi32(im.val as i32);
    let modulo = _mm256_set1_epi32(M::MOD as i32);
    let modulo_inv = _mm256_set1_epi32(M::MOD_INV as i32);
    if blocks == 1 {
        if offset == 1 {
            let (c0, c1, c2, c3) = (a[0], a[0 + 1], a[0 + 1 * 2], a[0 + 1 * 3]);
            let c01 = c0 + c1;
            let c01n = c0 - c1;
            let c23 = c2 + c3;
            let c23nim = (c2 - c3) * im;
            a[0] = c01 + c23;
            a[0 + 1] = c01n + c23nim;
            a[0 + 1 * 2] = c01 - c23;
            a[0 + 1 * 3] = c01n - c23nim;
        } else if offset < 8 {
            for now in 0..offset {
                let (c0, c1, c2, c3) = (a[now], a[now + offset], a[now + offset * 2], a[now + offset * 3]);
                let c01 = c0 + c1;
                let c01n = c0 - c1;
                let c23 = c2 + c3;
                let c23nim = (c2 - c3) * im;
                a[now] = c01 + c23;
                a[now + offset] = c01n + c23nim;
                a[now + offset * 2] = c01 - c23;
                a[now + offset * 3] = c01n - c23nim;
            }
        } else {
            for now in (0..offset).step_by(8) {
                let c0 = _mm256_loadu_si256(a[now..now + 8].as_ptr() as _);
                let c1 = _mm256_loadu_si256(a[now + offset..now + offset + 8].as_ptr() as _);
                let c2 = _mm256_loadu_si256(a[now + offset * 2..now + offset * 2 + 8].as_ptr() as _);
                let c3 = _mm256_loadu_si256(a[now + offset * 3..now + offset * 3 + 8].as_ptr() as _);
                let c01 = _mm256_add_mod_epi32(c0, c1, modulo);
                let c01n = _mm256_sub_mod_epi32(c0, c1, modulo);
                let c23 = _mm256_add_mod_epi32(c2, c3, modulo);
                let c23nim = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c2, c3, modulo), imag, modulo, modulo_inv);
                _mm256_storeu_si256(a[now..now + 8].as_mut_ptr() as _, _mm256_add_mod_epi32(c01, c23, modulo));
                _mm256_storeu_si256(a[now + offset..now + offset + 8].as_mut_ptr() as _, _mm256_add_mod_epi32(c01n, c23nim, modulo));
                _mm256_storeu_si256(a[now + offset * 2..now + offset * 2 + 8].as_mut_ptr() as _, _mm256_sub_mod_epi32(c01, c23, modulo));
                _mm256_storeu_si256(a[now + offset * 3..now + offset * 3 + 8].as_mut_ptr() as _, _mm256_sub_mod_epi32(c01n, c23nim, modulo));
            }
        }
    } else {
        if offset < 8 {
            for block in 0..blocks {
                let top = block * width;
                let rot2 = rot * rot;
                let rot3 = rot * rot2;
                for now in top..top + offset {
                    let (c0, c1, c2, c3) = (a[now], a[now + offset], a[now + offset * 2], a[now + offset * 3]);
                    let c01 = c0 + c1;
                    let c01n = c0 - c1;
                    let c23 = c2 + c3;
                    let c23nim = (c2 - c3) * im;
                    a[now] = c01 + c23;
                    a[now + offset] = (c01n + c23nim) * rot;
                    a[now + offset * 2] = (c01 - c23) * rot2;
                    a[now + offset * 3] = (c01n - c23nim) * rot3;
                }
                if top + width != deg {
                    rot *= rate[block.trailing_ones() as usize];
                }
            }
        } else {
            let mut rot = _mm256_set1_epi32(rot.val as i32);
            for block in 0..blocks {
                let top = block * width;
                let rot2 = montgomery_multiplication_u32x8(rot, rot, modulo, modulo_inv);
                let rot3 = montgomery_multiplication_u32x8(rot, rot2, modulo, modulo_inv);
                for now in (top..top + offset).step_by(8) {
                    let c0 = _mm256_loadu_si256(a[now..now + 8].as_ptr() as _);
                    let c1 = _mm256_loadu_si256(a[now + offset..now + offset + 8].as_ptr() as _);
                    let c2 = _mm256_loadu_si256(a[now + offset * 2..now + offset * 2 + 8].as_ptr() as _);
                    let c3 = _mm256_loadu_si256(a[now + offset * 3..now + offset * 3 + 8].as_ptr() as _);
                    let c01 = _mm256_add_mod_epi32(c0, c1, modulo);
                    let c01n = _mm256_sub_mod_epi32(c0, c1, modulo);
                    let c23 = _mm256_add_mod_epi32(c2, c3, modulo);
                    let c23nim = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c2, c3, modulo), imag, modulo, modulo_inv);
                    _mm256_storeu_si256(a[now..now + 8].as_mut_ptr() as _, _mm256_add_mod_epi32(c01, c23, modulo));
                    _mm256_storeu_si256(
                        a[now + offset..now + offset + 8].as_mut_ptr() as _,
                        montgomery_multiplication_u32x8(_mm256_add_mod_epi32(c01n, c23nim, modulo), rot, modulo, modulo_inv),
                    );
                    _mm256_storeu_si256(
                        a[now + offset * 2..now + offset * 2 + 8].as_mut_ptr() as _,
                        montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c01, c23, modulo), rot2, modulo, modulo_inv),
                    );
                    _mm256_storeu_si256(
                        a[now + offset * 3..now + offset * 3 + 8].as_mut_ptr() as _,
                        montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c01n, c23nim, modulo), rot3, modulo, modulo_inv),
                    );
                }
                if top + width != deg {
                    rot = montgomery_multiplication_u32x8(rot, _mm256_set1_epi32(rate[block.trailing_ones() as usize].val as i32), modulo, modulo_inv);
                }
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn gentleman_sande_radix_4_butterfly<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    if log & 1 != 0 {
        let width = 1 << 1;
        let offset = width >> 1;
        gentleman_sande_radix_2_kernel(deg, width, offset, a, &cache.rate2);
    }
    for i in (log & 1..log).step_by(2) {
        let width = 1 << (i + 2);
        let offset = width >> 2;
        gentleman_sande_radix_4_kernel(deg, width, offset, cache.root[2], a, &cache.rate3);
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn gentleman_sande_radix_4_butterfly_inv<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    if log & 1 != 0 {
        let width = 1 << 1;
        let offset = width >> 1;
        gentleman_sande_radix_2_kernel(deg, width, offset, a, &cache.irate2);
    }
    for i in (log & 1..log).step_by(2) {
        let width = 1 << (i + 2);
        let offset = width >> 2;
        gentleman_sande_radix_4_kernel(deg, width, offset, cache.iroot[2], a, &cache.irate3);
    }
}

#[cfg(test)]
mod tests {
    use super::{gentleman_sande_radix_4_butterfly, gentleman_sande_radix_4_butterfly_inv};
    use crate::common::bit_reverse;
    use crate::FftCache;
    use montgomery_modint::{Mod998244353, MontgomeryModint};

    type Modint = MontgomeryModint<Mod998244353>;

    pub fn ntt_gentleman_sande_radix_4(a: &mut [Modint]) {
        let deg = a.len();
        let log = deg.trailing_zeros() as usize;
        debug_assert_eq!(a.len(), 1 << log);
        bit_reverse(deg, a);
        let cache = FftCache::<Mod998244353>::new();
        unsafe { gentleman_sande_radix_4_butterfly(deg, log, a, &cache) }
    }
    pub fn intt_gentleman_sande_radix_4(a: &mut [Modint]) {
        let deg = a.len();
        let log = deg.trailing_zeros() as usize;
        debug_assert_eq!(a.len(), 1 << log);
        bit_reverse(deg, a);
        let cache = FftCache::<Mod998244353>::new();
        unsafe { gentleman_sande_radix_4_butterfly_inv(deg, log, a, &cache) }
        let inv = Modint::new(deg as u32).inv();
        a.iter_mut().for_each(|c| *c *= inv)
    }

    #[test]
    fn gentleman_sande_radix_4_test() {
        for i in 0..=13 {
            let n = 1 << i;
            let data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
            let mut data1 = data.clone();
            ntt_gentleman_sande_radix_4(&mut data1);
            intt_gentleman_sande_radix_4(&mut data1);
            assert_eq!(data, data1);
        }
    }

    use crate::test::Bencher;
    #[bench]
    fn gentleman_sande_radix_4_bench(b: &mut Bencher) {
        b.iter(|| {
            for i in 15..=20 {
                let n = 1 << i;
                let mut data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
                ntt_gentleman_sande_radix_4(&mut data);
                intt_gentleman_sande_radix_4(&mut data);
            }
        })
    }
}
