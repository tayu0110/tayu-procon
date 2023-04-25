use super::FftCache;
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    _mm256_loadu_si256, _mm256_permute2f128_si256, _mm256_permute4x64_epi64, _mm256_setr_epi32, _mm256_shuffle_epi32, _mm256_storeu_si256, _mm256_unpackhi_epi32, _mm256_unpackhi_epi64,
    _mm256_unpacklo_epi32, _mm256_unpacklo_epi64,
};

type Modint<M> = MontgomeryModint<M>;

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn cooley_tukey_radix_2_kernel<M: Modulo>(deg: usize, width: usize, offset: usize, a: &mut [Modint<M>], rate: &[Modint<M>]) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    if offset == 1 && blocks >= 8 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 2, 4, 6, 8, 10, 12, 14);
        for block in (0..blocks).step_by(8) {
            let top = block * width;
            for i in 0..8 {
                r[i] = rot;
                if block + i + 1 != blocks {
                    rot *= rate[(!(block + i)).trailing_zeros() as usize];
                }
            }
            let rot = MontgomeryModintx8::load_ptr(r.as_ptr());
            let c0 = MontgomeryModintx8::gather_ptr(a[top..].as_ptr(), vindex);
            let c1 = MontgomeryModintx8::gather_ptr(a[top + 1..].as_ptr(), vindex) * rot;
            let (c0, c1) = (c0 + c1, c0 - c1);
            let r0 = _mm256_unpacklo_epi32(c0.rawval(), c1.rawval());
            let r1 = _mm256_unpackhi_epi32(c0.rawval(), c1.rawval());
            _mm256_storeu_si256(a[top..].as_mut_ptr() as _, _mm256_permute2f128_si256(r0, r1, 0x20));
            _mm256_storeu_si256(a[top + 8..].as_mut_ptr() as _, _mm256_permute2f128_si256(r0, r1, 0x31));
        }
    } else {
        for block in 0..blocks {
            let top = block * width;
            for now in top..top + offset {
                let c = a[now + offset] * rot;
                a[now + offset] = a[now] - c;
                a[now] += c;
            }
            if top + width != deg {
                rot *= rate[(!block).trailing_zeros() as usize];
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn cooley_tukey_radix_4_kernel<M: Modulo>(deg: usize, width: usize, offset: usize, im: Modint<M>, a: &mut [Modint<M>], rate: &[Modint<M>]) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    let imag = MontgomeryModintx8::splat_raw(im);

    if offset == 1 && blocks >= 8 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 4, 8, 12, 16, 20, 24, 28);
        for block in (0..blocks).step_by(8) {
            let top = block * width;
            for i in 0..8 {
                r[i] = rot;
                if block + i != blocks {
                    rot *= rate[(!(block + i)).trailing_zeros() as usize];
                }
            }
            let rot = MontgomeryModintx8::<M>::load(&r);
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let c0 = MontgomeryModintx8::gather_ptr(a[top..].as_ptr(), vindex);
            let c1 = MontgomeryModintx8::gather_ptr(a[top + 1..].as_ptr(), vindex) * rot;
            let c2 = MontgomeryModintx8::gather_ptr(a[top + 2..].as_ptr(), vindex) * rot2;
            let c3 = MontgomeryModintx8::gather_ptr(a[top + 3..].as_ptr(), vindex) * rot3;
            let c02 = c0 + c2;
            let c02n = c0 - c2;
            let c13 = c1 + c3;
            let c13nim = (c1 - c3) * imag;
            let (r0, r1, r2, r3) = (c02 + c13, c02 - c13, c02n + c13nim, c02n - c13nim);
            let r01lo = _mm256_unpacklo_epi32(r0.rawval(), r1.rawval());
            let r01hi = _mm256_unpackhi_epi32(r0.rawval(), r1.rawval());
            let r23lo = _mm256_unpacklo_epi32(r2.rawval(), r3.rawval());
            let r23hi = _mm256_unpackhi_epi32(r2.rawval(), r3.rawval());
            let r01lo = _mm256_permute4x64_epi64(r01lo, 0b11_01_10_00);
            let r01hi = _mm256_permute4x64_epi64(r01hi, 0b11_01_10_00);
            let r23lo = _mm256_permute4x64_epi64(r23lo, 0b11_01_10_00);
            let r23hi = _mm256_permute4x64_epi64(r23hi, 0b11_01_10_00);
            _mm256_storeu_si256(a[top..].as_mut_ptr() as _, _mm256_unpacklo_epi64(r01lo, r23lo));
            _mm256_storeu_si256(a[top + 8..].as_mut_ptr() as _, _mm256_unpacklo_epi64(r01hi, r23hi));
            _mm256_storeu_si256(a[top + 16..].as_mut_ptr() as _, _mm256_unpackhi_epi64(r01lo, r23lo));
            _mm256_storeu_si256(a[top + 24..].as_mut_ptr() as _, _mm256_unpackhi_epi64(r01hi, r23hi));
        }
    } else if offset == 2 && blocks >= 4 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 1, 8, 9, 16, 17, 24, 25);
        for block in (0..blocks).step_by(4) {
            let top = block * width;
            for i in 0..4 {
                r[i * 2] = rot;
                r[i * 2 + 1] = rot;
                if block + i + 1 != blocks {
                    rot *= rate[(!(block + i)).trailing_zeros() as usize];
                }
            }
            let rot = MontgomeryModintx8::<M>::load(&r);
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let c0 = MontgomeryModintx8::gather_ptr(a[top..].as_ptr(), vindex);
            let c1 = MontgomeryModintx8::gather_ptr(a[top + 2..].as_ptr(), vindex) * rot;
            let c2 = MontgomeryModintx8::gather_ptr(a[top + 4..].as_ptr(), vindex) * rot2;
            let c3 = MontgomeryModintx8::gather_ptr(a[top + 6..].as_ptr(), vindex) * rot3;
            let c02 = c0 + c2;
            let c02n = c0 - c2;
            let c13 = c1 + c3;
            let c13nim = (c1 - c3) * imag;
            let (r0, r1, r2, r3) = (c02 + c13, c02 - c13, c02n + c13nim, c02n - c13nim);
            let r01lo = _mm256_unpacklo_epi64(r0.rawval(), r1.rawval());
            let r01hi = _mm256_unpackhi_epi64(r0.rawval(), r1.rawval());
            let r23lo = _mm256_unpacklo_epi64(r2.rawval(), r3.rawval());
            let r23hi = _mm256_unpackhi_epi64(r2.rawval(), r3.rawval());
            _mm256_storeu_si256(a[top..].as_mut_ptr() as _, _mm256_permute2f128_si256(r01lo, r23lo, 0x20));
            _mm256_storeu_si256(a[top + 8..].as_mut_ptr() as _, _mm256_permute2f128_si256(r01hi, r23hi, 0x20));
            _mm256_storeu_si256(a[top + 16..].as_mut_ptr() as _, _mm256_permute2f128_si256(r01lo, r23lo, 0x31));
            _mm256_storeu_si256(a[top + 24..].as_mut_ptr() as _, _mm256_permute2f128_si256(r01hi, r23hi, 0x31));
        }
    } else if offset == 4 && blocks >= 2 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 1, 2, 3, 16, 17, 18, 19);
        for block in (0..blocks).step_by(2) {
            let top = block * width;
            r[0] = rot;
            rot *= rate[(!block).trailing_zeros() as usize];
            r[4] = rot;
            if block + 2 != blocks {
                rot *= rate[(!(block + 1)).trailing_zeros() as usize];
            }
            let rot = MontgomeryModintx8::<M>::from_rawval(_mm256_shuffle_epi32(_mm256_loadu_si256(r.as_ptr() as _), 0b00_00_00_00));
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let c0 = MontgomeryModintx8::gather_ptr(a[top..].as_ptr(), vindex);
            let c1 = MontgomeryModintx8::gather_ptr(a[top + 4..].as_ptr(), vindex) * rot;
            let c2 = MontgomeryModintx8::gather_ptr(a[top + 8..].as_ptr(), vindex) * rot2;
            let c3 = MontgomeryModintx8::gather_ptr(a[top + 12..].as_ptr(), vindex) * rot3;
            let c02 = c0 + c2;
            let c02n = c0 - c2;
            let c13 = c1 + c3;
            let c13nim = (c1 - c3) * imag;
            let (r0, r1, r2, r3) = (c02 + c13, c02 - c13, c02n + c13nim, c02n - c13nim);
            _mm256_storeu_si256(a[top..].as_mut_ptr() as _, _mm256_permute2f128_si256(r0.rawval(), r1.rawval(), 0x20));
            _mm256_storeu_si256(a[top + 8..].as_mut_ptr() as _, _mm256_permute2f128_si256(r2.rawval(), r3.rawval(), 0x20));
            _mm256_storeu_si256(a[top + 16..].as_mut_ptr() as _, _mm256_permute2f128_si256(r0.rawval(), r1.rawval(), 0x31));
            _mm256_storeu_si256(a[top + 24..].as_mut_ptr() as _, _mm256_permute2f128_si256(r2.rawval(), r3.rawval(), 0x31));
        }
    } else if offset < 8 {
        for block in 0..blocks {
            let top = block * width;
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            for now in top..top + offset {
                let (c0, c1, c2, c3) = (a[now], a[now + offset] * rot, a[now + offset * 2] * rot2, a[now + offset * 3] * rot3);
                let c02 = c0 + c2;
                let c02n = c0 - c2;
                let c13 = c1 + c3;
                let c13nim = (c1 - c3) * im;
                a[now] = c02 + c13;
                a[now + offset] = c02 - c13;
                a[now + offset * 2] = c02n + c13nim;
                a[now + offset * 3] = c02n - c13nim;
            }
            if top + width != deg {
                rot *= rate[(!block).trailing_zeros() as usize];
            }
        }
    } else {
        let mut head = a.as_mut_ptr();
        for _ in (0..offset).step_by(8) {
            let c0 = MontgomeryModintx8::<M>::load_ptr(head);
            let c1 = MontgomeryModintx8::<M>::load_ptr(head.add(offset));
            let c2 = MontgomeryModintx8::<M>::load_ptr(head.add(offset * 2));
            let c3 = MontgomeryModintx8::<M>::load_ptr(head.add(offset * 3));
            let c02 = c0 + c2;
            let c02n = c0 - c2;
            let c13 = c1 + c3;
            let c13nim = (c1 - c3) * imag;
            (c02 + c13).store_ptr(head);
            (c02 - c13).store_ptr(head.add(offset));
            (c02n + c13nim).store_ptr(head.add(offset * 2));
            (c02n - c13nim).store_ptr(head.add(offset * 3));
            head = head.add(8);
        }
        let mut rot = MontgomeryModintx8::<M>::splat_raw(rate[0]);
        for block in 1..blocks {
            let top = block * width;
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let mut head = a[top..].as_mut_ptr();
            for _ in (top..top + offset).step_by(8) {
                let (c0a, c1a, c2a, c3a) = (head, head.add(offset), head.add(offset * 2), head.add(offset * 3));
                let c0 = MontgomeryModintx8::load_ptr(c0a);
                let c1 = MontgomeryModintx8::load_ptr(c1a) * rot;
                let c2 = MontgomeryModintx8::load_ptr(c2a) * rot2;
                let c3 = MontgomeryModintx8::load_ptr(c3a) * rot3;
                let c02 = c0 + c2;
                let c02n = c0 - c2;
                let c13 = c1 + c3;
                let c13nim = (c1 - c3) * imag;
                (c02 + c13).store_ptr(c0a);
                (c02 - c13).store_ptr(c1a);
                (c02n + c13nim).store_ptr(c2a);
                (c02n - c13nim).store_ptr(c3a);
                head = head.add(8);
            }
            if top + width != deg {
                rot = rot * MontgomeryModintx8::splat_raw(rate[(!block).trailing_zeros() as usize]);
            }
        }
    }
}

#[inline]
pub unsafe fn cooley_tukey_radix_4_butterfly<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    for i in (0..log).step_by(2) {
        let width = deg >> i;
        if i + 1 == log {
            let offset = width >> 1;
            cooley_tukey_radix_2_kernel(deg, width, offset, a, &cache.rate2);
        } else {
            let offset = width >> 2;
            cooley_tukey_radix_4_kernel(deg, width, offset, cache.root[2], a, &cache.rate3);
        }
    }
}

#[inline]
pub unsafe fn cooley_tukey_radix_4_butterfly_inv<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    for i in (0..log).step_by(2) {
        let width = deg >> i;
        if i + 1 == log {
            let offset = width >> 1;
            cooley_tukey_radix_2_kernel(deg, width, offset, a, &cache.irate2);
        } else {
            let offset = width >> 2;
            cooley_tukey_radix_4_kernel(deg, width, offset, cache.iroot[2], a, &cache.irate3);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::common::bit_reverse;
    use super::{cooley_tukey_radix_4_butterfly, cooley_tukey_radix_4_butterfly_inv};
    use crate::fft_cache::FftCache;
    use montgomery_modint::{Mod998244353, MontgomeryModint};

    type Modint = MontgomeryModint<Mod998244353>;

    pub fn ntt_cooley_tukey_radix_4(a: &mut [Modint]) {
        let deg = a.len();
        let log = deg.trailing_zeros() as usize;
        debug_assert_eq!(a.len(), 1 << log);
        let cache = FftCache::new();
        unsafe { cooley_tukey_radix_4_butterfly(deg, log, a, &cache) }
        bit_reverse(deg, a);
    }

    pub fn intt_cooley_tukey_radix_4(a: &mut [Modint]) {
        let deg = a.len();
        let log = deg.trailing_zeros() as usize;
        debug_assert_eq!(a.len(), 1 << log);
        let cache = FftCache::new();
        unsafe { cooley_tukey_radix_4_butterfly_inv(deg, log, a, &cache) }
        bit_reverse(deg, a);
        let inv = Modint::new(deg as u32).inv();
        a.iter_mut().for_each(|c| *c *= inv)
    }

    #[test]
    fn cooley_tukey_radix_4_test() {
        for i in 0..=13 {
            let n = 1 << i;
            let data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
            let mut data1 = data.clone();
            ntt_cooley_tukey_radix_4(&mut data1);
            intt_cooley_tukey_radix_4(&mut data1);
            assert_eq!(data, data1);
        }
    }

    use crate::test::Bencher;
    #[bench]
    fn cooley_tukey_radix_4_bench(b: &mut Bencher) {
        b.iter(|| {
            for i in 15..=20 {
                let n = 1 << i;
                let mut data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
                ntt_cooley_tukey_radix_4(&mut data);
                intt_cooley_tukey_radix_4(&mut data);
            }
        })
    }
}
