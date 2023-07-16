use crate::fft_cache::FftCache;
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    _mm256_permute2f128_si256 as permute2f128, _mm256_permute4x64_epi64 as permute4x64, _mm256_setr_epi32, _mm256_storeu_si256 as storeu, _mm256_unpackhi_epi32 as unpackhi32,
    _mm256_unpackhi_epi64 as unpackhi64, _mm256_unpacklo_epi32 as unpacklo32, _mm256_unpacklo_epi64 as unpacklo64,
};

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

macro_rules! radix4_inner {
    ($c0:expr, $c1:expr, $c2:expr, $c3:expr, $rot:expr, $rot2:expr, $rot3:expr, $imag:expr) => {
        {
            let (c0, c1, c2, c3) = ($c0, $c1, $c2, $c3);
            let c01 = c0 + c1;
            let c01n = c0 - c1;
            let c23 = c2 + c3;
            let c23nim = (c2 - c3) * $imag;
            (c01 + c23, (c01n + c23nim) * $rot, (c01 - c23) * $rot2, (c01n - c23nim) * $rot3)
        }
    };
}

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
                rot *= rate[(!(block + i)).trailing_zeros() as usize];
            }
            let rot = Modintx8::load_ptr(r.as_ptr());
            let c0 = Modintx8::gather_ptr(a[top..].as_ptr(), vindex);
            let c1 = Modintx8::gather_ptr(a[top + 1..].as_ptr(), vindex);

            let (c0, c1) = (c0 + c1, (c0 - c1) * rot);
            let r0 = unpacklo32(c0.rawval(), c1.rawval());
            let r1 = unpackhi32(c0.rawval(), c1.rawval());
            storeu(a[top..].as_mut_ptr() as _, permute2f128(r0, r1, 0x20));
            storeu(a[top + 8..].as_mut_ptr() as _, permute2f128(r0, r1, 0x31));
        }
    } else {
        for block in 0..blocks {
            let top = block * width;
            for now in top..top + offset {
                let c = a[now + offset];
                a[now + offset] = (a[now] - c) * rot;
                a[now] += c;
            }
            rot *= rate[(!block).trailing_zeros() as usize];
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn cooley_tukey_radix_4_kernel<M: Modulo>(deg: usize, width: usize, offset: usize, im: Modint<M>, a: &mut [Modint<M>], rate: &[Modint<M>]) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    let imag = Modintx8::splat_raw(im);

    if offset == 1 && blocks >= 8 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 4, 8, 12, 16, 20, 24, 28);
        for block in (0..blocks).step_by(8) {
            let top = block * width;
            for i in 0..8 {
                r[i] = rot;
                rot *= rate[(!(block + i)).trailing_zeros() as usize];
            }
            let rot = Modintx8::load_ptr(r.as_ptr());
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let (r0, r1, r2, r3) = radix4_inner!(
                Modintx8::gather_ptr(a[top..].as_ptr(), vindex),
                Modintx8::gather_ptr(a[top + 1..].as_ptr(), vindex),
                Modintx8::gather_ptr(a[top + 2..].as_ptr(), vindex),
                Modintx8::gather_ptr(a[top + 3..].as_ptr(), vindex),
                rot,
                rot2,
                rot3,
                imag
            );
            let r01lo = unpacklo32(r0.rawval(), r1.rawval());
            let r01hi = unpackhi32(r0.rawval(), r1.rawval());
            let r23lo = unpacklo32(r2.rawval(), r3.rawval());
            let r23hi = unpackhi32(r2.rawval(), r3.rawval());
            let r01lo = permute4x64(r01lo, 0b11_01_10_00);
            let r01hi = permute4x64(r01hi, 0b11_01_10_00);
            let r23lo = permute4x64(r23lo, 0b11_01_10_00);
            let r23hi = permute4x64(r23hi, 0b11_01_10_00);
            storeu(a[top..].as_mut_ptr() as _, unpacklo64(r01lo, r23lo));
            storeu(a[top + 8..].as_mut_ptr() as _, unpacklo64(r01hi, r23hi));
            storeu(a[top + 16..].as_mut_ptr() as _, unpackhi64(r01lo, r23lo));
            storeu(a[top + 24..].as_mut_ptr() as _, unpackhi64(r01hi, r23hi));
        }
    } else if offset == 2 && blocks >= 4 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 1, 8, 9, 16, 17, 24, 25);
        for block in (0..blocks).step_by(4) {
            let top = block * width;
            for i in 0..4 {
                r[i * 2] = rot;
                r[i * 2 + 1] = rot;
                rot *= rate[(!(block + i)).trailing_zeros() as usize];
            }
            let rot = Modintx8::load_ptr(r.as_ptr());
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let (r0, r1, r2, r3) = radix4_inner!(
                Modintx8::gather_ptr(a[top..].as_ptr(), vindex),
                Modintx8::gather_ptr(a[top + 2..].as_ptr(), vindex),
                Modintx8::gather_ptr(a[top + 4..].as_ptr(), vindex),
                Modintx8::gather_ptr(a[top + 6..].as_ptr(), vindex),
                rot,
                rot2,
                rot3,
                imag
            );
            let r01lo = unpacklo64(r0.rawval(), r1.rawval());
            let r01hi = unpackhi64(r0.rawval(), r1.rawval());
            let r23lo = unpacklo64(r2.rawval(), r3.rawval());
            let r23hi = unpackhi64(r2.rawval(), r3.rawval());
            storeu(a[top..].as_mut_ptr() as _, permute2f128(r01lo, r23lo, 0x20));
            storeu(a[top + 8..].as_mut_ptr() as _, permute2f128(r01hi, r23hi, 0x20));
            storeu(a[top + 16..].as_mut_ptr() as _, permute2f128(r01lo, r23lo, 0x31));
            storeu(a[top + 24..].as_mut_ptr() as _, permute2f128(r01hi, r23hi, 0x31));
        }
    } else if offset == 4 && blocks >= 2 {
        let vindex = _mm256_setr_epi32(0, 1, 2, 3, 16, 17, 18, 19);
        for block in (0..blocks).step_by(2) {
            let top = block * width;
            let next_rot = rot * rate[(!block).trailing_zeros() as usize];
            {
                let rot = Modintx8::load_ptr([rot, rot, rot, rot, next_rot, next_rot, next_rot, next_rot].as_ptr());
                let rot2 = rot * rot;
                let rot3 = rot * rot2;
                let (r0, r1, r2, r3) = radix4_inner!(
                    Modintx8::gather_ptr(a[top..].as_ptr(), vindex),
                    Modintx8::gather_ptr(a[top + 4..].as_ptr(), vindex),
                    Modintx8::gather_ptr(a[top + 8..].as_ptr(), vindex),
                    Modintx8::gather_ptr(a[top + 12..].as_ptr(), vindex),
                    rot,
                    rot2,
                    rot3,
                    imag
                );
                storeu(a[top..].as_mut_ptr() as _, permute2f128(r0.rawval(), r1.rawval(), 0x20));
                storeu(a[top + 8..].as_mut_ptr() as _, permute2f128(r2.rawval(), r3.rawval(), 0x20));
                storeu(a[top + 16..].as_mut_ptr() as _, permute2f128(r0.rawval(), r1.rawval(), 0x31));
                storeu(a[top + 24..].as_mut_ptr() as _, permute2f128(r2.rawval(), r3.rawval(), 0x31));
            }
            rot = next_rot * rate[(!(block + 1)).trailing_zeros() as usize];
        }
    } else if offset < 8 {
        for block in 0..blocks {
            let top = block * width;
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            for now in top..top + offset {
                let (r0, r1, r2, r3) = radix4_inner!(a[now], a[now + offset], a[now + offset * 2], a[now + offset * 3], rot, rot2, rot3, im);
                a[now] = r0;
                a[now + offset] = r1;
                a[now + offset * 2] = r2;
                a[now + offset * 3] = r3;
            }
            rot *= rate[(!block).trailing_zeros() as usize];
        }
    } else {
        for now in (0..offset).step_by(8) {
            let c0 = Modintx8::load_ptr(a[now..].as_ptr());
            let c1 = Modintx8::load_ptr(a[now + offset..].as_ptr());
            let c2 = Modintx8::load_ptr(a[now + offset * 2..].as_ptr());
            let c3 = Modintx8::load_ptr(a[now + offset * 3..].as_ptr());
            let c01 = c0 + c1;
            let c01n = c0 - c1;
            let c23 = c2 + c3;
            let c23nim = (c2 - c3) * imag;
            (c01 + c23).store_ptr(a[now..].as_mut_ptr());
            (c01n + c23nim).store_ptr(a[now + offset..].as_mut_ptr());
            (c01 - c23).store_ptr(a[now + offset * 2..].as_mut_ptr());
            (c01n - c23nim).store_ptr(a[now + offset * 3..].as_mut_ptr());
        }
        let mut rot = Modintx8::<M>::splat_raw(rate[0]);
        for block in 1..blocks {
            let top = block * width;
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let mut head = a[top..].as_mut_ptr();
            for _ in (top..top + offset).step_by(8) {
                let (c0a, c1a, c2a, c3a) = (head, head.add(offset), head.add(offset * 2), head.add(offset * 3));
                let (r0, r1, r2, r3) = radix4_inner!(
                    Modintx8::load_ptr(c0a),
                    Modintx8::load_ptr(c1a),
                    Modintx8::load_ptr(c2a),
                    Modintx8::load_ptr(c3a),
                    rot,
                    rot2,
                    rot3,
                    imag
                );
                r0.store_ptr(c0a);
                r1.store_ptr(c1a);
                r2.store_ptr(c2a);
                r3.store_ptr(c3a);
                head = head.add(8);
            }
            rot = rot * Modintx8::splat_raw(rate[(!block).trailing_zeros() as usize]);
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn cooley_tukey_radix_4_butterfly<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    if log & 1 != 0 {
        let width = 1 << 1;
        let offset = width >> 1;
        cooley_tukey_radix_2_kernel(deg, width, offset, a, &cache.rate2);
    }
    for i in (log & 1..log).step_by(2) {
        let width = 1 << (i + 2);
        let offset = width >> 2;
        cooley_tukey_radix_4_kernel(deg, width, offset, cache.root[2], a, &cache.rate3);
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn cooley_tukey_radix_4_butterfly_inv<M: Modulo>(deg: usize, log: usize, a: &mut [Modint<M>], cache: &FftCache<M>) {
    if log & 1 != 0 {
        let width = 1 << 1;
        let offset = width >> 1;
        cooley_tukey_radix_2_kernel(deg, width, offset, a, &cache.irate2);
    }
    for i in (log & 1..log).step_by(2) {
        let width = 1 << (i + 2);
        let offset = width >> 2;
        cooley_tukey_radix_4_kernel(deg, width, offset, cache.iroot[2], a, &cache.irate3);
    }
}
