use super::FftCache;
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use montgomery_modint::MontgomeryModintx8;
use montgomery_modint::{Modulo, MontgomeryModint};
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use std::arch::x86_64::{
    _mm256_permute2f128_si256 as permute2f128, _mm256_permute4x64_epi64 as permute4x64,
    _mm256_setr_epi32, _mm256_storeu_si256 as storeu, _mm256_unpackhi_epi64 as unpackhi64,
    _mm256_unpacklo_epi64 as unpacklo64,
};

type Modint<M> = MontgomeryModint<M>;
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
type Modintx8<M> = MontgomeryModintx8<M>;

macro_rules! radix4_inner {
    ($c0:expr, $c1:expr, $c2:expr, $c3:expr, $imag:expr) => {
        {
            let (c0, c1, c2, c3) = ($c0, $c1, $c2, $c3);
            let c02 = c0 + c2;
            let c02n = c0 - c2;
            let c13 = c1 + c3;
            let c13nim = (c1 - c3) * $imag;
            (c02 + c13, c02 - c13, c02n + c13nim, c02n - c13nim)
        }
    };
}

#[cfg(not(feature = "simd"))]
#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
fn gentleman_sande_radix_2_kernel<M: Modulo>(
    deg: usize,
    width: usize,
    offset: usize,
    a: &mut [Modint<M>],
    rate: &[Modint<M>],
) {
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
                let c = a[now + offset] * rot;
                a[now + offset] = a[now] - c;
                a[now] += c;
            }
        }
        if top + width != deg {
            rot *= rate[block.trailing_ones() as usize];
        }
    }
}

#[cfg(not(feature = "simd"))]
#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
fn gentleman_sande_radix_4_kernel<M: Modulo>(
    deg: usize,
    width: usize,
    offset: usize,
    im: Modint<M>,
    a: &mut [Modint<M>],
    rate: &[Modint<M>],
) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    for block in 0..blocks {
        let top = block * width;
        let rot2 = rot * rot;
        let rot3 = rot * rot2;
        for now in top..top + offset {
            let (c0, c1, c2, c3) = (
                a[now],
                a[now + offset] * rot,
                a[now + offset * 2] * rot2,
                a[now + offset * 3] * rot3,
            );
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
            rot *= rate[block.trailing_ones() as usize];
        }
    }
}

#[target_feature(enable = "avx2", enable = "bmi1")]
#[cfg(feature = "simd")]
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
unsafe fn gentleman_sande_radix_2_kernel<M: Modulo>(
    deg: usize,
    width: usize,
    offset: usize,
    a: &mut [Modint<M>],
    rate: &[Modint<M>],
) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    if offset == 1 && blocks >= 8 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 2, 4, 6, 8, 10, 12, 14);
        for block in (0..blocks).step_by(8) {
            let top = block * width;
            for i in 0..8 {
                r[i] = rot;
                rot *= rate[(block + i).trailing_ones() as usize];
            }
            let rot = Modintx8::load(r.as_ptr());
            let c0 = Modintx8::gather(a[top..].as_ptr(), vindex);
            let c1 = Modintx8::gather(a[top + 1..].as_ptr(), vindex) * rot;
            let (c0, c1) = (c0 + c1, c0 - c1);
            let r0 = c0.unpacklo32(c1);
            let r1 = c0.unpackhi32(c1);
            storeu(
                a[top..].as_mut_ptr() as _,
                permute2f128::<0x20>(r0.rawval(), r1.rawval()),
            );
            storeu(
                a[top + 8..].as_mut_ptr() as _,
                permute2f128::<0x31>(r0.rawval(), r1.rawval()),
            );
        }
    } else {
        for block in 0..blocks {
            let top = block * width;
            for now in top..top + offset {
                let c = a[now + offset] * rot;
                a[now + offset] = a[now] - c;
                a[now] += c;
            }
            rot *= rate[block.trailing_ones() as usize];
        }
    }
}

#[cfg(feature = "simd")]
#[target_feature(enable = "avx2", enable = "bmi1")]
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
unsafe fn gentleman_sande_radix_4_kernel<M: Modulo>(
    deg: usize,
    width: usize,
    offset: usize,
    im: Modint<M>,
    a: &mut [Modint<M>],
    rate: &[Modint<M>],
) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    let imag = Modintx8::splat(im);

    if offset == 1 && blocks >= 8 {
        let mut r = [Modint::zero(); 8];
        let vindex = _mm256_setr_epi32(0, 4, 8, 12, 16, 20, 24, 28);
        for block in (0..blocks).step_by(8) {
            let top = block * width;
            for i in 0..8 {
                r[i] = rot;
                rot *= rate[(block + i).trailing_ones() as usize];
            }
            let rot = Modintx8::<M>::load(r.as_ptr());
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let (r0, r1, r2, r3) = radix4_inner!(
                Modintx8::gather(a[top..].as_ptr(), vindex),
                Modintx8::gather(a[top + 1..].as_ptr(), vindex) * rot,
                Modintx8::gather(a[top + 2..].as_ptr(), vindex) * rot2,
                Modintx8::gather(a[top + 3..].as_ptr(), vindex) * rot3,
                imag
            );
            let r01lo = r0.unpacklo32(r1);
            let r01hi = r0.unpackhi32(r1);
            let r23lo = r2.unpacklo32(r3);
            let r23hi = r2.unpackhi32(r3);
            let r01lo = permute4x64::<0b11_01_10_00>(r01lo.rawval());
            let r01hi = permute4x64::<0b11_01_10_00>(r01hi.rawval());
            let r23lo = permute4x64::<0b11_01_10_00>(r23lo.rawval());
            let r23hi = permute4x64::<0b11_01_10_00>(r23hi.rawval());
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
                rot *= rate[(block + i).trailing_ones() as usize];
            }
            let rot = Modintx8::<M>::load(r.as_ptr());
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let (r0, r1, r2, r3) = radix4_inner!(
                Modintx8::gather(a[top..].as_ptr(), vindex),
                Modintx8::gather(a[top + 2..].as_ptr(), vindex) * rot,
                Modintx8::gather(a[top + 4..].as_ptr(), vindex) * rot2,
                Modintx8::gather(a[top + 6..].as_ptr(), vindex) * rot3,
                imag
            );
            let r01lo = r0.unpacklo64(r1);
            let r01hi = r0.unpackhi64(r1);
            let r23lo = r2.unpacklo64(r3);
            let r23hi = r2.unpackhi64(r3);
            storeu(
                a[top..].as_mut_ptr() as _,
                permute2f128::<0x20>(r01lo.rawval(), r23lo.rawval()),
            );
            storeu(
                a[top + 8..].as_mut_ptr() as _,
                permute2f128::<0x20>(r01hi.rawval(), r23hi.rawval()),
            );
            storeu(
                a[top + 16..].as_mut_ptr() as _,
                permute2f128::<0x31>(r01lo.rawval(), r23lo.rawval()),
            );
            storeu(
                a[top + 24..].as_mut_ptr() as _,
                permute2f128::<0x31>(r01hi.rawval(), r23hi.rawval()),
            );
        }
    } else if offset == 4 && blocks >= 2 {
        let vindex = _mm256_setr_epi32(0, 1, 2, 3, 16, 17, 18, 19);
        for block in (0..blocks).step_by(2) {
            let top = block * width;
            let next_rot = rot * rate[block.trailing_ones() as usize];
            {
                let rot = Modintx8::load(
                    [rot, rot, rot, rot, next_rot, next_rot, next_rot, next_rot].as_ptr(),
                );
                let rot2 = rot * rot;
                let rot3 = rot * rot2;
                let (r0, r1, r2, r3) = radix4_inner!(
                    Modintx8::gather(a[top..].as_ptr(), vindex),
                    Modintx8::gather(a[top + 4..].as_ptr(), vindex) * rot,
                    Modintx8::gather(a[top + 8..].as_ptr(), vindex) * rot2,
                    Modintx8::gather(a[top + 12..].as_ptr(), vindex) * rot3,
                    imag
                );
                storeu(
                    a[top..].as_mut_ptr() as _,
                    permute2f128::<0x20>(r0.rawval(), r1.rawval()),
                );
                storeu(
                    a[top + 8..].as_mut_ptr() as _,
                    permute2f128::<0x20>(r2.rawval(), r3.rawval()),
                );
                storeu(
                    a[top + 16..].as_mut_ptr() as _,
                    permute2f128::<0x31>(r0.rawval(), r1.rawval()),
                );
                storeu(
                    a[top + 24..].as_mut_ptr() as _,
                    permute2f128::<0x31>(r2.rawval(), r3.rawval()),
                );
            }
            rot = next_rot * rate[(block + 1).trailing_ones() as usize];
        }
    } else if offset < 8 {
        for block in 0..blocks {
            let top = block * width;
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            for now in top..top + offset {
                let (r0, r1, r2, r3) = radix4_inner!(
                    a[now],
                    a[now + offset] * rot,
                    a[now + offset * 2] * rot2,
                    a[now + offset * 3] * rot3,
                    im
                );
                a[now] = r0;
                a[now + offset] = r1;
                a[now + offset * 2] = r2;
                a[now + offset * 3] = r3;
            }
            rot *= rate[block.trailing_ones() as usize];
        }
    } else {
        let mut head = a.as_mut_ptr();
        for _ in (0..offset).step_by(8) {
            let (c0a, c1a, c2a, c3a) = (
                head,
                head.add(offset),
                head.add(offset * 2),
                head.add(offset * 3),
            );
            let (r0, r1, r2, r3) = radix4_inner!(
                Modintx8::load(c0a),
                Modintx8::load(c1a),
                Modintx8::load(c2a),
                Modintx8::load(c3a),
                imag
            );
            r0.store(c0a);
            r1.store(c1a);
            r2.store(c2a);
            r3.store(c3a);
            head = head.add(8);
        }
        let mut rot = Modintx8::splat(rate[0]);
        for block in 1..blocks {
            let top = block * width;
            let rot2 = rot * rot;
            let rot3 = rot * rot2;
            let mut head = a[top..].as_mut_ptr();
            for _ in (top..top + offset).step_by(8) {
                let (c0a, c1a, c2a, c3a) = (
                    head,
                    head.add(offset),
                    head.add(offset * 2),
                    head.add(offset * 3),
                );
                let (r0, r1, r2, r3) = radix4_inner!(
                    Modintx8::load(c0a),
                    Modintx8::load(c1a) * rot,
                    Modintx8::load(c2a) * rot2,
                    Modintx8::load(c3a) * rot3,
                    imag
                );
                r0.store(c0a);
                r1.store(c1a);
                r2.store(c2a);
                r3.store(c3a);
                head = head.add(8);
            }
            rot = rot * Modintx8::splat(*rate.get_unchecked(block.trailing_ones() as usize));
        }
    }
}

/// # Safety
/// The length of `a` must be the power of 2.
#[inline]
#[target_feature(enable = "avx2", enable = "bmi1")]
pub unsafe fn gentleman_sande_radix_4_butterfly<M: Modulo>(
    deg: usize,
    a: &mut [Modint<M>],
    cache: &FftCache<M>,
) {
    let log = deg.trailing_zeros();
    for i in (0..log).step_by(2) {
        let width = deg >> i;
        if i + 1 == log {
            let offset = width >> 1;
            gentleman_sande_radix_2_kernel(deg, width, offset, a, &cache.rate2);
        } else {
            let offset = width >> 2;
            gentleman_sande_radix_4_kernel(deg, width, offset, cache.root[2], a, &cache.rate3);
        }
    }
}

/// # Safety
/// The length of `a` must be the power of 2.
#[inline]
#[target_feature(enable = "avx2", enable = "bmi1")]
pub unsafe fn gentleman_sande_radix_4_butterfly_inv<M: Modulo>(
    deg: usize,
    a: &mut [Modint<M>],
    cache: &FftCache<M>,
) {
    let log = deg.trailing_zeros();
    for i in (0..log).step_by(2) {
        let width = deg >> i;
        if i + 1 == log {
            let offset = width >> 1;
            gentleman_sande_radix_2_kernel(deg, width, offset, a, &cache.irate2);
        } else {
            let offset = width >> 2;
            gentleman_sande_radix_4_kernel(deg, width, offset, cache.iroot[2], a, &cache.irate3);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utility::bit_reverse;
    use montgomery_modint::Mod998244353;

    type Modint = MontgomeryModint<Mod998244353>;

    pub fn ntt_gentleman_sande_radix_4(a: &mut [Modint]) {
        let deg = a.len();
        debug_assert_eq!(deg, 1 << deg.trailing_zeros());
        let cache = FftCache::new();
        unsafe { gentleman_sande_radix_4_butterfly(deg, a, &cache) }
        bit_reverse(deg, a);
    }

    pub fn intt_gentleman_sande_radix_4(a: &mut [Modint]) {
        let deg = a.len();
        debug_assert_eq!(deg, 1 << deg.trailing_zeros());
        let cache = FftCache::new();
        unsafe { gentleman_sande_radix_4_butterfly_inv(deg, a, &cache) }
        bit_reverse(deg, a);
        let inv = Modint::new(deg as u32).inv();
        a.iter_mut().for_each(|c| *c *= inv)
    }

    #[test]
    fn gentleman_sande_radix_4_test() {
        for i in 1..=13 {
            let n = 1 << i;
            let data: Vec<Modint> = (1..=n).map(Modint::new).collect();
            let mut data1 = data.clone();
            ntt_gentleman_sande_radix_4(&mut data1);
            intt_gentleman_sande_radix_4(&mut data1);
            assert_eq!(data, data1);
        }
    }
}
