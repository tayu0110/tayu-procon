use super::common::*;
use super::FftCache;
use montgomery_modint::{Modulo, MontgomeryModint};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{_mm256_i32gather_epi32, _mm256_loadu_si256, _mm256_set1_epi32, _mm256_setr_epi32, _mm256_storeu_si256};
use std::ptr::copy_nonoverlapping;

type Modint<M> = MontgomeryModint<M>;

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn cooley_tukey_radix_2_kernel<M: Modulo>(deg: usize, width: usize, offset: usize, a: &mut [Modint<M>], rate: &[Modint<M>]) {
    let mut rot = Modint::one();
    let blocks = deg / width;
    if offset == 1 && blocks >= 8 {
        let modulo = _mm256_set1_epi32(M::MOD as i32);
        let modulo_inv = _mm256_set1_epi32(M::MOD_INV as i32);
        let mut r = [Modint::zero(); 8];
        let mut buf = [[Modint::zero(); 8]; 2];
        let vindex = _mm256_setr_epi32(0, 2, 4, 6, 8, 10, 12, 14);
        for block in (0..blocks).step_by(8) {
            let top = block * width;
            for i in 0..8 {
                r[i] = rot;
                if block + i + 1 != blocks {
                    rot *= rate[(!(block + i)).trailing_zeros() as usize];
                }
            }
            let rot = _mm256_loadu_si256(r.as_ptr() as _);
            let c0 = _mm256_i32gather_epi32(a[top..].as_ptr() as _, vindex, 4);
            let c1 = montgomery_multiplication_u32x8(_mm256_i32gather_epi32(a[top + 1..].as_ptr() as _, vindex, 4), rot, modulo, modulo_inv);

            _mm256_storeu_si256(buf[0].as_mut_ptr() as _, _mm256_add_mod_epi32(c0, c1, modulo));
            _mm256_storeu_si256(buf[1].as_mut_ptr() as _, _mm256_sub_mod_epi32(c0, c1, modulo));

            for i in 0..8 {
                a[top + i * 2] = buf[0][i];
                a[top + i * 2 + 1] = buf[1][i];
            }
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
    let imag = _mm256_set1_epi32(im.val as i32);
    let modulo = _mm256_set1_epi32(M::MOD as i32);
    let modulo_inv = _mm256_set1_epi32(M::MOD_INV as i32);

    if offset == 1 && blocks >= 8 {
        let mut r = [Modint::zero(); 8];
        let mut buf = [[Modint::zero(); 8]; 4];
        let vindex = _mm256_setr_epi32(0, 4, 8, 12, 16, 20, 24, 28);
        for block in (0..blocks).step_by(8) {
            let top = block * width;
            for i in 0..8 {
                r[i] = rot;
                if block + i != blocks {
                    rot *= rate[(!(block + i)).trailing_zeros() as usize];
                }
            }
            let rot = _mm256_loadu_si256(r.as_ptr() as _);
            let rot2 = montgomery_multiplication_u32x8(rot, rot, modulo, modulo_inv);
            let rot3 = montgomery_multiplication_u32x8(rot, rot2, modulo, modulo_inv);
            let c0 = _mm256_i32gather_epi32(a[top..].as_ptr() as _, vindex, 4);
            let c1 = _mm256_i32gather_epi32(a[top + 1..].as_ptr() as _, vindex, 4);
            let c2 = _mm256_i32gather_epi32(a[top + 2..].as_ptr() as _, vindex, 4);
            let c3 = _mm256_i32gather_epi32(a[top + 3..].as_ptr() as _, vindex, 4);
            let (c1, c2, c3) = (
                montgomery_multiplication_u32x8(c1, rot, modulo, modulo_inv),
                montgomery_multiplication_u32x8(c2, rot2, modulo, modulo_inv),
                montgomery_multiplication_u32x8(c3, rot3, modulo, modulo_inv),
            );
            let c02 = _mm256_add_mod_epi32(c0, c2, modulo);
            let c02n = _mm256_sub_mod_epi32(c0, c2, modulo);
            let c13 = _mm256_add_mod_epi32(c1, c3, modulo);
            let c13nim = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c1, c3, modulo), imag, modulo, modulo_inv);
            _mm256_storeu_si256(buf[0].as_mut_ptr() as _, _mm256_add_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(buf[1].as_mut_ptr() as _, _mm256_sub_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(buf[2].as_mut_ptr() as _, _mm256_add_mod_epi32(c02n, c13nim, modulo));
            _mm256_storeu_si256(buf[3].as_mut_ptr() as _, _mm256_sub_mod_epi32(c02n, c13nim, modulo));

            for i in 0..4 {
                for j in 0..8 {
                    a[top + i + j * 4] = buf[i][j];
                }
            }
        }
    } else if offset == 2 && blocks >= 4 {
        let mut r = [Modint::zero(); 8];
        let mut buf = [[Modint::zero(); 8]; 4];
        let (b0, b1, b2, b3) = (buf[0].as_mut_ptr(), buf[1].as_mut_ptr(), buf[2].as_mut_ptr(), buf[3].as_mut_ptr());
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
            let rot = _mm256_loadu_si256(r.as_ptr() as _);
            let rot2 = montgomery_multiplication_u32x8(rot, rot, modulo, modulo_inv);
            let rot3 = montgomery_multiplication_u32x8(rot, rot2, modulo, modulo_inv);
            let c0 = _mm256_i32gather_epi32(a[top..].as_ptr() as _, vindex, 4);
            let c1 = _mm256_i32gather_epi32(a[top + 2..].as_ptr() as _, vindex, 4);
            let c2 = _mm256_i32gather_epi32(a[top + 4..].as_ptr() as _, vindex, 4);
            let c3 = _mm256_i32gather_epi32(a[top + 6..].as_ptr() as _, vindex, 4);
            let (c1, c2, c3) = (
                montgomery_multiplication_u32x8(c1, rot, modulo, modulo_inv),
                montgomery_multiplication_u32x8(c2, rot2, modulo, modulo_inv),
                montgomery_multiplication_u32x8(c3, rot3, modulo, modulo_inv),
            );
            let c02 = _mm256_add_mod_epi32(c0, c2, modulo);
            let c02n = _mm256_sub_mod_epi32(c0, c2, modulo);
            let c13 = _mm256_add_mod_epi32(c1, c3, modulo);
            let c13nim = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c1, c3, modulo), imag, modulo, modulo_inv);
            _mm256_storeu_si256(b0 as _, _mm256_add_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(b1 as _, _mm256_sub_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(b2 as _, _mm256_add_mod_epi32(c02n, c13nim, modulo));
            _mm256_storeu_si256(b3 as _, _mm256_sub_mod_epi32(c02n, c13nim, modulo));

            for j in 0..4 {
                copy_nonoverlapping(b0.add(j * 2), a[top + j * 8..top + j * 8 + 2].as_mut_ptr(), 2);
                copy_nonoverlapping(b1.add(j * 2), a[top + 2 + j * 8..top + 2 + j * 8 + 2].as_mut_ptr(), 2);
                copy_nonoverlapping(b2.add(j * 2), a[top + 4 + j * 8..top + 4 + j * 8 + 2].as_mut_ptr(), 2);
                copy_nonoverlapping(b3.add(j * 2), a[top + 6 + j * 8..top + 6 + j * 8 + 2].as_mut_ptr(), 2);
            }
        }
    } else if offset == 4 && blocks >= 2 {
        let mut r = [Modint::zero(); 8];
        let mut buf = [[Modint::zero(); 8]; 4];
        let (b0, b1, b2, b3) = (buf[0].as_mut_ptr(), buf[1].as_mut_ptr(), buf[2].as_mut_ptr(), buf[3].as_mut_ptr());
        let vindex = _mm256_setr_epi32(0, 1, 2, 3, 16, 17, 18, 19);
        for block in (0..blocks).step_by(2) {
            let top = block * width;
            for i in 0..2 {
                r[i * 4..i * 4 + 4].copy_from_slice(&[rot, rot, rot, rot]);
                if block + i + 1 != blocks {
                    rot *= rate[(!(block + i)).trailing_zeros() as usize];
                }
            }
            let rot = _mm256_loadu_si256(r.as_ptr() as _);
            let rot2 = montgomery_multiplication_u32x8(rot, rot, modulo, modulo_inv);
            let rot3 = montgomery_multiplication_u32x8(rot, rot2, modulo, modulo_inv);
            let c0 = _mm256_i32gather_epi32(a[top..].as_ptr() as _, vindex, 4);
            let c1 = _mm256_i32gather_epi32(a[top + 4..].as_ptr() as _, vindex, 4);
            let c2 = _mm256_i32gather_epi32(a[top + 8..].as_ptr() as _, vindex, 4);
            let c3 = _mm256_i32gather_epi32(a[top + 12..].as_ptr() as _, vindex, 4);
            let (c1, c2, c3) = (
                montgomery_multiplication_u32x8(c1, rot, modulo, modulo_inv),
                montgomery_multiplication_u32x8(c2, rot2, modulo, modulo_inv),
                montgomery_multiplication_u32x8(c3, rot3, modulo, modulo_inv),
            );
            let c02 = _mm256_add_mod_epi32(c0, c2, modulo);
            let c02n = _mm256_sub_mod_epi32(c0, c2, modulo);
            let c13 = _mm256_add_mod_epi32(c1, c3, modulo);
            let c13nim = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c1, c3, modulo), imag, modulo, modulo_inv);
            _mm256_storeu_si256(b0 as _, _mm256_add_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(b1 as _, _mm256_sub_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(b2 as _, _mm256_add_mod_epi32(c02n, c13nim, modulo));
            _mm256_storeu_si256(b3 as _, _mm256_sub_mod_epi32(c02n, c13nim, modulo));

            for j in 0..2 {
                copy_nonoverlapping(b0.add(j * 4), a[top + j * 16..top + j * 16 + 4].as_mut_ptr(), 4);
                copy_nonoverlapping(b1.add(j * 4), a[top + 4 + j * 16..top + 4 + j * 16 + 4].as_mut_ptr(), 4);
                copy_nonoverlapping(b2.add(j * 4), a[top + 8 + j * 16..top + 8 + j * 16 + 4].as_mut_ptr(), 4);
                copy_nonoverlapping(b3.add(j * 4), a[top + 12 + j * 16..top + 12 + j * 16 + 4].as_mut_ptr(), 4);
            }
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
        for now in (0..offset).step_by(8) {
            let c0 = _mm256_loadu_si256(a[now..now + 8].as_ptr() as _);
            let c1 = _mm256_loadu_si256(a[now + offset..now + offset + 8].as_ptr() as _);
            let c2 = _mm256_loadu_si256(a[now + offset * 2..now + offset * 2 + 8].as_ptr() as _);
            let c3 = _mm256_loadu_si256(a[now + offset * 3..now + offset * 3 + 8].as_ptr() as _);
            let c02 = _mm256_add_mod_epi32(c0, c2, modulo);
            let c02n = _mm256_sub_mod_epi32(c0, c2, modulo);
            let c13 = _mm256_add_mod_epi32(c1, c3, modulo);
            let c13nim = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c1, c3, modulo), imag, modulo, modulo_inv);
            _mm256_storeu_si256(a[now..now + 8].as_mut_ptr() as _, _mm256_add_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(a[now + offset..now + offset + 8].as_mut_ptr() as _, _mm256_sub_mod_epi32(c02, c13, modulo));
            _mm256_storeu_si256(a[now + offset * 2..now + offset * 2 + 8].as_mut_ptr() as _, _mm256_add_mod_epi32(c02n, c13nim, modulo));
            _mm256_storeu_si256(a[now + offset * 3..now + offset * 3 + 8].as_mut_ptr() as _, _mm256_sub_mod_epi32(c02n, c13nim, modulo));
        }
        let mut rot = _mm256_set1_epi32(rate[0].val as i32);
        for block in 1..blocks {
            let top = block * width;
            let rot2 = montgomery_multiplication_u32x8(rot, rot, modulo, modulo_inv);
            let rot3 = montgomery_multiplication_u32x8(rot, rot2, modulo, modulo_inv);
            let mut head = a[top..].as_mut_ptr();
            for _ in (top..top + offset).step_by(8) {
                let (c0a, c1a, c2a, c3a) = (head, head.add(offset), head.add(offset * 2), head.add(offset * 3));
                let c0 = _mm256_loadu_si256(c0a as _);
                let c1 = montgomery_multiplication_u32x8(_mm256_loadu_si256(c1a as _), rot, modulo, modulo_inv);
                let c2 = montgomery_multiplication_u32x8(_mm256_loadu_si256(c2a as _), rot2, modulo, modulo_inv);
                let c3 = montgomery_multiplication_u32x8(_mm256_loadu_si256(c3a as _), rot3, modulo, modulo_inv);
                let c02 = _mm256_add_mod_epi32(c0, c2, modulo);
                let c02n = _mm256_sub_mod_epi32(c0, c2, modulo);
                let c13 = _mm256_add_mod_epi32(c1, c3, modulo);
                let c13nim = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c1, c3, modulo), imag, modulo, modulo_inv);
                _mm256_storeu_si256(c0a as _, _mm256_add_mod_epi32(c02, c13, modulo));
                _mm256_storeu_si256(c1a as _, _mm256_sub_mod_epi32(c02, c13, modulo));
                _mm256_storeu_si256(c2a as _, _mm256_add_mod_epi32(c02n, c13nim, modulo));
                _mm256_storeu_si256(c3a as _, _mm256_sub_mod_epi32(c02n, c13nim, modulo));
                head = head.add(8);
            }
            if top + width != deg {
                rot = montgomery_multiplication_u32x8(rot, _mm256_set1_epi32(rate[(!block).trailing_zeros() as usize].val as i32), modulo, modulo_inv);
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
