use super::cooley_tukey::cooley_tukey_radix_4_butterfly;
use super::fft_cache::FftCache;
use super::gentleman_sande::gentleman_sande_radix_4_butterfly_inv;
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use std::{
    arch::x86_64::{__m256i, _mm256_loadu_si256, _mm256_permute2f128_si256, _mm256_storeu_si256, _mm256_unpackhi_epi32, _mm256_unpackhi_epi64, _mm256_unpacklo_epi32, _mm256_unpacklo_epi64},
    ptr::copy_nonoverlapping,
};

type Modint<M> = MontgomeryModint<M>;

#[inline]
#[target_feature(enable = "avx2")]
/// transpose n-rows/2n-columns matrix.
unsafe fn transpose_nx2n<M: Modulo>(n: usize, a: &mut [Modint<M>], buf: &mut [Modint<M>]) {
    if n == 1 {
        return;
    }
    assert!(buf.len() >= n);
    assert_eq!(n * n * 2, a.len());

    let (a, b) = a.split_at_mut(n * n);

    transpose(n, a);
    transpose(n, b);

    for (a, b) in a.chunks_exact_mut(n).zip(b.chunks_exact_mut(n)) {
        for j in 0..n >> 1 {
            a[j] = a[j * 2];
            buf[j] = a[j * 2 + 1];
        }
        for j in 0..n >> 1 {
            a[n / 2 + j] = b[j * 2];
            buf[n / 2 + j] = b[j * 2 + 1];
        }
        copy_nonoverlapping(buf.as_ptr(), b.as_mut_ptr(), n);
    }
}

#[inline]
#[target_feature(enable = "avx2")]
/// transpose 2n-rows/n-columns matrix.
unsafe fn transpose_2nxn<M: Modulo>(n: usize, a: &mut [Modint<M>], buf: &mut [Modint<M>]) {
    if n == 1 {
        return;
    }
    assert!(buf.len() >= n);
    assert_eq!(n * n * 2, a.len());

    let (a, b) = a.split_at_mut(n * n);

    for (a, b) in a.chunks_exact_mut(n).zip(b.chunks_exact_mut(n)) {
        copy_nonoverlapping(b.as_ptr(), buf.as_mut_ptr(), n);
        for j in (0..n / 2).rev() {
            b[j * 2] = a[n / 2 + j];
            b[j * 2 + 1] = buf[n / 2 + j];
        }
        for j in (0..n / 2).rev() {
            a[j * 2] = a[j];
            a[j * 2 + 1] = buf[j];
        }
    }

    transpose(n, a);
    transpose(n, b);
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn transpose8x8u32(
    m0: __m256i,
    m1: __m256i,
    m2: __m256i,
    m3: __m256i,
    m4: __m256i,
    m5: __m256i,
    m6: __m256i,
    m7: __m256i,
) -> (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i) {
    let a0 = _mm256_unpacklo_epi32(m0, m1);
    let a1 = _mm256_unpackhi_epi32(m0, m1);
    let a2 = _mm256_unpacklo_epi32(m2, m3);
    let a3 = _mm256_unpackhi_epi32(m2, m3);
    let a4 = _mm256_unpacklo_epi32(m4, m5);
    let a5 = _mm256_unpackhi_epi32(m4, m5);
    let a6 = _mm256_unpacklo_epi32(m6, m7);
    let a7 = _mm256_unpackhi_epi32(m6, m7);

    let m0 = _mm256_unpacklo_epi64(a0, a2);
    let m1 = _mm256_unpackhi_epi64(a0, a2);
    let m2 = _mm256_unpacklo_epi64(a1, a3);
    let m3 = _mm256_unpackhi_epi64(a1, a3);
    let m4 = _mm256_unpacklo_epi64(a4, a6);
    let m5 = _mm256_unpackhi_epi64(a4, a6);
    let m6 = _mm256_unpacklo_epi64(a5, a7);
    let m7 = _mm256_unpackhi_epi64(a5, a7);

    (
        _mm256_permute2f128_si256(m0, m4, 0x20),
        _mm256_permute2f128_si256(m1, m5, 0x20),
        _mm256_permute2f128_si256(m2, m6, 0x20),
        _mm256_permute2f128_si256(m3, m7, 0x20),
        _mm256_permute2f128_si256(m0, m4, 0x31),
        _mm256_permute2f128_si256(m1, m5, 0x31),
        _mm256_permute2f128_si256(m2, m6, 0x31),
        _mm256_permute2f128_si256(m3, m7, 0x31),
    )
}

#[inline]
#[target_feature(enable = "avx2")]
// transpose NxN square matrix.
unsafe fn transpose<M: Modulo>(n: usize, a: &mut [Modint<M>]) {
    const BLOCK: usize = 8;
    const PANEL: usize = 32;
    if n < PANEL {
        for i in 0..n {
            for j in i + 1..n {
                a.swap(i * n + j, i + n * j);
            }
        }
    } else {
        for i in (0..n).step_by(PANEL) {
            for k in (i..i + PANEL).step_by(BLOCK) {
                let m0 = _mm256_loadu_si256(a[(k + 0) * n + k..].as_ptr() as _);
                let m1 = _mm256_loadu_si256(a[(k + 1) * n + k..].as_ptr() as _);
                let m2 = _mm256_loadu_si256(a[(k + 2) * n + k..].as_ptr() as _);
                let m3 = _mm256_loadu_si256(a[(k + 3) * n + k..].as_ptr() as _);
                let m4 = _mm256_loadu_si256(a[(k + 4) * n + k..].as_ptr() as _);
                let m5 = _mm256_loadu_si256(a[(k + 5) * n + k..].as_ptr() as _);
                let m6 = _mm256_loadu_si256(a[(k + 6) * n + k..].as_ptr() as _);
                let m7 = _mm256_loadu_si256(a[(k + 7) * n + k..].as_ptr() as _);
                let (m0, m1, m2, m3, m4, m5, m6, m7) = transpose8x8u32(m0, m1, m2, m3, m4, m5, m6, m7);
                _mm256_storeu_si256(a[(k + 0) * n + k..].as_mut_ptr() as _, m0);
                _mm256_storeu_si256(a[(k + 1) * n + k..].as_mut_ptr() as _, m1);
                _mm256_storeu_si256(a[(k + 2) * n + k..].as_mut_ptr() as _, m2);
                _mm256_storeu_si256(a[(k + 3) * n + k..].as_mut_ptr() as _, m3);
                _mm256_storeu_si256(a[(k + 4) * n + k..].as_mut_ptr() as _, m4);
                _mm256_storeu_si256(a[(k + 5) * n + k..].as_mut_ptr() as _, m5);
                _mm256_storeu_si256(a[(k + 6) * n + k..].as_mut_ptr() as _, m6);
                _mm256_storeu_si256(a[(k + 7) * n + k..].as_mut_ptr() as _, m7);
                for l in (k + BLOCK..i + PANEL).step_by(BLOCK) {
                    let m0 = _mm256_loadu_si256(a[(k + 0) * n + l..].as_ptr() as _);
                    let m1 = _mm256_loadu_si256(a[(k + 1) * n + l..].as_ptr() as _);
                    let m2 = _mm256_loadu_si256(a[(k + 2) * n + l..].as_ptr() as _);
                    let m3 = _mm256_loadu_si256(a[(k + 3) * n + l..].as_ptr() as _);
                    let m4 = _mm256_loadu_si256(a[(k + 4) * n + l..].as_ptr() as _);
                    let m5 = _mm256_loadu_si256(a[(k + 5) * n + l..].as_ptr() as _);
                    let m6 = _mm256_loadu_si256(a[(k + 6) * n + l..].as_ptr() as _);
                    let m7 = _mm256_loadu_si256(a[(k + 7) * n + l..].as_ptr() as _);
                    let (m0, m1, m2, m3, m4, m5, m6, m7) = transpose8x8u32(m0, m1, m2, m3, m4, m5, m6, m7);
                    let n0 = _mm256_loadu_si256(a[(l + 0) * n + k..].as_ptr() as _);
                    let n1 = _mm256_loadu_si256(a[(l + 1) * n + k..].as_ptr() as _);
                    let n2 = _mm256_loadu_si256(a[(l + 2) * n + k..].as_ptr() as _);
                    let n3 = _mm256_loadu_si256(a[(l + 3) * n + k..].as_ptr() as _);
                    let n4 = _mm256_loadu_si256(a[(l + 4) * n + k..].as_ptr() as _);
                    let n5 = _mm256_loadu_si256(a[(l + 5) * n + k..].as_ptr() as _);
                    let n6 = _mm256_loadu_si256(a[(l + 6) * n + k..].as_ptr() as _);
                    let n7 = _mm256_loadu_si256(a[(l + 7) * n + k..].as_ptr() as _);
                    _mm256_storeu_si256(a[(l + 0) * n + k..].as_ptr() as _, m0);
                    _mm256_storeu_si256(a[(l + 1) * n + k..].as_ptr() as _, m1);
                    _mm256_storeu_si256(a[(l + 2) * n + k..].as_ptr() as _, m2);
                    _mm256_storeu_si256(a[(l + 3) * n + k..].as_ptr() as _, m3);
                    _mm256_storeu_si256(a[(l + 4) * n + k..].as_ptr() as _, m4);
                    _mm256_storeu_si256(a[(l + 5) * n + k..].as_ptr() as _, m5);
                    _mm256_storeu_si256(a[(l + 6) * n + k..].as_ptr() as _, m6);
                    _mm256_storeu_si256(a[(l + 7) * n + k..].as_ptr() as _, m7);
                    let (n0, n1, n2, n3, n4, n5, n6, n7) = transpose8x8u32(n0, n1, n2, n3, n4, n5, n6, n7);
                    _mm256_storeu_si256(a[(k + 0) * n + l..].as_ptr() as _, n0);
                    _mm256_storeu_si256(a[(k + 1) * n + l..].as_ptr() as _, n1);
                    _mm256_storeu_si256(a[(k + 2) * n + l..].as_ptr() as _, n2);
                    _mm256_storeu_si256(a[(k + 3) * n + l..].as_ptr() as _, n3);
                    _mm256_storeu_si256(a[(k + 4) * n + l..].as_ptr() as _, n4);
                    _mm256_storeu_si256(a[(k + 5) * n + l..].as_ptr() as _, n5);
                    _mm256_storeu_si256(a[(k + 6) * n + l..].as_ptr() as _, n6);
                    _mm256_storeu_si256(a[(k + 7) * n + l..].as_ptr() as _, n7);
                }
            }
            for j in (i + PANEL..n).step_by(PANEL) {
                for k in (i..i + PANEL).step_by(BLOCK) {
                    for l in (j..j + PANEL).step_by(BLOCK) {
                        let m0 = _mm256_loadu_si256(a[(k + 0) * n + l..].as_ptr() as _);
                        let m1 = _mm256_loadu_si256(a[(k + 1) * n + l..].as_ptr() as _);
                        let m2 = _mm256_loadu_si256(a[(k + 2) * n + l..].as_ptr() as _);
                        let m3 = _mm256_loadu_si256(a[(k + 3) * n + l..].as_ptr() as _);
                        let m4 = _mm256_loadu_si256(a[(k + 4) * n + l..].as_ptr() as _);
                        let m5 = _mm256_loadu_si256(a[(k + 5) * n + l..].as_ptr() as _);
                        let m6 = _mm256_loadu_si256(a[(k + 6) * n + l..].as_ptr() as _);
                        let m7 = _mm256_loadu_si256(a[(k + 7) * n + l..].as_ptr() as _);
                        let (m0, m1, m2, m3, m4, m5, m6, m7) = transpose8x8u32(m0, m1, m2, m3, m4, m5, m6, m7);
                        let n0 = _mm256_loadu_si256(a[(l + 0) * n + k..].as_ptr() as _);
                        let n1 = _mm256_loadu_si256(a[(l + 1) * n + k..].as_ptr() as _);
                        let n2 = _mm256_loadu_si256(a[(l + 2) * n + k..].as_ptr() as _);
                        let n3 = _mm256_loadu_si256(a[(l + 3) * n + k..].as_ptr() as _);
                        let n4 = _mm256_loadu_si256(a[(l + 4) * n + k..].as_ptr() as _);
                        let n5 = _mm256_loadu_si256(a[(l + 5) * n + k..].as_ptr() as _);
                        let n6 = _mm256_loadu_si256(a[(l + 6) * n + k..].as_ptr() as _);
                        let n7 = _mm256_loadu_si256(a[(l + 7) * n + k..].as_ptr() as _);
                        _mm256_storeu_si256(a[(l + 0) * n + k..].as_ptr() as _, m0);
                        _mm256_storeu_si256(a[(l + 1) * n + k..].as_ptr() as _, m1);
                        _mm256_storeu_si256(a[(l + 2) * n + k..].as_ptr() as _, m2);
                        _mm256_storeu_si256(a[(l + 3) * n + k..].as_ptr() as _, m3);
                        _mm256_storeu_si256(a[(l + 4) * n + k..].as_ptr() as _, m4);
                        _mm256_storeu_si256(a[(l + 5) * n + k..].as_ptr() as _, m5);
                        _mm256_storeu_si256(a[(l + 6) * n + k..].as_ptr() as _, m6);
                        _mm256_storeu_si256(a[(l + 7) * n + k..].as_ptr() as _, m7);
                        let (n0, n1, n2, n3, n4, n5, n6, n7) = transpose8x8u32(n0, n1, n2, n3, n4, n5, n6, n7);
                        _mm256_storeu_si256(a[(k + 0) * n + l..].as_ptr() as _, n0);
                        _mm256_storeu_si256(a[(k + 1) * n + l..].as_ptr() as _, n1);
                        _mm256_storeu_si256(a[(k + 2) * n + l..].as_ptr() as _, n2);
                        _mm256_storeu_si256(a[(k + 3) * n + l..].as_ptr() as _, n3);
                        _mm256_storeu_si256(a[(k + 4) * n + l..].as_ptr() as _, n4);
                        _mm256_storeu_si256(a[(k + 5) * n + l..].as_ptr() as _, n5);
                        _mm256_storeu_si256(a[(k + 6) * n + l..].as_ptr() as _, n6);
                        _mm256_storeu_si256(a[(k + 7) * n + l..].as_ptr() as _, n7);
                    }
                }
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn six_step_ntt<M: Modulo>(a: &mut [Modint<M>], cache: &FftCache<M>) {
    let n = a.len();
    let log = n.trailing_zeros() as usize;
    assert_eq!(n, 1 << log);

    let clog = (log + 1) / 2;
    let columns = 1 << clog;
    let rlog = log - clog;
    let rows = 1 << rlog;
    if rows == columns {
        transpose(columns, a);

        for a in a.chunks_exact_mut(rows) {
            cooley_tukey_radix_4_butterfly(rows, rlog, a, &cache);
        }

        transpose(columns, a);
    } else {
        let mut buf = vec![Modint::zero(); rows];
        transpose_nx2n(rows, a, &mut buf);

        for a in a.chunks_exact_mut(rows) {
            cooley_tukey_radix_4_butterfly(rows, rlog, a, &cache);
        }

        transpose_2nxn(rows, a, &mut buf);
    }

    let rate = cache.gen_rate((log + 3) / 2);
    let mut w = Modint::one();
    if rows < 8 {
        for (i, v) in a.chunks_exact_mut(columns).enumerate() {
            let mut rot = Modint::one();
            v.iter_mut().for_each(|v| {
                *v *= rot;
                rot *= w;
            });
            if i + 1 != rows {
                w *= rate[(!i).trailing_zeros() as usize];
            }

            cooley_tukey_radix_4_butterfly(columns, clog, v, &cache)
        }
    } else {
        let mut buf = [Modint::one(); 8];
        for (i, v) in a.chunks_exact_mut(columns).enumerate() {
            if w != Modint::one() {
                for j in 1..8 {
                    buf[j] = buf[j - 1] * w;
                }
                let mut rot = MontgomeryModintx8::load_ptr(buf.as_ptr());
                let wx8 = MontgomeryModintx8::splat_raw((buf[7] * w).val);
                v.chunks_exact_mut(8).for_each(|v| {
                    (MontgomeryModintx8::load_ptr(v.as_ptr()) * rot).store_ptr(v.as_mut_ptr());
                    rot = rot * wx8;
                });
            }

            if i + 1 != rows {
                w *= rate[(!i).trailing_zeros() as usize];
            }

            cooley_tukey_radix_4_butterfly(columns, clog, v, &cache)
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn six_step_intt<M: Modulo>(a: &mut [Modint<M>], cache: &FftCache<M>) {
    let n = a.len();
    let log = n.trailing_zeros() as usize;
    assert_eq!(n, 1 << log);

    let clog = (log + 1) / 2;
    let columns = 1 << clog;
    let rlog = log - clog;
    let rows = 1 << rlog;

    let irate = cache.gen_irate((log + 3) / 2);
    let mut w = Modint::one();
    if rows < 8 {
        for (i, v) in a.chunks_exact_mut(columns).enumerate() {
            gentleman_sande_radix_4_butterfly_inv(columns, clog, v, &cache);

            let mut irot = Modint::one();
            v.iter_mut().for_each(|v| {
                *v *= irot;
                irot *= w;
            });
            if i + 1 != rows {
                w *= irate[(!i).trailing_zeros() as usize];
            }
        }
    } else {
        let mut buf = [Modint::one(); 8];
        for (i, v) in a.chunks_exact_mut(columns).enumerate() {
            gentleman_sande_radix_4_butterfly_inv(columns, clog, v, &cache);

            if w == Modint::one() {
                w = irate[(!i).trailing_zeros() as usize];
                continue;
            }
            for j in 1..8 {
                buf[j] = buf[j - 1] * w;
            }
            let mut irot = MontgomeryModintx8::load_ptr(buf.as_ptr());
            let wx8 = MontgomeryModintx8::splat_raw((buf[7] * w).val);
            v.chunks_exact_mut(8).for_each(|v| {
                (MontgomeryModintx8::load_ptr(v.as_ptr()) * irot).store_ptr(v.as_mut_ptr());
                irot = irot * wx8;
            });

            if i + 1 != rows {
                w *= irate[(!i).trailing_zeros() as usize];
            }
        }
    }

    if rows == columns {
        transpose(columns, a);

        for a in a.chunks_exact_mut(rows) {
            gentleman_sande_radix_4_butterfly_inv(rows, rlog, a, &cache);
        }

        transpose(columns, a);
    } else {
        let mut buf = vec![Modint::zero(); rows];
        transpose_nx2n(rows, a, &mut buf);

        for a in a.chunks_exact_mut(rows) {
            gentleman_sande_radix_4_butterfly_inv(rows, rlog, a, &cache);
        }

        transpose_2nxn(rows, a, &mut buf);
    }

    unsafe {
        let ninv = Modint::raw(n as u32).inv();
        if n < 8 {
            a.iter_mut().for_each(|a| *a *= ninv);
        } else {
            let ninv = MontgomeryModintx8::splat_raw(ninv.val);
            a.chunks_exact_mut(8).for_each(|v| (MontgomeryModintx8::load_ptr(v.as_ptr()) * ninv).store_ptr(v.as_mut_ptr()));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::gentleman_sande::gentleman_sande_radix_4_butterfly_inv;
    use super::cooley_tukey_radix_4_butterfly;
    use super::*;
    use montgomery_modint::{Mod998244353, MontgomeryModint};

    type Modint = MontgomeryModint<Mod998244353>;

    #[test]
    fn six_step_ntt_test() {
        let cache = FftCache::new();
        for i in 1..=14 {
            let data = (1..=1 << i).map(|v| Modint::raw(v)).collect::<Vec<_>>();
            let mut data1 = data.clone();
            unsafe {
                six_step_ntt(&mut data1, &cache);
                six_step_intt(&mut data1, &cache);
            }
            let data = data.into_iter().map(|v| v.val).collect::<Vec<_>>();
            let data1 = data1.into_iter().map(|v| v.val).collect::<Vec<_>>();
            assert_eq!(data, data1);
        }
    }

    use test::Bencher;
    #[bench]
    fn six_step_ntt_bench(b: &mut Bencher) {
        let cache = FftCache::new();
        b.iter(|| {
            for i in 15..=20 {
                let mut data = (0..1 << i).map(|v| Modint::raw(v)).collect::<Vec<_>>();
                unsafe {
                    six_step_ntt(&mut data, &cache);
                    six_step_intt(&mut data, &cache);
                }
            }
        })
    }

    #[test]
    fn six_step_cooley_tukey_compare_test() {
        for log in (2..=14).step_by(2) {
            let len = 1 << log;
            let data = (1..=len).map(|a| Modint::raw(a as u32)).collect::<Vec<_>>();
            let mut data_s = data.clone();
            let mut data_c = data.clone();
            let cache = FftCache::new();

            unsafe {
                six_step_ntt(&mut data_s, &cache);
                cooley_tukey_radix_4_butterfly(len, log, &mut data_c, &cache);

                six_step_intt(&mut data_s, &cache);
                gentleman_sande_radix_4_butterfly_inv(len, log, &mut data_c, &cache);
            }
            data_c.iter_mut().for_each(|v| *v *= Modint::raw(len as u32).inv());

            assert_eq!(data_s, data_c);

            assert_eq!(data, data_s);
        }
    }

    #[test]
    fn transpose_square_test() {
        for i in (2..14).step_by(2) {
            let mut mat = (0..1 << i).map(|i| Modint::raw(i)).collect::<Vec<_>>();
            let expect = mat.clone();
            unsafe { transpose(1 << (i / 2), &mut mat) }
            unsafe { transpose(1 << (i / 2), &mut mat) }
            assert_eq!(mat, expect);
        }
    }
}
