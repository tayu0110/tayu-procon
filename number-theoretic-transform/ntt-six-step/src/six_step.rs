use std::ptr::copy_nonoverlapping;

use super::cooley_tukey::cooley_tukey_radix_4_butterfly;
use super::fft_cache::FftCache;
use crate::gentleman_sande::gentleman_sande_radix_4_butterfly_inv;
use montgomery_modint::{Modulo, MontgomeryModint};

type Modint<M> = MontgomeryModint<M>;

#[inline]
/// transpose n-rows/2n-columns matrix.
fn transpose_nx2n<M: Modulo>(n: usize, a: &mut [Modint<M>], buf: &mut [Modint<M>]) {
    if n == 1 {
        return;
    }
    assert!(buf.len() >= n);
    assert_eq!(n * n * 2, a.len());

    let (a, b) = a.split_at_mut(n * n);

    transpose(n, a);
    transpose(n, b);

    for (a, b) in a.chunks_exact_mut(n).zip(b.chunks_exact_mut(n)) {
        for j in 0..n / 2 {
            a[j] = a[j * 2];
            buf[j] = a[j * 2 + 1];
        }
        for j in 0..n / 2 {
            a[n / 2 + j] = b[j * 2];
            buf[n / 2 + j] = b[j * 2 + 1];
        }
        unsafe { copy_nonoverlapping(buf.as_ptr(), b.as_mut_ptr(), n) }
    }
}

#[inline]
/// transpose 2n-rows/n-columns matrix.
fn transpose_2nxn<M: Modulo>(n: usize, a: &mut [Modint<M>], buf: &mut [Modint<M>]) {
    if n == 1 {
        return;
    }
    assert!(buf.len() >= n);
    assert_eq!(n * n * 2, a.len());

    let (a, b) = a.split_at_mut(n * n);

    for (a, b) in a.chunks_exact_mut(n).zip(b.chunks_exact_mut(n)) {
        unsafe { copy_nonoverlapping(b.as_ptr(), buf.as_mut_ptr(), n) }
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
// transpose NxN square matrix.
fn transpose<M: Modulo>(n: usize, a: &mut [Modint<M>]) {
    const BLOCK: usize = 8;
    const PANEL: usize = 32;
    for i in (0..n).step_by(PANEL) {
        for j in (i..n).step_by(PANEL) {
            for k in (i..i + PANEL).step_by(BLOCK) {
                for l in (j..j + PANEL).step_by(BLOCK) {
                    for s in k..(k + BLOCK).min(n) {
                        for t in l..(l + BLOCK).min(n) {
                            let p = s * n + t;
                            let q = s + n * t;
                            if p > q {
                                a.swap(s * n + t, s + n * t);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[inline]
pub fn six_step_ntt<M: Modulo>(a: &mut [Modint<M>], cache: &FftCache<M>) {
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
    for (i, v) in a.chunks_exact_mut(columns).enumerate() {
        let mut rot = Modint::one();
        v.iter_mut().for_each(|v| {
            *v *= rot;
            rot *= w;
        });

        if i + 1 != rows {
            w *= rate[i.trailing_ones() as usize];
        }

        cooley_tukey_radix_4_butterfly(columns, clog, v, &cache);
    }
}

#[inline]
pub fn six_step_intt<M: Modulo>(a: &mut [Modint<M>], cache: &FftCache<M>) {
    let n = a.len();
    let log = n.trailing_zeros() as usize;
    assert_eq!(n, 1 << log);

    let clog = (log + 1) / 2;
    let columns = 1 << clog;
    let rlog = log - clog;
    let rows = 1 << rlog;

    let irate = cache.gen_irate((log + 3) / 2);
    let mut w = Modint::one();
    for (i, v) in a.chunks_exact_mut(columns).enumerate() {
        gentleman_sande_radix_4_butterfly_inv(columns, clog, v, &cache);

        let mut irot = Modint::one();
        v.iter_mut().for_each(|v| {
            *v *= irot;
            irot *= w;
        });
        if i + 1 != rows {
            w *= irate[i.trailing_ones() as usize];
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

    let ninv = Modint::raw(n as u32).inv();
    a.iter_mut().for_each(|a| *a *= ninv);
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
        for i in (2..=14).step_by(2) {
            let data = (0..1 << i).map(|v| Modint::raw(v)).collect::<Vec<_>>();
            let mut data1 = data.clone();
            six_step_ntt(&mut data1, &cache);
            six_step_intt(&mut data1, &cache);
            assert_eq!(data, data1);
        }
    }

    #[test]
    fn six_step_cooley_tukey_compare_test() {
        for log in (2..=14).step_by(2) {
            let len = 1 << log;
            let data = (0..len).map(|a| Modint::raw(a as u32)).collect::<Vec<_>>();
            let mut data_s = data.clone();
            let mut data_c = data.clone();
            let cache = FftCache::new();

            six_step_ntt(&mut data_s, &cache);
            cooley_tukey_radix_4_butterfly(len, log, &mut data_c, &cache);

            six_step_intt(&mut data_s, &cache);
            gentleman_sande_radix_4_butterfly_inv(len, log, &mut data_c, &cache);
            data_c.iter_mut().for_each(|v| *v *= Modint::raw(len as u32).inv());

            assert_eq!(data_s, data_c);

            assert_eq!(data, data_s);
        }
    }
}
