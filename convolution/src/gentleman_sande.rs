use super::common::{radix_4_inner_montgomery_modint, radix_4_inv_inner_montgomery_modint, radix_8_inner_montgomery_modint, radix_8_inv_inner_montgomery_modint};
use super::fft_cache::FftCache;
use std::ops::{Add, AddAssign, Mul, Sub};

type Radix4Inner<T> = fn(T, T, T, T, &FftCache<T>) -> (T, T, T, T);
type Radix8Inner<T> = fn(T, T, T, T, T, T, T, T, &FftCache<T>) -> (T, T, T, T, T, T, T, T);

#[inline]
fn radix_2_kernel<M: Sub<M, Output = M> + AddAssign + Copy>(width: usize, a: &mut [M]) {
    let offset = width >> 1;
    // Since it is only called when the degree is halfway, offset is always 1.
    assert_eq!(offset, 1);
    a.chunks_exact_mut(2).for_each(|chunks| {
        let c1 = chunks[1];
        chunks[1] = chunks[0] - c1;
        chunks[0] += c1;
    });
}

#[inline]
fn radix_4_kernel<M: Add<M, Output = M> + Mul<M, Output = M> + Copy>(deg: usize, width: usize, a: &mut [M], cache: &FftCache<M>, twiddle: &[M], radix4_inner: Radix4Inner<M>) {
    let log = width.trailing_zeros();
    let offset = width >> 2;
    // This function is only called in the last adjustment when deg % 3 == 2 or deg % 3 == 1 and deg >= 4, so the offset is always 1 or 4.
    assert!(offset == 1 || offset == 4);
    if offset == 1 {
        a.chunks_exact_mut(4).for_each(|chunk| {
            let (c0, c1, c2, c3) = radix4_inner(chunk[0], chunk[1], chunk[2], chunk[3], cache);
            chunk.copy_from_slice(&[c0, c2, c1, c3]);
        });
    } else {
        assert_eq!(log, 4);
        let exp = deg >> log;
        let (w1, w2, w3, w4, w6, w9) = (twiddle[exp], twiddle[exp * 2], twiddle[exp * 3], twiddle[exp * 4], twiddle[exp * 6], twiddle[exp * 9]);
        for chunk in a.chunks_exact_mut(16) {
            let (c0, c4, c8, c12) = radix4_inner(chunk[0], chunk[4], chunk[8], chunk[12], cache);
            let (c1, c5, c9, c13) = radix4_inner(chunk[1], chunk[5], chunk[9], chunk[13], cache);
            let (c2, c6, c10, c14) = radix4_inner(chunk[2], chunk[6], chunk[10], chunk[14], cache);
            let (c3, c7, c11, c15) = radix4_inner(chunk[3], chunk[7], chunk[11], chunk[15], cache);
            chunk.copy_from_slice(&[c0, c1, c2, c3, c8, c9 * w2, c10 * w4, c11 * w6, c4, c5 * w1, c6 * w2, c7 * w3, c12, c13 * w3, c14 * w6, c15 * w9]);
        }
    }
}

#[inline]
fn radix_8_kernel<M: Mul<M, Output = M> + Copy>(deg: usize, width: usize, a: &mut [M], cache: &FftCache<M>, twiddle: &[M], radix8_inner: Radix8Inner<M>) {
    let log = width.trailing_zeros();
    let offset = width >> 3;
    let exp = deg >> log;
    let exp = [0, exp, exp * 2, exp * 3, exp * 4, exp * 5, exp * 6, exp * 7];
    if offset == 1 {
        a.chunks_exact_mut(8).for_each(|chunk| {
            let (c0, c1, c2, c3, c4, c5, c6, c7) = radix8_inner(chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7], cache);
            chunk.copy_from_slice(&[c0, c4, c2, c6, c1, c5, c3, c7]);
        });
    } else {
        for top in (0..deg).step_by(width) {
            let (c0, c1, c2, c3, c4, c5, c6, c7) = radix8_inner(
                a[top],
                a[top + offset],
                a[top + offset * 2],
                a[top + offset * 3],
                a[top + offset * 4],
                a[top + offset * 5],
                a[top + offset * 6],
                a[top + offset * 7],
                cache,
            );
            a[top] = c0;
            a[top + offset * 4] = c1;
            a[top + offset * 2] = c2;
            a[top + offset * 6] = c3;
            a[top + offset] = c4;
            a[top + offset * 5] = c5;
            a[top + offset * 3] = c6;
            a[top + offset * 7] = c7;
            for base in top + 1..top + offset {
                let (c0, c1, c2, c3, c4, c5, c6, c7) = (
                    a[base],
                    a[base + offset],
                    a[base + offset * 2],
                    a[base + offset * 3],
                    a[base + offset * 4],
                    a[base + offset * 5],
                    a[base + offset * 6],
                    a[base + offset * 7],
                );

                let (c0, c1, c2, c3, c4, c5, c6, c7) = radix8_inner(c0, c1, c2, c3, c4, c5, c6, c7, cache);

                let w1 = twiddle[exp[1] * (base - top)];
                let w2 = twiddle[exp[2] * (base - top)];
                let w3 = twiddle[exp[3] * (base - top)];
                let w4 = twiddle[exp[4] * (base - top)];
                let w5 = twiddle[exp[5] * (base - top)];
                let w6 = twiddle[exp[6] * (base - top)];
                let w7 = twiddle[exp[7] * (base - top)];

                a[base] = c0;
                a[base + offset * 4] = c1 * w1;
                a[base + offset * 2] = c2 * w2;
                a[base + offset * 6] = c3 * w3;
                a[base + offset] = c4 * w4;
                a[base + offset * 5] = c5 * w5;
                a[base + offset * 3] = c6 * w6;
                a[base + offset * 7] = c7 * w7;
            }
        }
    }
}

#[inline]
pub fn gentleman_sande_radix_8_butterfly_montgomery_modint<M: Add<M, Output = M> + Sub<M, Output = M> + Mul<M, Output = M> + AddAssign + Copy>(
    deg: usize,
    log: usize,
    a: &mut [M],
    cache: &FftCache<M>,
) {
    let twiddle = cache.twiddle_factors();
    for i in (0..log).step_by(3) {
        let width = deg >> i;
        if i + 1 == log {
            radix_2_kernel(width, a);
        } else if i + 2 == log {
            radix_4_kernel(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
        } else if i + 4 == log {
            radix_4_kernel(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
            let width = deg >> (i + 2);
            radix_4_kernel(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
            break;
        } else {
            radix_8_kernel(deg, width, a, cache, twiddle, radix_8_inner_montgomery_modint);
        }
    }
}

#[inline]
pub fn gentleman_sande_radix_8_butterfly_inv_montgomery_modint<M: Add<M, Output = M> + Sub<M, Output = M> + Mul<M, Output = M> + AddAssign + Copy>(
    deg: usize,
    log: usize,
    a: &mut [M],
    cache: &FftCache<M>,
) {
    let twiddle_factors = cache.twiddle_factors_inv();
    for i in (0..log).step_by(3) {
        let width = deg >> i;
        if i + 1 == log {
            radix_2_kernel(width, a);
        } else if i + 2 == log {
            radix_4_kernel(deg, width, a, cache, twiddle_factors, radix_4_inv_inner_montgomery_modint);
        } else if i + 4 == log {
            radix_4_kernel(deg, width, a, cache, twiddle_factors, radix_4_inv_inner_montgomery_modint);
            let width = deg >> (i + 2);
            radix_4_kernel(deg, width, a, cache, twiddle_factors, radix_4_inv_inner_montgomery_modint);
            break;
        } else {
            radix_8_kernel(deg, width, a, cache, twiddle_factors, radix_8_inv_inner_montgomery_modint)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::common::bit_reverse;
    use super::super::FftCache;
    use super::{gentleman_sande_radix_8_butterfly_inv_montgomery_modint, gentleman_sande_radix_8_butterfly_montgomery_modint};
    use modint::{Mod998244353, MontgomeryModint};

    type Modint = MontgomeryModint<Mod998244353>;

    macro_rules! impl_fft_inner {
        ( $t:ty, $butterfly:ident, $deg:ident, $log:ident, $a:ident, $cache:ident, $epilogue:expr ) => {{
            $butterfly($deg, $log, $a, &($cache));
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
        fft_gentleman_sande_radix_8_montgomery_modint,
        gentleman_sande_radix_8_butterfly_montgomery_modint,
        ifft_gentleman_sande_radix_8_montgomery_modint,
        gentleman_sande_radix_8_butterfly_inv_montgomery_modint,
        |deg: usize, a: &mut [Modint]| {
            let inv = Modint::new(deg as u32).inv();
            a.iter_mut().for_each(|c| *c *= inv)
        }
    );

    #[test]
    fn gentleman_sande_radix_8_montgomery_modint_test() {
        for i in 1..=10 {
            let n = 1 << i;
            let data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
            let mut data1 = data.clone();
            fft_gentleman_sande_radix_8_montgomery_modint(&mut data1);
            ifft_gentleman_sande_radix_8_montgomery_modint(&mut data1);
            assert_eq!(data, data1);
        }
    }
}
