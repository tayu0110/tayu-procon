use super::common::{radix_4_inner_montgomery_modint, radix_4_inv_inner_montgomery_modint, radix_8_inner_montgomery_modint, radix_8_inv_inner_montgomery_modint};
use super::fft_cache::FftCache;
use super::simd::radix_4_kernel_gentleman_sande_avx2;
use modint::{Mod998244353, MontgomeryModint};

type Mint = MontgomeryModint<Mod998244353>;

type Radix4Inner<T> = fn(T, T, T, T, &FftCache<T>) -> (T, T, T, T);
type Radix8Inner<T> = fn(T, T, T, T, T, T, T, T, &FftCache<T>) -> (T, T, T, T, T, T, T, T);

#[inline]
fn radix_2_kernel(deg: usize, width: usize, root: Mint, a: &mut [Mint]) {
    let offset = width >> 1;
    for top in (0..deg).step_by(width) {
        let (c0, c1) = (a[top], a[top + offset]);
        a[top] = c0 + c1;
        a[top + offset] = c0 - c1;
        let mut w = root;
        for base in top + 1..top + offset {
            let (c0, c1) = (a[base], a[base + offset]);
            let (c0, c1) = (c0 + c1, c0 - c1);

            a[base] = c0;
            a[base + offset] = c1 * w;
            w *= root;
        }
    }
}

#[inline]
fn radix_4_kernel(deg: usize, width: usize, a: &mut [Mint], cache: &FftCache<Mint>, twiddle: &[Mint], radix4_inner: Radix4Inner<Mint>) {
    let log = width.trailing_zeros();
    let exp = deg >> log;
    let exp = [0, exp, exp * 2, exp * 3];
    let offset = width >> 2;
    for top in (0..deg).step_by(width) {
        let (id0, id1, id2, id3) = (top, top + offset, top + offset * 2, top + offset * 3);
        let (c0, c1, c2, c3) = (a[id0], a[id1], a[id2], a[id3]);
        let (c0, c1, c2, c3) = radix4_inner(c0, c1, c2, c3, cache);
        a[id0] = c0;
        a[id2] = c1;
        a[id1] = c2;
        a[id3] = c3;
        for base in top + 1..top + offset {
            let (id0, id1, id2, id3) = (base, base + offset, base + offset * 2, base + offset * 3);
            let (c0, c1, c2, c3) = (a[id0], a[id1], a[id2], a[id3]);
            let (c0, c1, c2, c3) = radix4_inner(c0, c1, c2, c3, cache);

            let w1 = twiddle[(exp[1] * (base - top)) & (deg - 1)];
            let w2 = twiddle[(exp[2] * (base - top)) & (deg - 1)];
            let w3 = twiddle[(exp[3] * (base - top)) & (deg - 1)];

            a[id0] = c0;
            a[id2] = c1 * w1;
            a[id1] = c2 * w2;
            a[id3] = c3 * w3;
        }
    }
}

#[inline]
fn radix_8_kernel(deg: usize, width: usize, a: &mut [Mint], cache: &FftCache<Mint>, twiddle: &[Mint], radix8_inner: Radix8Inner<Mint>) {
    let log = width.trailing_zeros();
    let offset = width >> 3;
    let exp = deg >> log;
    let exp = [0, exp, exp * 2, exp * 3, exp * 4, exp * 5, exp * 6, exp * 7];
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
            let (id0, id1, id2, id3, id4, id5, id6, id7) = (
                base,
                base + offset,
                base + offset * 2,
                base + offset * 3,
                base + offset * 4,
                base + offset * 5,
                base + offset * 6,
                base + offset * 7,
            );
            let (c0, c1, c2, c3, c4, c5, c6, c7) = (a[id0], a[id1], a[id2], a[id3], a[id4], a[id5], a[id6], a[id7]);

            let (c0, c1, c2, c3, c4, c5, c6, c7) = radix8_inner(c0, c1, c2, c3, c4, c5, c6, c7, cache);

            let w1 = twiddle[((exp[1] * (base - top)) & (deg - 1))];
            let w2 = twiddle[((exp[2] * (base - top)) & (deg - 1))];
            let w3 = twiddle[((exp[3] * (base - top)) & (deg - 1))];
            let w4 = twiddle[((exp[4] * (base - top)) & (deg - 1))];
            let w5 = twiddle[((exp[5] * (base - top)) & (deg - 1))];
            let w6 = twiddle[((exp[6] * (base - top)) & (deg - 1))];
            let w7 = twiddle[((exp[7] * (base - top)) & (deg - 1))];

            a[id0] = c0;
            a[id4] = c1 * w1;
            a[id2] = c2 * w2;
            a[id6] = c3 * w3;
            a[id1] = c4 * w4;
            a[id5] = c5 * w5;
            a[id3] = c6 * w6;
            a[id7] = c7 * w7;
        }
    }
}

#[inline]
pub fn gentleman_sande_radix_8_butterfly_montgomery_modint(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors();
    for i in (0..log).step_by(3) {
        let width = deg >> i;
        let root = cache.prim_root(log - i);
        if i + 1 == log {
            radix_2_kernel(deg, width, root, a);
        } else if i + 2 == log {
            if is_x86_feature_detected!("avx2") {
                unsafe {
                    radix_4_kernel_gentleman_sande_avx2(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
                }
            } else {
                radix_4_kernel(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
            }
        } else if i + 4 == log {
            if is_x86_feature_detected!("avx2") {
                unsafe {
                    radix_4_kernel_gentleman_sande_avx2(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
                    let width = deg >> (i + 2);
                    radix_4_kernel_gentleman_sande_avx2(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
                }
            } else {
                radix_4_kernel(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
                let width = deg >> (i + 2);
                radix_4_kernel(deg, width, a, cache, twiddle, radix_4_inner_montgomery_modint);
            }
            break;
        } else {
            radix_8_kernel(deg, width, a, cache, twiddle, radix_8_inner_montgomery_modint);
        }
    }
}

#[inline]
pub fn gentleman_sande_radix_8_butterfly_inv_montgomery_modint(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle_factors = cache.twiddle_factors_inv();
    for i in (0..log).step_by(3) {
        let width = deg >> i;
        let root = cache.prim_root_inv(log - i);
        if i + 1 == log {
            radix_2_kernel(deg, width, root, a);
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

    type MontMint998244353 = MontgomeryModint<Mod998244353>;

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
        MontMint998244353,
        fft_gentleman_sande_radix_8_montgomery_modint,
        gentleman_sande_radix_8_butterfly_montgomery_modint,
        ifft_gentleman_sande_radix_8_montgomery_modint,
        gentleman_sande_radix_8_butterfly_inv_montgomery_modint,
        |deg: usize, a: &mut [MontMint998244353]| {
            let inv = MontMint998244353::new(deg as u32).inv();
            a.iter_mut().for_each(|c| *c *= inv)
        }
    );

    const N: u32 = 1 << 7;

    #[test]
    fn gentleman_sande_radix_8_montgomery_modint_test() {
        let data: Vec<MontMint998244353> = (1..=N).map(|v| MontMint998244353::new(v)).collect();
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_8_montgomery_modint(&mut data1);
        ifft_gentleman_sande_radix_8_montgomery_modint(&mut data1);
        assert_eq!(data, data1);
    }
}
