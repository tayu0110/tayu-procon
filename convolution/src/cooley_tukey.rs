use super::common::{
    bit_reverse, radix_4_inner_complex, radix_4_inner_modint, radix_4_inner_montgomery_modint,
    radix_4_inv_inner_complex, radix_4_inv_inner_modint, radix_4_inv_inner_montgomery_modint,
    radix_8_inv_inner_montgomery_modint,
};
use super::fft_cache::FftCache;
use complex::Complex;
use modint::{Mint, Mod998244353, MontgomeryModint};
use std::ops::{Add, Mul, MulAssign, Sub};

#[inline]
fn radix_2_kernel<T>(deg: usize, backet_width: usize, root: T, a: &mut [T])
where
    T: Clone + Copy + Add<T, Output = T> + Sub<T, Output = T> + Mul<T, Output = T> + MulAssign,
{
    let offset = backet_width >> 1;
    for backet_top in (0..deg).step_by(backet_width) {
        let (c0, c1) = (a[backet_top], a[backet_top + offset]);
        let (c0, c1) = (c0 + c1, c0 - c1);
        a[backet_top] = c0;
        a[backet_top + offset] = c1;
        let mut w = root;
        for base in backet_top + 1..backet_top + offset {
            let (c0, c1) = (a[base], a[base + offset] * w);
            let (w0, w1) = (c0 + c1, c0 - c1);

            a[base] = w0;
            a[base + offset] = w1;
            w *= root;
        }
    }
}

#[inline]
fn radix_4_kernel<T>(
    deg: usize,
    backet_width: usize,
    root: T,
    a: &mut [T],
    cache: &FftCache<T>,
    radix_4_inner: impl Fn(T, T, T, T, &FftCache<T>) -> (T, T, T, T),
) where
    T: Clone + Copy + Add<T, Output = T> + Sub<T, Output = T> + Mul<T, Output = T> + MulAssign,
{
    let offset = backet_width >> 2;
    for backet_top in (0..deg).step_by(backet_width) {
        let (c0, c1, c2, c3) = (
            a[backet_top],
            a[backet_top + offset * 2],
            a[backet_top + offset],
            a[backet_top + offset * 3],
        );
        let (c0, c1, c2, c3) = radix_4_inner(c0, c1, c2, c3, cache);
        a[backet_top] = c0;
        a[backet_top + offset] = c1;
        a[backet_top + offset * 2] = c2;
        a[backet_top + offset * 3] = c3;
        let mut w = root;
        for base in backet_top + 1..backet_top + offset {
            let w1 = w;
            let w2 = w1 * w;
            let w3 = w2 * w;
            let (c0, c1, c2, c3) = (
                a[base],
                a[base + offset * 2] * w1,
                a[base + offset] * w2,
                a[base + offset * 3] * w3,
            );

            let (c0, c1, c2, c3) = radix_4_inner(c0, c1, c2, c3, cache);

            a[base] = c0;
            a[base + offset] = c1;
            a[base + offset * 2] = c2;
            a[base + offset * 3] = c3;
            w *= root;
        }
    }
}

macro_rules! impl_butterfly {
    ( $t:tt, $radix2:ident, $radix2_inv:ident, $radix4:ident, $radix4_inv:ident, $radix4_inner:ident, $radix4_inner_inv:ident ) => {
        #[inline]
        pub fn $radix2(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in 0..log {
                let backet_width = 1 << (i + 1);
                let root = cache.prim_root(i + 1);
                radix_2_kernel(deg, backet_width, root, a);
            }
        }

        #[inline]
        pub fn $radix2_inv(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in 0..log {
                let backet_width = 1 << (i + 1);
                let root = cache.prim_root_inv(i + 1);
                radix_2_kernel(deg, backet_width, root, a);
            }
        }

        #[inline]
        pub fn $radix4(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(2) {
                if i + 1 == log {
                    let backet_width = 1 << (i + 1);
                    let root = cache.prim_root(i + 1);
                    radix_2_kernel(deg, backet_width, root, a);
                } else {
                    let backet_width = 1 << (i + 2);
                    let root = cache.prim_root(i + 2);
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner);
                }
            }
        }

        #[inline]
        pub fn $radix4_inv(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(2) {
                if i + 1 == log {
                    let backet_width = 1 << (i + 1);
                    let root = cache.prim_root_inv(i + 1);
                    radix_2_kernel(deg, backet_width, root, a);
                } else {
                    let backet_width = 1 << (i + 2);
                    let root = cache.prim_root_inv(i + 2);
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner_inv);
                }
            }
        }
    };
}

type Complexf32 = Complex<f32>;
type Complexf64 = Complex<f64>;

impl_butterfly!(
    Complexf32,
    cooley_tukey_radix_2_butterfly_f32,
    cooley_tukey_radix_2_butterfly_inv_f32,
    cooley_tukey_radix_4_butterfly_f32,
    cooley_tukey_radix_4_butterfly_inv_f32,
    radix_4_inner_complex,
    radix_4_inv_inner_complex
);
impl_butterfly!(
    Complexf64,
    cooley_tukey_radix_2_butterfly,
    cooley_tukey_radix_2_butterfly_inv,
    cooley_tukey_radix_4_butterfly,
    cooley_tukey_radix_4_butterfly_inv,
    radix_4_inner_complex,
    radix_4_inv_inner_complex
);

type Mint998244353 = Mint<Mod998244353>;
impl_butterfly!(
    Mint998244353,
    cooley_tukey_radix_2_butterfly_modint,
    cooley_tukey_radix_2_butterfly_inv_modint,
    cooley_tukey_radix_4_butterfly_modint,
    cooley_tukey_radix_4_butterfly_inv_modint,
    radix_4_inner_modint,
    radix_4_inv_inner_modint
);

type MontMint998244353 = MontgomeryModint<Mod998244353>;
impl_butterfly!(
    MontMint998244353,
    cooley_tukey_radix_2_butterfly_montgomery_modint,
    cooley_tukey_radix_2_butterfly_inv_montgomery_modint,
    cooley_tukey_radix_4_butterfly_montgomery_modint,
    cooley_tukey_radix_4_butterfly_inv_montgomery_modint,
    radix_4_inner_montgomery_modint,
    radix_4_inv_inner_montgomery_modint
);

#[inline]
pub fn cooley_tukey_radix_8_butterfly_inv_montgomery_modint(
    deg: usize,
    log: usize,
    a: &mut [MontMint998244353],
    cache: &FftCache<MontMint998244353>,
) {
    for i in (0..log).step_by(3) {
        if i + 1 == log {
            let backet_width = 1 << (i + 1);
            let root = cache.prim_root_inv(i + 1);
            radix_2_kernel(deg, backet_width, root, a);
        } else if i + 2 == log {
            let backet_width = 1 << (i + 2);
            let root = cache.prim_root_inv(i + 2);
            radix_4_kernel(
                deg,
                backet_width,
                root,
                a,
                cache,
                radix_4_inv_inner_montgomery_modint,
            );
        } else {
            let backet_width = 1 << (i + 3);
            let offset = backet_width >> 3;
            let root = cache.prim_root_inv(i + 3);
            for backet_top in (0..deg).step_by(backet_width) {
                let (c0, c1, c2, c3, c4, c5, c6, c7) = radix_8_inv_inner_montgomery_modint(
                    a[backet_top],
                    a[backet_top + offset * 4],
                    a[backet_top + offset * 2],
                    a[backet_top + offset * 6],
                    a[backet_top + offset],
                    a[backet_top + offset * 5],
                    a[backet_top + offset * 3],
                    a[backet_top + offset * 7],
                    cache,
                );
                a[backet_top] = c0;
                a[backet_top + offset] = c1;
                a[backet_top + offset * 2] = c2;
                a[backet_top + offset * 3] = c3;
                a[backet_top + offset * 4] = c4;
                a[backet_top + offset * 5] = c5;
                a[backet_top + offset * 6] = c6;
                a[backet_top + offset * 7] = c7;
                let mut w = root;
                for base in backet_top + 1..backet_top + offset {
                    let w1 = w;
                    let w2 = w1 * w;
                    let w3 = w2 * w;
                    let w4 = w3 * w;
                    let w5 = w4 * w;
                    let w6 = w5 * w;
                    let w7 = w6 * w;
                    let (c0, c1, c2, c3, c4, c5, c6, c7) = (
                        a[base],
                        a[base + offset * 4] * w1,
                        a[base + offset * 2] * w2,
                        a[base + offset * 6] * w3,
                        a[base + offset] * w4,
                        a[base + offset * 5] * w5,
                        a[base + offset * 3] * w6,
                        a[base + offset * 7] * w7,
                    );

                    let (c0, c1, c2, c3, c4, c5, c6, c7) =
                        radix_8_inv_inner_montgomery_modint(c0, c1, c2, c3, c4, c5, c6, c7, cache);

                    a[base] = c0;
                    a[base + offset] = c1;
                    a[base + offset * 2] = c2;
                    a[base + offset * 3] = c3;
                    a[base + offset * 4] = c4;
                    a[base + offset * 5] = c5;
                    a[base + offset * 6] = c6;
                    a[base + offset * 7] = c7;
                    w *= root;
                }
            }
        }
    }
}

pub fn fft_cooley_tukey_radix_2(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    bit_reverse(deg, log, a);

    let cache = FftCache::<Complex<f64>>::new(log);

    cooley_tukey_radix_2_butterfly(deg, log, a, &cache);
}

pub fn ifft_cooley_tukey_radix_2(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    bit_reverse(deg, log, a);

    let cache = FftCache::<Complex<f64>>::new(log);

    cooley_tukey_radix_2_butterfly_inv(deg, log, a, &cache);

    a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f64);
}

pub fn fft_cooley_tukey_radix_4(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    bit_reverse(deg, log, a);

    let cache = FftCache::<Complex<f64>>::new(log);

    cooley_tukey_radix_4_butterfly(deg, log, a, &cache);
}

pub fn ifft_cooley_tukey_radix_4(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    bit_reverse(deg, log, a);

    let cache = FftCache::<Complex<f64>>::new(log);

    cooley_tukey_radix_4_butterfly_inv(deg, log, a, &cache);

    a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f64);
}
