use super::common::{
    bit_reverse, radix_4_inner_complex, radix_4_inner_montgomery_modint, radix_4_inv_inner_complex,
    radix_4_inv_inner_montgomery_modint, radix_8_inner_complex, radix_8_inner_montgomery_modint,
    radix_8_inv_inner_complex, radix_8_inv_inner_montgomery_modint,
};
use super::fft_cache::FftCache;
use complex::Complex;
use modint::{Mod998244353, MontgomeryModint};
use std::ops::{Add, Mul, MulAssign, Sub};

#[inline]
fn radix_2_kernel<T>(deg: usize, backet_width: usize, root: T, a: &mut [T])
where
    T: Clone + Copy + Add<T, Output = T> + Sub<T, Output = T> + Mul<T, Output = T> + MulAssign,
{
    let offset = backet_width >> 1;
    for backet_top in (0..deg).step_by(backet_width) {
        let (c0, c1) = (a[backet_top], a[backet_top + offset]);
        a[backet_top] = c0 + c1;
        a[backet_top + offset] = c0 - c1;
        let mut w = root;
        for base in backet_top + 1..backet_top + offset {
            let (c0, c1) = (a[base], a[base + offset]);
            let (c0, c1) = (c0 + c1, c0 - c1);

            a[base] = c0;
            a[base + offset] = c1 * w;
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
            a[backet_top + offset],
            a[backet_top + offset * 2],
            a[backet_top + offset * 3],
        );
        let (c0, c1, c2, c3) = radix_4_inner(c0, c1, c2, c3, cache);
        a[backet_top] = c0;
        a[backet_top + offset * 2] = c1;
        a[backet_top + offset] = c2;
        a[backet_top + offset * 3] = c3;
        let mut w = root;
        for base in backet_top + 1..backet_top + offset {
            let (c0, c1, c2, c3) = (
                a[base],
                a[base + offset],
                a[base + offset * 2],
                a[base + offset * 3],
            );
            let (c0, c1, c2, c3) = radix_4_inner(c0, c1, c2, c3, cache);

            let w1 = w;
            let w2 = w1 * w;
            let w3 = w2 * w;
            a[base] = c0;
            a[base + offset * 2] = c1 * w1;
            a[base + offset] = c2 * w2;
            a[base + offset * 3] = c3 * w3;
            w *= root;
        }
    }
}

#[inline]
fn radix_8_kernel<T>(
    deg: usize,
    backet_width: usize,
    root: T,
    a: &mut [T],
    cache: &FftCache<T>,
    radix_8_inner: impl Fn(T, T, T, T, T, T, T, T, &FftCache<T>) -> (T, T, T, T, T, T, T, T),
) where
    T: Clone + Copy + Add<T, Output = T> + Sub<T, Output = T> + Mul<T, Output = T> + MulAssign,
{
    let offset = backet_width >> 3;
    for backet_top in (0..deg).step_by(backet_width) {
        let (c0, c1, c2, c3, c4, c5, c6, c7) = radix_8_inner(
            a[backet_top],
            a[backet_top + offset],
            a[backet_top + offset * 2],
            a[backet_top + offset * 3],
            a[backet_top + offset * 4],
            a[backet_top + offset * 5],
            a[backet_top + offset * 6],
            a[backet_top + offset * 7],
            cache,
        );
        a[backet_top] = c0;
        a[backet_top + offset * 4] = c1;
        a[backet_top + offset * 2] = c2;
        a[backet_top + offset * 6] = c3;
        a[backet_top + offset] = c4;
        a[backet_top + offset * 5] = c5;
        a[backet_top + offset * 3] = c6;
        a[backet_top + offset * 7] = c7;
        let mut w = root;
        for base in backet_top + 1..backet_top + offset {
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

            let (c0, c1, c2, c3, c4, c5, c6, c7) =
                radix_8_inner(c0, c1, c2, c3, c4, c5, c6, c7, cache);

            let w1 = w;
            let w2 = w1 * w;
            let w3 = w2 * w;
            let w4 = w3 * w;
            let w5 = w4 * w;
            let w6 = w5 * w;
            let w7 = w6 * w;

            a[base] = c0;
            a[base + offset * 4] = c1 * w1;
            a[base + offset * 2] = c2 * w2;
            a[base + offset * 6] = c3 * w3;
            a[base + offset] = c4 * w4;
            a[base + offset * 5] = c5 * w5;
            a[base + offset * 3] = c6 * w6;
            a[base + offset * 7] = c7 * w7;
            w *= root;
        }
    }
}

macro_rules! impl_butterfly {
    ( $t:tt, $radix2:ident, $radix2_inv:ident, $radix4:ident, $radix4_inv:ident, $radix8:ident, $radix8_inv:ident, $radix4_inner:ident, $radix4_inner_inv:ident, $radix8_inner:ident, $radix8_inner_inv:ident ) => {
        #[inline]
        pub fn $radix2(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in 0..log {
                let backet_width = deg >> i;
                let root = cache.prim_root(log - i);
                radix_2_kernel(deg, backet_width, root, a);
            }
        }

        #[inline]
        pub fn $radix2_inv(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in 0..log {
                let backet_width = deg >> i;
                let root = cache.prim_root_inv(log - i);
                radix_2_kernel(deg, backet_width, root, a);
            }
        }

        #[inline]
        pub fn $radix4(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(2) {
                let backet_width = deg >> i;
                let root = cache.prim_root(log - i);
                if i + 1 == log {
                    radix_2_kernel(deg, backet_width, root, a);
                } else {
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner);
                }
            }
        }

        #[inline]
        pub fn $radix4_inv(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(2) {
                let backet_width = deg >> i;
                let root = cache.prim_root_inv(log - i);
                if i + 1 == log {
                    radix_2_kernel(deg, backet_width, root, a);
                } else {
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner_inv);
                }
            }
        }

        #[inline]
        pub fn $radix8(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(3) {
                let backet_width = deg >> i;
                let root = cache.prim_root(log - i);
                if i + 1 == log {
                    radix_2_kernel(deg, backet_width, root, a);
                } else if i + 2 == log {
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner);
                } else if i + 4 == log {
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner);
                    let backet_width = deg >> (i + 2);
                    let root = cache.prim_root(log - (i + 2));
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner);
                    break;
                } else {
                    radix_8_kernel(deg, backet_width, root, a, cache, $radix8_inner);
                }
            }
        }

        #[inline]
        pub fn $radix8_inv(deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(3) {
                let backet_width = deg >> i;
                let root = cache.prim_root_inv(log - i);
                if i + 1 == log {
                    radix_2_kernel(deg, backet_width, root, a);
                } else if i + 2 == log {
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner_inv);
                } else if i + 4 == log {
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner_inv);
                    let backet_width = deg >> (i + 2);
                    let root = cache.prim_root_inv(log - (i + 2));
                    radix_4_kernel(deg, backet_width, root, a, cache, $radix4_inner_inv);
                    break;
                } else {
                    radix_8_kernel(deg, backet_width, root, a, cache, $radix8_inner_inv);
                }
            }
        }
    };
}

type Complexf32 = Complex<f32>;
type Complexf64 = Complex<f64>;

impl_butterfly!(
    Complexf32,
    gentleman_sande_radix_2_butterfly_f32,
    gentleman_sande_radix_2_butterfly_inv_f32,
    gentleman_sande_radix_4_butterfly_f32,
    gentleman_sande_radix_4_butterfly_inv_f32,
    gentleman_sande_radix_8_butterfly_f32,
    gentleman_sande_radix_8_butterfly_inv_f32,
    radix_4_inner_complex,
    radix_4_inv_inner_complex,
    radix_8_inner_complex,
    radix_8_inv_inner_complex
);
impl_butterfly!(
    Complexf64,
    gentleman_sande_radix_2_butterfly,
    gentleman_sande_radix_2_butterfly_inv,
    gentleman_sande_radix_4_butterfly,
    gentleman_sande_radix_4_butterfly_inv,
    gentleman_sande_radix_8_butterfly,
    gentleman_sande_radix_8_butterfly_inv,
    radix_4_inner_complex,
    radix_4_inv_inner_complex,
    radix_8_inner_complex,
    radix_8_inv_inner_complex
);

type MontMint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;
impl_butterfly!(
    MontMint998244353,
    gentleman_sande_radix_2_butterfly_montgomery_modint,
    gentleman_sande_radix_2_butterfly_inv_montgomery_modint,
    gentleman_sande_radix_4_butterfly_montgomery_modint,
    gentleman_sande_radix_4_butterfly_inv_montgomery_modint,
    gentleman_sande_radix_8_butterfly_montgomery_modint,
    gentleman_sande_radix_8_butterfly_inv_montgomery_modint,
    radix_4_inner_montgomery_modint,
    radix_4_inv_inner_montgomery_modint,
    radix_8_inner_montgomery_modint,
    radix_8_inv_inner_montgomery_modint
);

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

impl_fft!(
    Complexf64,
    fft_gentleman_sande_radix_2,
    gentleman_sande_radix_2_butterfly,
    ifft_gentleman_sande_radix_2,
    gentleman_sande_radix_2_butterfly_inv,
    |deg: usize, a: &mut [Complexf64]| a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f64)
);
impl_fft!(
    Complexf64,
    fft_gentleman_sande_radix_4,
    gentleman_sande_radix_4_butterfly,
    ifft_gentleman_sande_radix_4,
    gentleman_sande_radix_4_butterfly_inv,
    |deg: usize, a: &mut [Complexf64]| a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f64)
);
impl_fft!(
    Complexf64,
    fft_gentleman_sande_radix_8,
    gentleman_sande_radix_8_butterfly,
    ifft_gentleman_sande_radix_8,
    gentleman_sande_radix_8_butterfly_inv,
    |deg: usize, a: &mut [Complexf64]| a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f64)
);

impl_fft!(
    Complexf32,
    fft_gentleman_sande_radix_2_f32,
    gentleman_sande_radix_2_butterfly_f32,
    ifft_gentleman_sande_radix_2_f32,
    gentleman_sande_radix_2_butterfly_inv_f32,
    |deg: usize, a: &mut [Complexf32]| a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f32)
);
impl_fft!(
    Complexf32,
    fft_gentleman_sande_radix_4_f32,
    gentleman_sande_radix_4_butterfly_f32,
    ifft_gentleman_sande_radix_4_f32,
    gentleman_sande_radix_4_butterfly_inv_f32,
    |deg: usize, a: &mut [Complexf32]| a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f32)
);
impl_fft!(
    Complexf32,
    fft_gentleman_sande_radix_8_f32,
    gentleman_sande_radix_8_butterfly_f32,
    ifft_gentleman_sande_radix_8_f32,
    gentleman_sande_radix_8_butterfly_inv_f32,
    |deg: usize, a: &mut [Complexf32]| a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f32)
);

impl_fft!(
    MontMint998244353,
    fft_gentleman_sande_radix_2_montgomery_modint,
    gentleman_sande_radix_2_butterfly_montgomery_modint,
    ifft_gentleman_sande_radix_2_montgomery_modint,
    gentleman_sande_radix_2_butterfly_inv_montgomery_modint,
    |deg: usize, a: &mut [MontMint998244353]| {
        let inv = MontMint998244353::new(deg as u32).inv();
        a.iter_mut().for_each(|c| *c *= inv)
    }
);
impl_fft!(
    MontMint998244353,
    fft_gentleman_sande_radix_4_montgomery_modint,
    gentleman_sande_radix_4_butterfly_montgomery_modint,
    ifft_gentleman_sande_radix_4_montgomery_modint,
    gentleman_sande_radix_4_butterfly_inv_montgomery_modint,
    |deg: usize, a: &mut [MontMint998244353]| {
        let inv = MontMint998244353::new(deg as u32).inv();
        a.iter_mut().for_each(|c| *c *= inv)
    }
);
impl_fft!(
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

#[cfg(test)]
mod tests {
    use super::{
        fft_gentleman_sande_radix_2, fft_gentleman_sande_radix_4,
        fft_gentleman_sande_radix_4_montgomery_modint, fft_gentleman_sande_radix_8,
        fft_gentleman_sande_radix_8_montgomery_modint, ifft_gentleman_sande_radix_2,
        ifft_gentleman_sande_radix_4, ifft_gentleman_sande_radix_8,
        ifft_gentleman_sande_radix_8_montgomery_modint,
    };
    use complex::Complex;
    use modint::{Mod998244353, MontgomeryModint};

    fn calc_diff(a: &[Complex], b: &[Complex]) -> f64 {
        let mut diff_max = 0.0;
        for (d, v) in a.into_iter().zip(b.into_iter()) {
            if (d.real() - v.real()).abs() > diff_max {
                diff_max = (d.real() - v.real()).abs();
            }
            if (d.imag() - v.imag()).abs() > diff_max {
                diff_max = (d.imag() - v.imag()).abs();
            }
        }

        diff_max
    }

    #[test]
    fn gentleman_sande_radix_2_test() {
        let data: Vec<Complex> = (1..=32).map(|v| (v as f64).into()).collect();
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_2(&mut data1);
        ifft_gentleman_sande_radix_2(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn gentleman_sande_radix_4_test() {
        let data: Vec<Complex> = (1..=32).map(|v| (v as f64).into()).collect();
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_4(&mut data1);
        ifft_gentleman_sande_radix_4(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn gentleman_sande_radix_8_test() {
        let data: Vec<Complex> = (1..=32).map(|v| (v as f64).into()).collect();
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_8(&mut data1);
        ifft_gentleman_sande_radix_8(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn gentleman_sande_radix_2_radix_4_compare_test() {
        let data: Vec<Complex> = (1..=32).map(|v| (v as f64).into()).collect();
        let mut data1 = data.clone();
        let mut data2 = data.clone();
        fft_gentleman_sande_radix_2(&mut data1);
        fft_gentleman_sande_radix_4(&mut data2);
        let diff_max = calc_diff(&data1, &data2);
        assert!(diff_max < 1e-10);

        ifft_gentleman_sande_radix_2(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);

        ifft_gentleman_sande_radix_4(&mut data2);
        let diff_max = calc_diff(&data, &data2);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn gentleman_sande_radix_8_montgomery_modint_test() {
        type MontMint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;
        let data: Vec<MontMint998244353> = (1..=32).map(|v| MontMint998244353::new(v)).collect();
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_8_montgomery_modint(&mut data1);
        ifft_gentleman_sande_radix_8_montgomery_modint(&mut data1);
        assert_eq!(data, data1);
    }

    #[test]
    fn gentleman_sande_radix_4_radix_8_montgomery_modint_compare_test() {
        type MontMint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;
        let data: Vec<MontMint998244353> = (1..=32).map(|v| MontMint998244353::new(v)).collect();
        let mut data1 = data.clone();
        let mut data2 = data.clone();
        fft_gentleman_sande_radix_8_montgomery_modint(&mut data1);
        fft_gentleman_sande_radix_4_montgomery_modint(&mut data2);
        assert_eq!(data1, data2);
    }
}
