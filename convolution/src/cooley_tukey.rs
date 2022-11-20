use super::common::{
    bit_reverse,
    radix_4_inner_complex, radix_4_inv_inner_complex,
    radix_4_inner_modint, radix_4_inv_inner_modint
};
use super::fft_cache::FftCache;
use complex::Complex;
use modint::{
    Mint, Mod998244353
};
use std::ops::{
    Add, Sub, Mul
};


#[inline]
fn kernel_radix_2<T>(base: usize, half_width: usize, w: T, a: &mut [T])
where T: Clone + Copy + Add<T, Output = T> + Sub<T, Output = T> + Mul<T, Output = T> {
    let (c0, c1) = (a[base], a[base+half_width] * w);
    let (w0, w1) = (c0 + c1, c0 - c1);

    a[base] = w0;
    a[base+half_width] = w1;
}

macro_rules! impl_butterfly {
    ( $t:tt, $radix2:ident, $radix2_inv:ident, $radix4:ident, $radix4_inv:ident, $radix2_inner:ident, $radix4_inner:ident, $radix4_inner_inv:ident ) => {
        #[inline]
        pub fn $radix2 (deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
                for i in 0..log {
                let backet_width = 1 << (i+1);
                let half_width = backet_width >> 1;
                let root = cache.prim_root(i+1);
                for k in (0..deg).step_by(backet_width) {
                    let mut w = $t::one();
                    for base in k..k+half_width {
                        $radix2_inner (base, half_width, w, a);
                        w *= root;
                    }
                }
            }
        }

        #[inline]
        pub fn $radix2_inv (deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in 0..log {
                let backet_width = 1 << (i+1);
                let half_width = backet_width >> 1;
                let root = cache.prim_root_inv(i+1);
                for k in (0..deg).step_by(backet_width) {
                    let mut w = $t::one();
                    for base in k..k+half_width {
                        $radix2_inner (base, half_width, w, a);
                        w *= root;
                    }
                }
            }
        }

        #[inline]
        pub fn $radix4 (deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(2) {
                if i + 1 == log {
                    let backet_width = 1 << (i+1);
                    let half_width = backet_width >> 1;
                    let root = cache.prim_root(i+1);
                    for k in (0..deg).step_by(backet_width) {
                        let mut w = $t::one();
                        for base in k..k+half_width {
                            $radix2_inner (base, half_width, w, a);
                            w *= root;
                        }
                    }
                } else {
                    let backet_width = 1 << (i+2);
                    let quarter = backet_width >> 2;
                    let root = cache.prim_root(i+2);
                    for base in (0..deg).step_by(backet_width) {
                        let mut w = $t::one();
                        for k in base..base+quarter {
                            let (c0, mut c1, mut c2, mut c3) = (a[k], a[k+quarter*2], a[k+quarter], a[k+quarter*3]);
                            let mut nw = w;
                            c1 *= nw;
                            nw *= w;
                            c2 *= nw;
                            nw *= w;
                            c3 *= nw;

                            let (w0, w1, w2, w3) = $radix4_inner (c0, c1, c2, c3, cache);

                            a[k] = w0;
                            a[k+quarter] = w1;
                            a[k+quarter*2] = w2;
                            a[k+quarter*3] = w3;
                            w *= root;
                        }
                    }
                }
            }
        }

        #[inline]
        #[target_feature(enable = "avx2")]
        pub unsafe fn $radix4_inv (deg: usize, log: usize, a: &mut [$t], cache: &FftCache<$t>) {
            for i in (0..log).step_by(2) {
                if i + 1 == log {
                    let backet_width = 1 << (i+1);
                    let half_width = backet_width >> 1;
                    let root = cache.prim_root_inv(i+1);
                    for k in (0..deg).step_by(backet_width) {
                        let mut w = $t::one();
                        for base in k..k+half_width {
                            $radix2_inner (base, half_width, w, a);
                            w *= root;
                        }
                    }
                } else {
                    let backet_width = 1 << (i+2);
                    let quarter = backet_width >> 2;
                    let root = cache.prim_root_inv(i+2);
                    for base in (0..deg).step_by(backet_width) {
                        let mut w = $t::one();
                        for k in base..base+quarter {
                            let (c0, mut c1, mut c2, mut c3) = (a[k], a[k+quarter*2], a[k+quarter], a[k+quarter*3]);
                            let mut nw = w;
                            c1 *= nw;
                            nw *= w;
                            c2 *= nw;
                            nw *= w;
                            c3 *= nw;

                            let (w0, w1, w2, w3) = $radix4_inner_inv (c0, c1, c2, c3, cache);

                            a[k] = w0;
                            a[k+quarter] = w1;
                            a[k+quarter*2] = w2;
                            a[k+quarter*3] = w3;
                            w *= root;
                        }
                    }
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
    kernel_radix_2,
    radix_4_inner_complex,
    radix_4_inv_inner_complex
);
impl_butterfly!(
    Complexf64,
    cooley_tukey_radix_2_butterfly,
    cooley_tukey_radix_2_butterfly_inv,
    cooley_tukey_radix_4_butterfly,
    cooley_tukey_radix_4_butterfly_inv,
    kernel_radix_2,
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
    kernel_radix_2,
    radix_4_inner_modint,
    radix_4_inv_inner_modint
);


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

    unsafe {
        cooley_tukey_radix_4_butterfly_inv(deg, log, a, &cache);
    }

    a.iter_mut().for_each(|c| *c = c.conjugate() / deg as f64);
}
