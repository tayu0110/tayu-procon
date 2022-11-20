use super::fft_cache::FftCache;

use complex::Complex;
use numeric::float::Float;
use modint::{
    Mint, Modulo
};

#[inline]
pub fn bit_reverse(deg: usize, log: usize, a: &mut [Complex<f64>]) {
    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
        }
    }
}

#[inline]
pub fn complex_prim_root(nth: usize) -> Complex {
    // W = exp(-2PI/N), N = backet_width
    Complex::from_polar(1.0, -2.0 * std::f64::consts::PI / nth as f64)
}

#[inline]
#[allow(dead_code)]
pub fn complex_prim_root_inv(nth: usize) -> Complex {
    // W = exp(2PI/N), N = backet_width
    Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / nth as f64)
}

#[inline]
pub fn complex_prim_root_f32(nth: usize) -> Complex<f32> {
    // W = exp(-2PI/N), N = backet_width
    Complex::from_polar(1.0, -2.0 * std::f32::consts::PI / nth as f32)
}

#[inline]
#[allow(dead_code)]
pub fn complex_prim_root_inv_f32(nth: usize) -> Complex<f32> {
    // W = exp(2PI/N), N = backet_width
    Complex::from_polar(1.0, 2.0 * std::f32::consts::PI / nth as f32)
}

#[inline]
pub fn radix_4_inner_complex<T: Float>(c0: Complex<T>, c1: Complex<T>, c2: Complex<T>, c3: Complex<T>, _cache: &FftCache<Complex<T>>) -> (Complex<T>, Complex<T>, Complex<T>, Complex<T>) {
    // If W = exp(-2PIi/N), then
    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1  -i  -1   i | => | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1   i  -1  -i |    | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
    (
        Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
        Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real()),
        Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
        Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real())
    )
}

#[inline]
pub fn radix_4_inv_inner_complex<T: Float>(c0: Complex<T>, c1: Complex<T>, c2: Complex<T>, c3: Complex<T>, _cache: &FftCache<Complex<T>>) -> (Complex<T>, Complex<T>, Complex<T>, Complex<T>) {
    // If W = exp(2PIi/N), then
    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1   i  -1  -i | => | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1  -i  -1   i |    | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
    (
        Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
        Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real()),
        Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
        Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real())
    )
}

#[inline]
pub fn radix_4_inner_modint<M: Modulo>(c0: Mint<M>, c1: Mint<M>, c2: Mint<M>, c3: Mint<M>, cache: &FftCache<Mint<M>>) -> (Mint<M>, Mint<M>, Mint<M>, Mint<M>) {
    let c0pc2 = c0.val() + c2.val();
    let c0mc2 = M::modulo() + c0.val() - c2.val();
    let c1pc3 = c1.val() + c3.val();
    let c1mc3 = M::modulo() + c1.val() - c3.val();
    let c1mc3im = c1mc3 * cache.prim_root_inv(2).val();

    (Mint::new(c0pc2 + c1pc3), Mint::new(c0mc2 - c1mc3im), Mint::new(c0pc2 - c1pc3), Mint::new(c0mc2 + c1mc3im))
}

#[inline]
pub fn radix_4_inv_inner_modint<M: Modulo>(c0: Mint<M>, c1: Mint<M>, c2: Mint<M>, c3: Mint<M>, cache: &FftCache<Mint<M>>) -> (Mint<M>, Mint<M>, Mint<M>, Mint<M>) {
    let c0pc2 = c0.val() + c2.val();
    let c0mc2 = M::modulo() + c0.val() - c2.val();
    let c1pc3 = c1.val() + c3.val();
    let c1mc3 = M::modulo() + c1.val() - c3.val();
    let c1mc3im = c1mc3 * cache.prim_root_inv(2).val();

    (Mint::new(c0pc2 + c1pc3), Mint::new(c0mc2 + c1mc3im), Mint::new(c0pc2 - c1pc3), Mint::new(c0mc2 - c1mc3im))
}
