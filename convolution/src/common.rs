use super::fft_cache::FftCache;

use complex::Complex;
use modint::{Mint, Modulo, MontgomeryModint};
use numeric::float::Float;

#[inline]
pub fn bit_reverse<T>(deg: usize, log: usize, a: &mut [T]) {
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
pub fn radix_4_inner_complex<T: Float>(
    c0: Complex<T>,
    c1: Complex<T>,
    c2: Complex<T>,
    c3: Complex<T>,
    _cache: &FftCache<Complex<T>>,
) -> (Complex<T>, Complex<T>, Complex<T>, Complex<T>) {
    // If W = exp(-2PIi/N), then
    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1  -i  -1   i | => | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1   i  -1  -i |    | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
    (
        Complex::new(
            c0.real() + c1.real() + c2.real() + c3.real(),
            c0.imag() + c1.imag() + c2.imag() + c3.imag(),
        ),
        Complex::new(
            c0.real() + c1.imag() - c2.real() - c3.imag(),
            c0.imag() - c1.real() - c2.imag() + c3.real(),
        ),
        Complex::new(
            c0.real() - c1.real() + c2.real() - c3.real(),
            c0.imag() - c1.imag() + c2.imag() - c3.imag(),
        ),
        Complex::new(
            c0.real() - c1.imag() - c2.real() + c3.imag(),
            c0.imag() + c1.real() - c2.imag() - c3.real(),
        ),
    )
}

#[inline]
pub fn radix_4_inv_inner_complex<T: Float>(
    c0: Complex<T>,
    c1: Complex<T>,
    c2: Complex<T>,
    c3: Complex<T>,
    _cache: &FftCache<Complex<T>>,
) -> (Complex<T>, Complex<T>, Complex<T>, Complex<T>) {
    // If W = exp(2PIi/N), then
    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1   i  -1  -i | => | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1  -i  -1   i |    | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
    (
        Complex::new(
            c0.real() + c1.real() + c2.real() + c3.real(),
            c0.imag() + c1.imag() + c2.imag() + c3.imag(),
        ),
        Complex::new(
            c0.real() - c1.imag() - c2.real() + c3.imag(),
            c0.imag() + c1.real() - c2.imag() - c3.real(),
        ),
        Complex::new(
            c0.real() - c1.real() + c2.real() - c3.real(),
            c0.imag() - c1.imag() + c2.imag() - c3.imag(),
        ),
        Complex::new(
            c0.real() + c1.imag() - c2.real() - c3.imag(),
            c0.imag() - c1.real() - c2.imag() + c3.real(),
        ),
    )
}

#[inline]
pub fn radix_4_inner_modint<M: Modulo>(
    c0: Mint<M>,
    c1: Mint<M>,
    c2: Mint<M>,
    c3: Mint<M>,
    cache: &FftCache<Mint<M>>,
) -> (Mint<M>, Mint<M>, Mint<M>, Mint<M>) {
    let c0pc2 = c0.val() + c2.val();
    let c0mc2 = M::modulo() + c0.val() - c2.val();
    let c1pc3 = c1.val() + c3.val();
    let c1mc3 = M::modulo() + c1.val() - c3.val();
    let c1mc3im = c1mc3 * cache.prim_root_inv(2).val();

    (
        Mint::new(c0pc2 + c1pc3),
        Mint::new(c0mc2 - c1mc3im),
        Mint::new(c0pc2 - c1pc3),
        Mint::new(c0mc2 + c1mc3im),
    )
}

#[inline]
pub fn radix_4_inv_inner_modint<M: Modulo>(
    c0: Mint<M>,
    c1: Mint<M>,
    c2: Mint<M>,
    c3: Mint<M>,
    cache: &FftCache<Mint<M>>,
) -> (Mint<M>, Mint<M>, Mint<M>, Mint<M>) {
    let c0pc2 = c0.val() + c2.val();
    let c0mc2 = M::modulo() + c0.val() - c2.val();
    let c1pc3 = c1.val() + c3.val();
    let c1mc3 = M::modulo() + c1.val() - c3.val();
    let c1mc3im = c1mc3 * cache.prim_root_inv(2).val();

    (
        Mint::new(c0pc2 + c1pc3),
        Mint::new(c0mc2 + c1mc3im),
        Mint::new(c0pc2 - c1pc3),
        Mint::new(c0mc2 - c1mc3im),
    )
}

#[inline]
pub fn radix_4_inner_montgomery_modint<M: Modulo>(
    c0: MontgomeryModint<M>,
    c1: MontgomeryModint<M>,
    c2: MontgomeryModint<M>,
    c3: MontgomeryModint<M>,
    cache: &FftCache<MontgomeryModint<M>>,
) -> (
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
) {
    let c0pc2 = c0 + c2;
    let c0mc2 = c0 - c2;
    let c1pc3 = c1 + c3;
    let c1mc3 = c1 - c3;
    let c1mc3im = c1mc3 * cache.prim_root_inv(2);

    (
        c0pc2 + c1pc3,
        c0mc2 - c1mc3im,
        c0pc2 - c1pc3,
        c0mc2 + c1mc3im,
    )
}

#[inline]
pub fn radix_4_inv_inner_montgomery_modint<M: Modulo>(
    c0: MontgomeryModint<M>,
    c1: MontgomeryModint<M>,
    c2: MontgomeryModint<M>,
    c3: MontgomeryModint<M>,
    cache: &FftCache<MontgomeryModint<M>>,
) -> (
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
) {
    let c0pc2 = c0 + c2;
    let c0mc2 = c0 - c2;
    let c1pc3 = c1 + c3;
    let c1mc3 = c1 - c3;
    let c1mc3im = c1mc3 * cache.prim_root_inv(2);

    (
        c0pc2 + c1pc3,
        c0mc2 + c1mc3im,
        c0pc2 - c1pc3,
        c0mc2 - c1mc3im,
    )
}

#[inline]
pub fn radix_8_inner_montgomery_modint<M: Modulo>(
    c0: MontgomeryModint<M>,
    c1: MontgomeryModint<M>,
    c2: MontgomeryModint<M>,
    c3: MontgomeryModint<M>,
    c4: MontgomeryModint<M>,
    c5: MontgomeryModint<M>,
    c6: MontgomeryModint<M>,
    c7: MontgomeryModint<M>,
    cache: &FftCache<MontgomeryModint<M>>,
) -> (
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
) {
    let im = cache.prim_root_inv(2);

    let c0pc4 = c0 + c4;
    let c0mc4 = c0 - c4;
    let c2pc6 = c2 + c6;
    let c2mc6 = c2 - c6;
    let c2mc6im = c2mc6 * im;

    let c0pc4pc2pc6 = c0pc4 + c2pc6;
    let c0pc4mc2pc6 = c0pc4 - c2pc6;
    let c0mc4mc2mc6im = c0mc4 - c2mc6im;
    let c0mc4pc2mc6im = c0mc4 + c2mc6im;

    let c1pc5 = c1 + c5;
    let c1mc5 = c1 - c5;
    let c3pc7 = c3 + c7;
    let c3mc7 = c3 - c7;
    let c1mc5im = c1mc5 * im;
    let c3mc7im = c3mc7 * im;

    let w1 = cache.prim_root(3);

    let c1pc5pc3pc7 = c1pc5 + c3pc7;
    let c1pc5mc3pc7 = c1pc5 - c3pc7;
    let c1mc5immc3mc7w = (c1mc5im - c3mc7) * w1;
    let c1mc5mc3mc7imw = (c1mc5 - c3mc7im) * w1;
    let c1pc5immc3pc7im = c1pc5mc3pc7 * im;

    (
        c0pc4pc2pc6 + c1pc5pc3pc7, // c0 + c4 + c2  + c6  + c1   + c5   + c3   + c7
        c0mc4mc2mc6im + c1mc5mc3mc7imw, // c0 - c4 - c2i + c6i + c1W  - c5W  - c3iW + c7iW
        c0pc4mc2pc6 - c1pc5immc3pc7im, // c0 + c4 - c2  - c6  - c1i  - c5i  + c3i  + c7i
        c0mc4pc2mc6im - c1mc5immc3mc7w, // c0 - c4 + c2i - c6i - c1iW + c5iW + c3W  - c7W
        c0pc4pc2pc6 - c1pc5pc3pc7, // c0 + c4 + c2  + c6  - c1   - c5   - c3   - c7
        c0mc4mc2mc6im - c1mc5mc3mc7imw, // c0 - c4 - c2i + c6i - c1W  + c5W  + c3iW - c7iW
        c0pc4mc2pc6 + c1pc5immc3pc7im, // c0 + c4 - c2  - c6  + c1i  + c5i  - c3i  - c7i
        c0mc4pc2mc6im + c1mc5immc3mc7w, // c0 - c4 + c2i - c6i + c1iW - c5iW - c3W  + c7W
    )
}

#[inline]
pub fn radix_8_inv_inner_montgomery_modint<M: Modulo>(
    c0: MontgomeryModint<M>,
    c1: MontgomeryModint<M>,
    c2: MontgomeryModint<M>,
    c3: MontgomeryModint<M>,
    c4: MontgomeryModint<M>,
    c5: MontgomeryModint<M>,
    c6: MontgomeryModint<M>,
    c7: MontgomeryModint<M>,
    cache: &FftCache<MontgomeryModint<M>>,
) -> (
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
    MontgomeryModint<M>,
) {
    let im = cache.prim_root_inv(2);

    let c0pc4 = c0 + c4;
    let c0mc4 = c0 - c4;
    let c2pc6 = c2 + c6;
    let c2mc6 = c2 - c6;
    let c2mc6im = c2mc6 * im;

    let c0pc4pc2pc6 = c0pc4 + c2pc6;
    let c0pc4mc2pc6 = c0pc4 - c2pc6;
    let c0mc4mc2mc6im = c0mc4 - c2mc6im;
    let c0mc4pc2mc6im = c0mc4 + c2mc6im;

    let c1pc5 = c1 + c5;
    let c1mc5 = c1 - c5;
    let c3pc7 = c3 + c7;
    let c3mc7 = c3 - c7;
    let c1mc5im = c1mc5 * im;
    let c3mc7im = c3mc7 * im;

    let w1 = cache.prim_root_inv(3);

    let c1pc5pc3pc7 = c1pc5 + c3pc7;
    let c1pc5mc3pc7 = c1pc5 - c3pc7;
    let c1mc5impc3mc7w = (c1mc5im + c3mc7) * w1;
    let c1mc5pc3mc7imw = (c1mc5 + c3mc7im) * w1;
    let c1pc5immc3pc7im = c1pc5mc3pc7 * im;

    (
        c0pc4pc2pc6 + c1pc5pc3pc7, // c0 + c4 + c2  + c6  + c1   + c5   + c3   + c7
        c0mc4pc2mc6im + c1mc5pc3mc7imw, // c0 - c4 + c2i - c6i + c1W  - c5W  + c3iW - c7iW
        c0pc4mc2pc6 + c1pc5immc3pc7im, // c0 + c4 - c2  - c6  + c1i  + c5i  - c3i  - c7i
        c0mc4mc2mc6im + c1mc5impc3mc7w, // c0 - c4 - c2i + c6i + c1iW - c5iW + c3W  - c7W
        c0pc4pc2pc6 - c1pc5pc3pc7, // c0 + c4 + c2  + c6  - c1   - c5   - c3   - c7
        c0mc4pc2mc6im - c1mc5pc3mc7imw, // c0 - c4 + c2i - c6i - c1W  + c5W  - c3iW + c7iW
        c0pc4mc2pc6 - c1pc5immc3pc7im, // c0 + c4 - c2  - c6  - c1i  - c5i  + c3i  + c7i
        c0mc4mc2mc6im - c1mc5impc3mc7w, // c0 - c4 - c2i + c6i - c1iW + c5iW - c3W  + c7W
    )
}
