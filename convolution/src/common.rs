use super::fft_cache::FftCache;

use complex::Complex;
use modint::{Modulo, MontgomeryModint, MontgomeryMultiplication};
use numeric::{float::Float, Integer};

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
pub fn complex_prim_root_f32(nth: usize) -> Complex<f32> {
    // W = exp(-2PI/N), N = backet_width
    Complex::from_polar(1.0, -2.0 * std::f32::consts::PI / nth as f32)
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
pub fn radix_8_inner_complex<T: Float>(
    c0: Complex<T>,
    c1: Complex<T>,
    c2: Complex<T>,
    c3: Complex<T>,
    c4: Complex<T>,
    c5: Complex<T>,
    c6: Complex<T>,
    c7: Complex<T>,
    cache: &FftCache<Complex<T>>,
) -> (
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
) {
    // If W = exp(-2PIi/N), then
    // | W^0  W^0  W^0  W^0  W^0  W^0  W^0  W^0  |   | W^0  W^0  W^0  W^0  W^0  W^0  W^0  W^0 |   | 1   1   1   1   1   1   1   1 |
    // | W^0  W^1  W^2  W^3  W^4  W^5  W^6  W^7  |   | W^0  W^1  W^2  W^3  W^4  W^5  W^6  W^7 |   | 1   W  -i -iW  -1  -W   i  iW |
    // | W^0  W^2  W^4  W^6  W^8  W^10 W^12 W^14 |   | W^0  W^2  W^4  W^6  W^0  W^2  W^4  W^6 |   | 1  -i  -1   i   1  -i  -1   i |
    // | W^0  W^3  W^6  W^9  W^12 W^15 W^18 W^21 | = | W^0  W^3  W^6  W^1  W^4  W^7  W^2  W^5 | = | 1 -iW   i   W  -1  iW  -i  -W |
    // | W^0  W^4  W^8  W^12 W^16 W^20 W^24 W^28 |   | W^0  W^4  W^0  W^4  W^0  W^4  W^0  W^4 |   | 1  -1   1  -1   1  -1   1  -1 |
    // | W^0  W^5  W^10 W^15 W^20 W^25 W^30 W^35 |   | W^0  W^5  W^2  W^7  W^4  W^1  W^6  W^3 |   | 1  -W  -i  iW  -1   W   i -iW |
    // | W^0  W^6  W^12 W^18 W^24 W^30 W^36 W^42 |   | W^0  W^6  W^4  W^2  W^0  W^2  W^4  W^2 |   | 1   i  -1  -i   1   i  -1  -i |
    // | W^0  W^7  W^14 W^21 W^28 W^35 W^42 W^49 |   | W^0  W^7  W^6  W^5  W^4  W^3  W^2  W^1 |   | 1  iW   i  -W  -1 -iW  -i   W |
    let c0pc4 = c0 + c4;
    let c0mc4 = c0 - c4;
    let c2pc6 = c2 + c6;
    let c2mc6 = c2 - c6;
    let c2mc6im = Complex::<T>::new(-c2mc6.imag(), c2mc6.real());

    let c0pc4pc2pc6 = c0pc4 + c2pc6;
    let c0pc4mc2pc6 = c0pc4 - c2pc6;
    let c0mc4mc2mc6im = c0mc4 - c2mc6im;
    let c0mc4pc2mc6im = c0mc4 + c2mc6im;

    let c1pc5 = c1 + c5;
    let c1mc5 = c1 - c5;
    let c3pc7 = c3 + c7;
    let c3mc7 = c3 - c7;
    let c1mc5im = Complex::<T>::new(-c1mc5.imag(), c1mc5.real());
    let c3mc7im = Complex::<T>::new(-c3mc7.imag(), c3mc7.real());

    let w1 = cache.prim_root(3);

    let c1pc5pc3pc7 = c1pc5 + c3pc7;
    let c1pc5mc3pc7 = c1pc5 - c3pc7;
    let c1mc5immc3mc7w = (c1mc5im - c3mc7) * w1;
    let c1mc5mc3mc7imw = (c1mc5 - c3mc7im) * w1;
    let c1pc5immc3pc7im = Complex::<T>::new(-c1pc5mc3pc7.imag(), c1pc5mc3pc7.real());

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
pub fn radix_8_inv_inner_complex<T: Float>(
    c0: Complex<T>,
    c1: Complex<T>,
    c2: Complex<T>,
    c3: Complex<T>,
    c4: Complex<T>,
    c5: Complex<T>,
    c6: Complex<T>,
    c7: Complex<T>,
    cache: &FftCache<Complex<T>>,
) -> (
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
    Complex<T>,
) {
    // If W = exp(2PIi/N), then
    // | W^0  W^0  W^0  W^0  W^0  W^0  W^0  W^0  |   | W^0  W^0  W^0  W^0  W^0  W^0  W^0  W^0 |   | 1   1   1   1   1   1   1   1 |
    // | W^0  W^1  W^2  W^3  W^4  W^5  W^6  W^7  |   | W^0  W^1  W^2  W^3  W^4  W^5  W^6  W^7 |   | 1   W   i  iW  -1  -W   i -iW |
    // | W^0  W^2  W^4  W^6  W^8  W^10 W^12 W^14 |   | W^0  W^2  W^4  W^6  W^0  W^2  W^4  W^6 |   | 1   i  -1  -i   1   i  -1   i |
    // | W^0  W^3  W^6  W^9  W^12 W^15 W^18 W^21 | = | W^0  W^3  W^6  W^1  W^4  W^7  W^2  W^5 | = | 1  iW  -i   W  -1 -iW   i  -W |
    // | W^0  W^4  W^8  W^12 W^16 W^20 W^24 W^28 |   | W^0  W^4  W^0  W^4  W^0  W^4  W^0  W^4 |   | 1  -1   1  -1   1  -1   1  -1 |
    // | W^0  W^5  W^10 W^15 W^20 W^25 W^30 W^35 |   | W^0  W^5  W^2  W^7  W^4  W^1  W^6  W^3 |   | 1  -W   i -iW  -1   W  -i  iW |
    // | W^0  W^6  W^12 W^18 W^24 W^30 W^36 W^42 |   | W^0  W^6  W^4  W^2  W^0  W^2  W^4  W^2 |   | 1  -i  -1   i   1  -i  -1   i |
    // | W^0  W^7  W^14 W^21 W^28 W^35 W^42 W^49 |   | W^0  W^7  W^6  W^5  W^4  W^3  W^2  W^1 |   | 1 -iW  -i  -W  -1  iW   i   W |
    let c0pc4 = c0 + c4;
    let c0mc4 = c0 - c4;
    let c2pc6 = c2 + c6;
    let c2mc6 = c2 - c6;
    let c2mc6im = Complex::<T>::new(-c2mc6.imag(), c2mc6.real());

    let c0pc4pc2pc6 = c0pc4 + c2pc6;
    let c0pc4mc2pc6 = c0pc4 - c2pc6;
    let c0mc4mc2mc6im = c0mc4 - c2mc6im;
    let c0mc4pc2mc6im = c0mc4 + c2mc6im;

    let c1pc5 = c1 + c5;
    let c1mc5 = c1 - c5;
    let c3pc7 = c3 + c7;
    let c3mc7 = c3 - c7;
    let c1mc5im = Complex::<T>::new(-c1mc5.imag(), c1mc5.real());
    let c3mc7im = Complex::<T>::new(-c3mc7.imag(), c3mc7.real());

    let w1 = cache.prim_root_inv(3);

    let c1pc5pc3pc7 = c1pc5 + c3pc7;
    let c1pc5mc3pc7 = c1pc5 - c3pc7;
    let c1mc5impc3mc7w = (c1mc5im + c3mc7) * w1;
    let c1mc5pc3mc7imw = (c1mc5 + c3mc7im) * w1;
    let c1pc5immc3pc7im = Complex::<T>::new(-c1pc5mc3pc7.imag(), c1pc5mc3pc7.real());

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

#[inline]
pub fn radix_4_inner_montgomery_modint<
    M: Modulo<T>,
    T: Integer + MontgomeryMultiplication<M, T>,
>(
    c0: MontgomeryModint<M, T>,
    c1: MontgomeryModint<M, T>,
    c2: MontgomeryModint<M, T>,
    c3: MontgomeryModint<M, T>,
    cache: &FftCache<MontgomeryModint<M, T>>,
) -> (
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
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
pub fn radix_4_inv_inner_montgomery_modint<
    M: Modulo<T>,
    T: Integer + MontgomeryMultiplication<M, T>,
>(
    c0: MontgomeryModint<M, T>,
    c1: MontgomeryModint<M, T>,
    c2: MontgomeryModint<M, T>,
    c3: MontgomeryModint<M, T>,
    cache: &FftCache<MontgomeryModint<M, T>>,
) -> (
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
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
pub fn radix_8_inner_montgomery_modint<
    M: Modulo<T>,
    T: Integer + MontgomeryMultiplication<M, T>,
>(
    c0: MontgomeryModint<M, T>,
    c1: MontgomeryModint<M, T>,
    c2: MontgomeryModint<M, T>,
    c3: MontgomeryModint<M, T>,
    c4: MontgomeryModint<M, T>,
    c5: MontgomeryModint<M, T>,
    c6: MontgomeryModint<M, T>,
    c7: MontgomeryModint<M, T>,
    cache: &FftCache<MontgomeryModint<M, T>>,
) -> (
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
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
pub fn radix_8_inv_inner_montgomery_modint<
    M: Modulo<T>,
    T: Integer + MontgomeryMultiplication<M, T>,
>(
    c0: MontgomeryModint<M, T>,
    c1: MontgomeryModint<M, T>,
    c2: MontgomeryModint<M, T>,
    c3: MontgomeryModint<M, T>,
    c4: MontgomeryModint<M, T>,
    c5: MontgomeryModint<M, T>,
    c6: MontgomeryModint<M, T>,
    c7: MontgomeryModint<M, T>,
    cache: &FftCache<MontgomeryModint<M, T>>,
) -> (
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
    MontgomeryModint<M, T>,
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
