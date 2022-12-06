use super::fft_cache::FftCache;

use modint::{Modulo, MontgomeryModint, MontgomeryMultiplication};
use numeric::Integer;

#[inline]
#[allow(dead_code)]
pub fn bit_reverse<T>(deg: usize, log: usize, a: &mut [T]) {
    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
        }
    }
}

#[inline]
pub fn radix_4_inner_montgomery_modint<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>>(
    c0: MontgomeryModint<M, T>,
    c1: MontgomeryModint<M, T>,
    c2: MontgomeryModint<M, T>,
    c3: MontgomeryModint<M, T>,
    cache: &FftCache<MontgomeryModint<M, T>>,
) -> (MontgomeryModint<M, T>, MontgomeryModint<M, T>, MontgomeryModint<M, T>, MontgomeryModint<M, T>) {
    let c0pc2 = c0 + c2;
    let c0mc2 = c0 - c2;
    let c1pc3 = c1 + c3;
    let c1mc3 = c1 - c3;
    let c1mc3im = c1mc3 * cache.prim_root(2);

    (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
}

#[inline]
pub fn radix_4_inv_inner_montgomery_modint<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>>(
    c0: MontgomeryModint<M, T>,
    c1: MontgomeryModint<M, T>,
    c2: MontgomeryModint<M, T>,
    c3: MontgomeryModint<M, T>,
    cache: &FftCache<MontgomeryModint<M, T>>,
) -> (MontgomeryModint<M, T>, MontgomeryModint<M, T>, MontgomeryModint<M, T>, MontgomeryModint<M, T>) {
    let c0pc2 = c0 + c2;
    let c0mc2 = c0 - c2;
    let c1pc3 = c1 + c3;
    let c1mc3 = c1 - c3;
    let c1mc3im = c1mc3 * cache.prim_root_inv(2);

    (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
}

#[inline]
pub fn radix_8_inner_montgomery_modint<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>>(
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
    let im = cache.prim_root(2);

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
    let c1mc5impc3mc7w = (c1mc5im + c3mc7) * w1;
    let c1mc5pc3mc7imw = (c1mc5 + c3mc7im) * w1;
    let c1pc5immc3pc7im = c1pc5mc3pc7 * im;

    (
        c0pc4pc2pc6 + c1pc5pc3pc7,      // c0 + c4 + c2  + c6  + c1   + c5   + c3   + c7
        c0mc4pc2mc6im + c1mc5pc3mc7imw, // c0 - c4 + c2i - c6i + c1W  - c5W  + c3iW - c7iW
        c0pc4mc2pc6 + c1pc5immc3pc7im,  // c0 + c4 - c2  - c6  + c1i  + c5i  - c3i  - c7i
        c0mc4mc2mc6im + c1mc5impc3mc7w, // c0 - c4 - c2i + c6i + c1iW - c5iW + c3W  - c7W
        c0pc4pc2pc6 - c1pc5pc3pc7,      // c0 + c4 + c2  + c6  - c1   - c5   - c3   - c7
        c0mc4pc2mc6im - c1mc5pc3mc7imw, // c0 - c4 + c2i - c6i - c1W  + c5W  - c3iW + c7iW
        c0pc4mc2pc6 - c1pc5immc3pc7im,  // c0 + c4 - c2  - c6  - c1i  - c5i  + c3i  + c7i
        c0mc4mc2mc6im - c1mc5impc3mc7w, // c0 - c4 - c2i + c6i - c1iW + c5iW - c3W  + c7W
    )
}

#[inline]
pub fn radix_8_inv_inner_montgomery_modint<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>>(
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
        c0pc4pc2pc6 + c1pc5pc3pc7,      // c0 + c4 + c2  + c6  + c1   + c5   + c3   + c7
        c0mc4pc2mc6im + c1mc5pc3mc7imw, // c0 - c4 + c2i - c6i + c1W  - c5W  + c3iW - c7iW
        c0pc4mc2pc6 + c1pc5immc3pc7im,  // c0 + c4 - c2  - c6  + c1i  + c5i  - c3i  - c7i
        c0mc4mc2mc6im + c1mc5impc3mc7w, // c0 - c4 - c2i + c6i + c1iW - c5iW + c3W  - c7W
        c0pc4pc2pc6 - c1pc5pc3pc7,      // c0 + c4 + c2  + c6  - c1   - c5   - c3   - c7
        c0mc4pc2mc6im - c1mc5pc3mc7imw, // c0 - c4 + c2i - c6i - c1W  + c5W  - c3iW + c7iW
        c0pc4mc2pc6 - c1pc5immc3pc7im,  // c0 + c4 - c2  - c6  - c1i  - c5i  + c3i  + c7i
        c0mc4mc2mc6im - c1mc5impc3mc7w, // c0 - c4 - c2i + c6i - c1iW + c5iW - c3W  + c7W
    )
}
