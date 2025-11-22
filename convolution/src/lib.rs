#[cfg(feature = "arbitrary-modulo-convolution")]
mod arbitrary_modulo_convolution;

use std::iter::repeat;
use std::mem::transmute;

#[cfg(feature = "arbitrary-modulo-convolution")]
pub use arbitrary_modulo_convolution::*;
use montgomery_modint::{
    Mod880803841, Mod897581057, Mod998244353, Modulo, MontgomeryModint, MontgomeryModintx8,
};
use number_theoretic_transform::{utility, NumberTheoreticTransform};

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

/// Multiply each element of `a` and `b` and store in `a`.  
/// `a.len()` and `b.len()` need not be aligned to a power of 2.
///
/// # Panics
/// `a.len()` must be equal to `b.len()`.  
///
/// # Examples
/// ```rust
/// use convolution::hadamard;
/// use montgomery_modint::Mod998244353;
///
/// let mut a = vec![0.into(), 1.into(), 2.into(), 3.into()];
/// let b = vec![1.into(), 2.into(), 4.into(), 8.into()];
/// hadamard::<Mod998244353>(&mut a, &b);
/// assert_eq!(a, vec![0.into(), 2.into(), 8.into(), 24.into()]);
/// ```
#[inline]
pub fn hadamard<M: Modulo>(a: &mut [Modint<M>], b: &[Modint<M>]) {
    assert_eq!(a.len(), b.len());
    let mut ait = a.chunks_exact_mut(8);
    let mut bit = b.chunks_exact(8);
    for (a, b) in ait.by_ref().zip(bit.by_ref()) {
        unsafe { (Modintx8::load(a.as_ptr()) * Modintx8::load(b.as_ptr())).store(a.as_mut_ptr()) }
    }
    ait.into_remainder()
        .iter_mut()
        .zip(bit.remainder())
        .for_each(|(a, b)| *a *= *b);
}

/// Convolve `a` and `b` with mod `M`.
///
/// `a` and `b` need not be within mod `M` and `Vec::len` of them can be different.  
/// `M` need not be NTT Friendly and there is no length limit.
///
/// The length of `a` and `b` is adjusted so that the result of the convolution does not cycle.
///
/// # Examples
/// ```rust
/// use convolution::convolution;
/// use montgomery_modint::Mod998244353;
///
/// let res = convolution::<Mod998244353>(vec![1, 2, 3, 4], vec![5, 6, 7, 8, 9]);
/// assert_eq!(res, vec![5, 16, 34, 60, 70, 70, 59, 36]);
/// ```
pub fn convolution<M: Modulo>(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    unsafe {
        utility::u32tomint::<M>(&mut a);
        utility::u32tomint::<M>(&mut b);
        let mut res = convolution_mod::<M>(
            transmute::<Vec<u32>, Vec<MontgomeryModint<M>>>(a),
            transmute::<Vec<u32>, Vec<MontgomeryModint<M>>>(b),
        );
        utility::minttou32(&mut res);
        transmute(res)
    }
}

fn convolution_mod_ntt_friendly<M: Modulo>(
    mut a: Vec<Modint<M>>,
    mut b: Vec<Modint<M>>,
) -> Vec<Modint<M>> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();

    a.resize(n, Modint::zero());
    b.resize(n, Modint::zero());

    a.ntt();
    b.ntt();

    hadamard(&mut a, &b);

    a.intt();
    a.truncate(deg);
    a
}

fn convolution_mod_not_ntt_friendly<M: Modulo>(
    a: Vec<Modint<M>>,
    b: Vec<Modint<M>>,
) -> Vec<Modint<M>> {
    let c1 = convolution_mod::<Mod880803841>(
        a.iter().map(|a| Modint::new(a.val())).collect(),
        b.iter().map(|b| Modint::new(b.val())).collect(),
    );
    let c2 = convolution_mod::<Mod897581057>(
        a.iter().map(|a| Modint::new(a.val())).collect(),
        b.iter().map(|b| Modint::new(b.val())).collect(),
    );
    let c3 = convolution_mod::<Mod998244353>(
        a.iter().map(|a| Modint::new(a.val())).collect(),
        b.iter().map(|b| Modint::new(b.val())).collect(),
    );

    const P: [u64; 3] = [
        Mod880803841::N as u64,
        Mod897581057::N as u64,
        Mod998244353::N as u64,
    ];
    const P1P2: u64 = P[0] * P[1] % P[2];
    let p1p2mod: u64 = P[0] * P[1] % M::N as u64;
    let p1i = Modint::<Mod897581057>::new(P[0] as u32).inv().val() as u64;
    let p2i = Modint::<Mod998244353>::new(P1P2 as u32).inv().val() as u64;
    c1.iter()
        .map(Modint::val)
        .zip(c2.iter().map(Modint::val).zip(c3.iter().map(Modint::val)))
        .map(|(c1, (c2, c3))| {
            let t1 = (c2 as u64 + P[1] - c1 as u64) * p1i % P[1];
            let res2 = (c1 as u64 + t1 * P[0]) % P[2];
            let res3 = (c1 as u64 + t1 * P[0]) % M::N as u64;
            let t2 = (c3 as u64 + P[2] - res2) * p2i % P[2];
            Modint::<M>::from(res3 + t2 * p1p2mod)
        })
        .collect()
}

/// Convolve `a` and `b` with mod `M`.
///
/// `M` need not be NTT Friendly and there is no length limit.  
/// It is better to use `convolution` when you convolve `u32` arrays.
///
/// The length of `a` and `b` is adjusted so that the result of the convolution does not cycle.
///
/// # Examples
/// ```rust
/// use convolution::convolution_mod;
/// use montgomery_modint::Mod998244353;
///
/// let res = convolution_mod::<Mod998244353>(
///     vec![1.into(), 2.into(), 3.into(), 4.into()],
///     vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()],
/// );
/// assert_eq!(
///     res,
///     vec![5.into(), 16.into(), 34.into(), 60.into(), 70.into(), 70.into(), 59.into(), 36.into()]
/// );
/// ```
pub fn convolution_mod<M: Modulo>(mut a: Vec<Modint<M>>, mut b: Vec<Modint<M>>) -> Vec<Modint<M>> {
    if a.len() < b.len() {
        (a, b) = (b, a);
    }

    let m = a.len() + b.len() - 1;
    if b.len() <= 8 {
        a.resize(m, Modint::zero());
        for i in (0..m).rev() {
            let mut res = Modint::zero();
            for (j, &r) in b.iter().enumerate().take_while(|&(j, _)| i >= j) {
                res += a[i - j] * r;
            }
            a[i] = res;
        }
        return a;
    }

    if m.next_power_of_two() <= 1 << (M::N - 1).trailing_zeros() {
        return convolution_mod_ntt_friendly(a, b);
    }

    // THRESH is as same as the return value of the following block.
    // {
    //     let m880 = (Mod880803841::N - 1).trailing_zeros();
    //     let m897 = (Mod897581057::N - 1).trailing_zeros();
    //     let m998 = (Mod998244353::N - 1).trailing_zeros();
    //     let a = if m880 < m897 { m880 } else { m897 };
    //     if a < m998 { a } else { m998 }
    // }
    const THRESH: u32 = 23;

    if m.next_power_of_two() <= 1 << THRESH {
        return convolution_mod_not_ntt_friendly(a, b);
    }

    let n = a.len().next_power_of_two() >> 1;
    if a.len() > n && b.len() > n {
        let a1 = a.split_off(n);
        let b1 = b.split_off(n);

        let mut z0 = convolution_mod(a.clone(), b.clone());
        let z2 = convolution_mod(a1.clone(), b1.clone());

        let mut z1 = z0.clone();
        z1.iter_mut().zip(&z2).for_each(|(s, t)| *s += *t);

        let (mut a1m0, mut b1m0) = (a, b);
        for (s, t) in [(&mut a1m0, a1), (&mut b1m0, b1)] {
            s.iter_mut()
                .zip(t.into_iter().chain(repeat(Modint::zero())))
                .for_each(|(s, t)| *s = t - *s);
        }

        z1.iter_mut()
            .zip(convolution_mod(a1m0, b1m0))
            .for_each(|(s, t)| *s -= t);

        z0.resize(m, Modint::zero());
        z0[n..].iter_mut().zip(z1).for_each(|(s, t)| *s += t);
        z0[n * 2..].iter_mut().zip(z2).for_each(|(s, t)| *s += t);
        return z0;
    }

    let a1 = a.split_off(n);
    let mut lo = convolution_mod(a, b.clone());
    let hi = convolution_mod(a1, b);
    lo.resize(m, Modint::zero());
    lo[n..].iter_mut().zip(hi).for_each(|(s, t)| *s += t);

    lo
}
