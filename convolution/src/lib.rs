// reference1: https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
// reference2: https://www.kurims.kyoto-u.ac.jp/~ooura/fftman/ftmn1_2.html#sec1_2_1
// In a normal Decimation In Frequency (DIF) FFT, the array starts the operation in normal order and are reordered into bit-reversal order according to the signal flow.
// However, the same result can be obtained by first re-ordering the array in bit-reversal order, then proceeding in order of reversal signal flow with multiplying twiddle factors that is a power of the bit-reversal order to each block.
// This method greatly reduces the amount of cache required for the twiddle factors and improves performance by making memory accesses continuous and localized.
// Similar results are obtained for the Decimation In Time (DIT) FFT.
// The normal DIF requires bit-reversal reordering after the operation (or before in the case of DIT), but when FFT and IFFT are executed in pairs, the bit-reversal reordering can be canceled by proceeding in the order of DIF and IDIT.
// In this implementation, the correct result can be obtained by proceeding in the order of DIT and IDIF.
// The implementation was based on the AtCoder Library (reference1), and reference2 was used to understand the semantics of the implementation.

pub mod common;
pub mod cooley_tukey;
mod fft_cache;
pub mod gentleman_sande;

use cooley_tukey::cooley_tukey_radix_4_butterfly;
use fft_cache::FftCache;
use gentleman_sande::gentleman_sande_radix_4_butterfly_inv;
use math::{ext_gcd, garner};
use montgomery_modint::{Mod1811939329, Mod2013265921, Mod2281701377, Mod2483027969, Mod2885681153, Mod3221225473, Mod3489660929, Modulo, MontgomeryModint};

type Modint<M> = MontgomeryModint<M>;

pub fn convolution<M: Modulo>(mut a: Vec<Modint<M>>, mut b: Vec<Modint<M>>) -> Vec<Modint<M>> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;

    a.resize(n, Modint::zero());
    b.resize(n, Modint::zero());

    let cache = FftCache::new();

    cooley_tukey_radix_4_butterfly(n, log, &mut a, &cache);
    cooley_tukey_radix_4_butterfly(n, log, &mut b, &cache);

    a.iter_mut().zip(b.into_iter()).for_each(|(a, b)| *a *= b);

    gentleman_sande_radix_4_butterfly_inv(n, log, &mut a, &cache);

    let ninv = Modint::new(n as u32).inv();
    a.resize(deg, Modint::zero());
    a.iter_mut().for_each(|v| *v *= ninv);
    a
}

pub fn convolution_998_upper223(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let na = a.iter().cloned().map(|a| Modint::<Mod3221225473>::raw(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod3221225473>::raw(b)).collect::<Vec<_>>();
    let c1 = convolution(na, nb);
    let na = a.iter().cloned().map(|a| Modint::<Mod3489660929>::raw(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod3489660929>::raw(b)).collect::<Vec<_>>();
    let c2 = convolution(na, nb);
    let na = a.into_iter().map(|a| Modint::<Mod2281701377>::raw(a)).collect::<Vec<_>>();
    let nb = b.into_iter().map(|b| Modint::<Mod2281701377>::raw(b)).collect::<Vec<_>>();
    let c3 = convolution(na, nb);

    const MOD: i64 = 998244353;
    const P: [i64; 3] = [Mod3221225473::N as i64, Mod3489660929::N as i64, Mod2281701377::N as i64];
    c1.into_iter()
        .zip(c2.into_iter().zip(c3.into_iter()))
        .map(|(c1, (c2, c3))| garner(&[c1.val() as i64, c2.val() as i64, c3.val() as i64], &P, MOD).0 as u32)
        .collect()
}

pub fn convolution_1e97(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let na = a.iter().cloned().map(|a| Modint::<Mod3221225473>::raw(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod3221225473>::raw(b)).collect::<Vec<_>>();
    let c1 = convolution(na, nb);
    let na = a.iter().cloned().map(|a| Modint::<Mod3489660929>::raw(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod3489660929>::raw(b)).collect::<Vec<_>>();
    let c2 = convolution(na, nb);
    let na = a.into_iter().map(|a| Modint::<Mod2281701377>::raw(a)).collect::<Vec<_>>();
    let nb = b.into_iter().map(|b| Modint::<Mod2281701377>::raw(b)).collect::<Vec<_>>();
    let c3 = convolution(na, nb);

    const MOD: i64 = 1000_000_007;
    const P: [i64; 3] = [Mod3221225473::N as i64, Mod3489660929::N as i64, Mod2281701377::N as i64];
    c1.into_iter()
        .zip(c2.into_iter().zip(c3.into_iter()))
        .map(|(c1, (c2, c3))| garner(&[c1.val() as i64, c2.val() as i64, c3.val() as i64], &P, MOD).0 as u32)
        .collect()
}

pub fn convolution_mod_2_64(a: Vec<u64>, b: Vec<u64>) -> Vec<u64> {
    let na = a.iter().cloned().map(|a| Modint::<Mod3221225473>::from(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod3221225473>::from(b)).collect::<Vec<_>>();
    let c1 = convolution(na, nb);
    let na = a.iter().cloned().map(|a| Modint::<Mod3489660929>::from(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod3489660929>::from(b)).collect::<Vec<_>>();
    let c2 = convolution(na, nb);
    let na = a.iter().cloned().map(|a| Modint::<Mod2281701377>::from(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod2281701377>::from(b)).collect::<Vec<_>>();
    let c3 = convolution(na, nb);
    let na = a.iter().cloned().map(|a| Modint::<Mod1811939329>::from(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod1811939329>::from(b)).collect::<Vec<_>>();
    let c4 = convolution(na, nb);
    let na = a.iter().cloned().map(|a| Modint::<Mod2013265921>::from(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod2013265921>::from(b)).collect::<Vec<_>>();
    let c5 = convolution(na, nb);
    let na = a.iter().cloned().map(|a| Modint::<Mod2483027969>::from(a)).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| Modint::<Mod2483027969>::from(b)).collect::<Vec<_>>();
    let c6 = convolution(na, nb);
    let na = a.into_iter().map(|a| Modint::<Mod2885681153>::from(a)).collect::<Vec<_>>();
    let nb = b.into_iter().map(|b| Modint::<Mod2885681153>::from(b)).collect::<Vec<_>>();
    let c7 = convolution(na, nb);

    const P: [u64; 7] = [
        Mod3221225473::N as u64,
        Mod3489660929::N as u64,
        Mod2281701377::N as u64,
        Mod1811939329::N as u64,
        Mod2013265921::N as u64,
        Mod2483027969::N as u64,
        Mod2885681153::N as u64,
    ];
    let mut res = vec![];
    for i in 0..c1.len() {
        let mut prod = vec![1; 8];
        let mut w = vec![0; 8];
        for (i, (a, &m)) in vec![c1[i].val(), c2[i].val(), c3[i].val(), c4[i].val(), c5[i].val(), c6[i].val(), c7[i].val()]
            .iter()
            .map(|&v| v as u64)
            .zip(P.iter())
            .enumerate()
        {
            let a = a % m;
            let (_, inv, _) = ext_gcd(prod[i] as i64, m as i64);
            let t = ((a as i64 - w[i] as i64) * inv).rem_euclid(m as i64);
            for (i, &p) in P.iter().enumerate().skip(i + 1) {
                w[i] = (w[i] + (t as u64 * prod[i])) % p;
                prod[i] = (prod[i] * m) % p;
            }
            w[7] = (w[7] as u128 + (t as u128 * prod[7] as u128)) as u64;
            prod[7] = (prod[7] as u128 * m as u128) as u64;
        }
        res.push(w[7])
    }
    res
}

#[cfg(test)]
mod tests {
    use super::convolution;
    use montgomery_modint::{Mod754974721, Mod998244353, MontgomeryModint};

    #[test]
    fn convolution_test() {
        type Modint = MontgomeryModint<Mod998244353>;
        let a = vec![Modint::new(1), Modint::new(2), Modint::new(3), Modint::new(4)];
        let b = vec![Modint::new(1), Modint::new(2), Modint::new(4), Modint::new(8)];
        let c = convolution(a, b);
        assert_eq!(
            c,
            vec![Modint::new(1), Modint::new(4), Modint::new(11), Modint::new(26), Modint::new(36), Modint::new(40), Modint::new(32)]
        );
    }

    #[test]
    fn convolution_test2() {
        type Modint = MontgomeryModint<Mod754974721>;
        let a = vec![Modint::new(1), Modint::new(2), Modint::new(3), Modint::new(4)];
        let b = vec![Modint::new(1), Modint::new(2), Modint::new(4), Modint::new(8)];
        let c = convolution(a, b);
        assert_eq!(
            c,
            vec![Modint::new(1), Modint::new(4), Modint::new(11), Modint::new(26), Modint::new(36), Modint::new(40), Modint::new(32)]
        );
    }
}
