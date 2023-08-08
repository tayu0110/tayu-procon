use montgomery_modint::{Modulo, MontgomeryModint};

type Modint<M> = MontgomeryModint<M>;

// AtCoder-Library like FftCache
// reference: https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
pub struct FftCache<M: Modulo> {
    pub root: [Modint<M>; 35],
    pub iroot: [Modint<M>; 35],
    pub rate2: [Modint<M>; 35],
    pub irate2: [Modint<M>; 35],
    pub rate3: [Modint<M>; 35],
    pub irate3: [Modint<M>; 35],
}

impl<M: Modulo> FftCache<M> {
    const RANK2: usize = (M::N - 1).trailing_zeros() as usize;
    pub const fn new() -> Self {
        let mut root = [Modint::one(); 35];
        let mut iroot = [Modint::one(); 35];
        let mut rate2 = [Modint::one(); 35];
        let mut irate2 = [Modint::one(); 35];
        let mut rate3 = [Modint::one(); 35];
        let mut irate3 = [Modint::one(); 35];

        root[Self::RANK2] = Modint::<M>::nth_root(1 << Self::RANK2);
        iroot[Self::RANK2] = root[Self::RANK2].inv();
        let mut i = Self::RANK2;
        while i > 0 {
            i -= 1;
            root[i] = root[i + 1].mul_const(root[i + 1]);
            iroot[i] = iroot[i + 1].mul_const(iroot[i + 1]);
        }

        let mut prod = Modint::one();
        let mut iprod = Modint::one();
        let mut i = 0;
        while i < Self::RANK2.saturating_sub(1) {
            rate2[i] = root[i + 2].mul_const(prod);
            irate2[i] = iroot[i + 2].mul_const(iprod);
            prod = prod.mul_const(iroot[i + 2]);
            iprod = iprod.mul_const(root[i + 2]);
            i += 1;
        }

        let mut prod = Modint::one();
        let mut iprod = Modint::one();
        let mut i = 0;
        while i < Self::RANK2.saturating_sub(2) {
            rate3[i] = root[i + 3].mul_const(prod);
            irate3[i] = iroot[i + 3].mul_const(iprod);
            prod = prod.mul_const(iroot[i + 3]);
            iprod = iprod.mul_const(root[i + 3]);
            i += 1;
        }

        Self { root, iroot, rate2, irate2, rate3, irate3 }
    }
}
