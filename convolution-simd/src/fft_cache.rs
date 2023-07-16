use montgomery_modint::{Modulo, MontgomeryModint};

type Modint<M> = MontgomeryModint<M>;

// AtCoder-Library like FftCache
// reference: https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
pub struct FftCache<M: Modulo> {
    pub root: Vec<Modint<M>>,
    pub iroot: Vec<Modint<M>>,
    pub rate2: Vec<Modint<M>>,
    pub irate2: Vec<Modint<M>>,
    pub rate3: Vec<Modint<M>>,
    pub irate3: Vec<Modint<M>>,
}

impl<M: Modulo> FftCache<M> {
    const RANK2: usize = (M::MOD - 1).trailing_zeros() as usize;
    pub fn new() -> Self {
        // Create all arrays one size larger than required.
        // This removes the out-of-array reference check within the NTT main loop.
        let mut root = vec![Modint::one(); Self::RANK2 + 2];
        let mut iroot = vec![Modint::one(); Self::RANK2 + 2];
        let mut rate2 = vec![Modint::one(); Self::RANK2];
        let mut irate2 = vec![Modint::one(); Self::RANK2];
        let mut rate3 = vec![Modint::one(); Self::RANK2.saturating_sub(1)];
        let mut irate3 = vec![Modint::one(); Self::RANK2.saturating_sub(1)];

        root[Self::RANK2] = Modint::<M>::nth_root(1 << Self::RANK2);
        iroot[Self::RANK2] = root[Self::RANK2].inv();
        for i in (0..Self::RANK2).rev() {
            root[i] = root[i + 1] * root[i + 1];
            iroot[i] = iroot[i + 1] * iroot[i + 1];
        }

        let mut prod = Modint::one();
        let mut iprod = Modint::one();
        for i in 0..Self::RANK2.saturating_sub(1) {
            rate2[i] = root[i + 2] * prod;
            irate2[i] = iroot[i + 2] * iprod;
            prod *= iroot[i + 2];
            iprod *= root[i + 2];
        }

        let mut prod = Modint::one();
        let mut iprod = Modint::one();
        for i in 0..Self::RANK2.saturating_sub(2) {
            rate3[i] = root[i + 3] * prod;
            irate3[i] = iroot[i + 3] * iprod;
            prod *= iroot[i + 3];
            iprod *= root[i + 3];
        }

        Self { root, iroot, rate2, irate2, rate3, irate3 }
    }

    #[inline]
    pub fn gen_rate(&self, log: usize) -> Vec<Modint<M>> {
        if log == 2 {
            return self.rate2.clone();
        } else if log == 3 {
            return self.rate3.clone();
        }
        let mut rate = vec![Modint::one(); Self::RANK2.saturating_sub(log - 1)];
        let mut prod = Modint::one();
        for i in 0..Self::RANK2.saturating_sub(log - 1) {
            rate[i] = self.root[i + log] * prod;
            prod *= self.iroot[i + log];
        }
        rate
    }

    #[inline]
    pub fn gen_irate(&self, log: usize) -> Vec<Modint<M>> {
        if log == 2 {
            return self.irate2.clone();
        }
        if log == 3 {
            return self.irate3.clone();
        }
        let mut irate = vec![Modint::one(); Self::RANK2.saturating_sub(log - 1)];
        let mut iprod = Modint::one();
        for i in 0..Self::RANK2.saturating_sub(log - 1) {
            irate[i] = self.iroot[i + log] * iprod;
            iprod *= self.root[i + log];
        }
        irate
    }
}
