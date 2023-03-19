use montgomery_modint::{Modulo, MontgomeryModint};

pub struct FftCache<T: Clone + Copy> {
    // prim_roots[i]^(2^i) == 1
    prim_roots: Vec<T>,
    // prim_roots_inv[i] == prim_roots_inv[i].conjugate
    prim_roots_inv: Vec<T>,
    // twiddle_factors[i]^(deg/i) == 1
    twiddle_factors: Vec<T>,
    // twiddle_factors_inv[i] == twiddle_factors[i].conjugate
    twiddle_factors_inv: Vec<T>,
}

impl<T: Clone + Copy> FftCache<T> {
    #[inline]
    pub fn prim_root(&self, nth: usize) -> T { self.prim_roots[nth] }

    #[inline]
    pub fn prim_root_inv(&self, nth: usize) -> T { self.prim_roots_inv[nth] }

    #[inline]
    pub fn prim_roots(&self) -> &Vec<T> { &self.prim_roots }

    #[inline]
    pub fn prim_roots_inv(&self) -> &Vec<T> { &self.prim_roots_inv }

    #[inline]
    pub fn twiddle_factors(&self) -> &Vec<T> { &self.twiddle_factors }

    #[inline]
    pub fn twiddle_factors_inv(&self) -> &Vec<T> { &self.twiddle_factors_inv }
}

impl<M: Modulo> FftCache<MontgomeryModint<M>> {
    #[inline]
    pub fn new(size: usize) -> Self {
        debug_assert!(size <= (M::MOD - 1).trailing_zeros() as usize);

        let mut prim_roots = vec![MontgomeryModint::zero(); size + 1];
        prim_roots[size] = MontgomeryModint::<M>::nth_root(1 << size);
        let mut prim_roots_inv = vec![MontgomeryModint::zero(); size + 1];
        prim_roots_inv[size] = prim_roots[size].inv();
        for i in (0..size).rev() {
            prim_roots[i] = prim_roots[i + 1] * prim_roots[i + 1];
            prim_roots_inv[i] = prim_roots_inv[i + 1] * prim_roots_inv[i + 1];
        }

        let mut twiddle_factors = vec![MontgomeryModint::<M>::one(); (1 << size) + 1];
        twiddle_factors[1] = prim_roots[size];
        let mut twiddle_factors_inv = vec![MontgomeryModint::<M>::one(); (1 << size) + 1];
        twiddle_factors_inv[1] = prim_roots_inv[size];

        for i in 1..(1 << size) {
            twiddle_factors[i + 1] = twiddle_factors[i] * prim_roots[size];
            twiddle_factors_inv[i + 1] = twiddle_factors_inv[i] * prim_roots_inv[size];
        }

        Self {
            prim_roots,
            prim_roots_inv,
            twiddle_factors,
            twiddle_factors_inv,
        }
    }
}
