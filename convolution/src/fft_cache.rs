use super::common::{
    complex_prim_root,
    complex_prim_root_f32
};
use complex::Complex;
use modint::{
    Mint, Modulo
};

pub struct FftCache<T>
where T: Clone + Copy
{
    prim_roots: Vec<T>,
    prim_roots_inv: Vec<T>
}

impl<T> FftCache<T>
where T: Clone + Copy {
    #[inline]
    pub fn prim_root(&self, nth: usize) -> T {
        self.prim_roots[nth]
    }

    #[inline]
    pub fn prim_root_inv(&self, nth: usize) -> T {
        self.prim_roots_inv[nth]
    }
}

impl FftCache<Complex> {
    #[inline]
    pub fn new(size: usize) -> Self {
        let prim_roots = (0..=size).map(|i| complex_prim_root(1 << i)).collect::<Vec<_>>();
        let prim_roots_inv = prim_roots.iter().cloned().map(|c| c.conjugate()).collect();

        Self { prim_roots, prim_roots_inv }
    }
}

impl FftCache<Complex<f32>> {
    #[inline]
    pub fn new(size: usize) -> Self {
        let prim_roots = (0..=size).map(|i| complex_prim_root_f32(1 << i)).collect::<Vec<_>>();
        let prim_roots_inv = prim_roots.iter().cloned().map(|c| c.conjugate()).collect();

        Self { prim_roots, prim_roots_inv }
    }
}

impl<M> FftCache<Mint<M>>
where M: Modulo {
    #[inline]
    pub fn new(size: usize) -> Self {
        debug_assert!(size <= (M::modulo()-1).trailing_zeros() as usize);

        let size = std::cmp::max(size, 2);

        let mut prim_roots = vec![Mint::zero(); size+1];
        prim_roots[size] = Mint::<M>::nth_root(1 << size);
        let mut prim_roots_inv = vec![Mint::zero(); size+1];
        prim_roots_inv[size] = Mint::<M>::nth_root(-(1 << size));
        for i in (0..size).rev() {
            prim_roots[i] = prim_roots[i+1] * prim_roots[i+1];
            prim_roots_inv[i] = prim_roots_inv[i+1] * prim_roots_inv[i+1];
        }

        Self { prim_roots, prim_roots_inv }
    }
}
