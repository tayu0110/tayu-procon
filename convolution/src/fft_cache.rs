use super::common::{complex_prim_root, complex_prim_root_f32};
use complex::Complex;
use modint::{Modulo, MontgomeryModint, MontgomeryMultiplication};
use numeric::Integer;

pub struct FftCache<T>
where
    T: Clone + Copy,
{
    prim_roots: Vec<T>,
    prim_roots_inv: Vec<T>,
}

impl<T> FftCache<T>
where
    T: Clone + Copy,
{
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
        let prim_roots = (0..=size)
            .map(|i| complex_prim_root(1 << i))
            .collect::<Vec<_>>();
        let prim_roots_inv = prim_roots.iter().cloned().map(|c| c.conjugate()).collect();

        Self {
            prim_roots,
            prim_roots_inv,
        }
    }
}

impl FftCache<Complex<f32>> {
    #[inline]
    pub fn new(size: usize) -> Self {
        let prim_roots = (0..=size)
            .map(|i| complex_prim_root_f32(1 << i))
            .collect::<Vec<_>>();
        let prim_roots_inv = prim_roots.iter().cloned().map(|c| c.conjugate()).collect();

        Self {
            prim_roots,
            prim_roots_inv,
        }
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> FftCache<MontgomeryModint<M, T>> {
    #[inline]
    pub fn new(size: usize) -> Self {
        debug_assert!(size <= (M::modulo() - T::one()).trailing_zeros() as usize);

        let size = std::cmp::max(size, 3);

        let mut prim_roots = vec![MontgomeryModint::zero(); size + 1];
        prim_roots[size] = MontgomeryModint::<M, T>::nth_root(T::one() << size);
        let mut prim_roots_inv = vec![MontgomeryModint::zero(); size + 1];
        prim_roots_inv[size] = prim_roots[size].inv();
        for i in (0..size).rev() {
            prim_roots[i] = prim_roots[i + 1] * prim_roots[i + 1];
            prim_roots_inv[i] = prim_roots_inv[i + 1] * prim_roots_inv[i + 1];
        }

        Self {
            prim_roots,
            prim_roots_inv,
        }
    }
}
