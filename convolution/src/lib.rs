#![allow(clippy::ptr_arg)]

#[cfg(feature = "arbitrary-modulo-convolution")]
mod arbitrary_modulo_convolution;
#[cfg(feature = "large-convolution")]
mod large_convolution;

#[cfg(feature = "arbitrary-modulo-convolution")]
pub use arbitrary_modulo_convolution::*;
#[cfg(feature = "large-convolution")]
pub use large_convolution::*;
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use number_theoretic_transform::NumberTheoreticTransform;
use std::mem::transmute;

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

#[inline]
pub fn hadamard<M: Modulo>(a: &mut Vec<Modint<M>>, b: &[Modint<M>]) {
    if a.len() < 8 {
        a.iter_mut().zip(b).for_each(|(a, &b)| *a *= b);
    } else {
        unsafe {
            a.chunks_exact_mut(8)
                .zip(b.chunks_exact(8))
                .for_each(|(v, w)| {
                    (Modintx8::load(v.as_ptr()) * Modintx8::load(w.as_ptr())).store(v.as_mut_ptr())
                })
        }
    }
}

#[inline]
pub fn hadamard_u32<M: Modulo>(a: &mut Vec<u32>, b: &[u32]) {
    let a = unsafe { transmute(a) };
    let b = unsafe { transmute(b) };
    hadamard::<M>(a, b);
}

pub fn convolution<M: Modulo>(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();

    a.resize(n, 0);
    b.resize(n, 0);

    <[u32] as NumberTheoreticTransform<M>>::ntt(&mut a);
    <[u32] as NumberTheoreticTransform<M>>::ntt(&mut b);

    hadamard_u32::<M>(&mut a, &b);

    <[u32] as NumberTheoreticTransform<M>>::intt(&mut a);
    a.resize(deg, 0);
    a
}
