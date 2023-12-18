use std::mem::transmute;

use super::Matrix;
use montgomery_modint::{MontgomeryModint, MontgomeryModintx8};
use static_modint::{Modulo, StaticModint};

impl<M: Modulo> From<Vec<Vec<u32>>> for Matrix<StaticModint<M>> {
    fn from(value: Vec<Vec<u32>>) -> Self {
        let row = value.len() as u32;
        let col = value.first().map_or(0, |v| v.len()) as u32;
        let data = value
            .into_iter()
            .flatten()
            .map(|v| StaticModint::raw(v))
            .collect();
        Self { row, col, data }
    }
}

impl<M: Modulo> From<Vec<Vec<u32>>> for Matrix<MontgomeryModint<M>> {
    fn from(value: Vec<Vec<u32>>) -> Self {
        let row = value.len() as u32;
        let col = value.first().map_or(0, |v| v.len()) as u32;
        let mut data = value.into_iter().flatten().collect::<Vec<_>>();
        data.chunks_exact_mut(8).for_each(|v| unsafe {
            let w = MontgomeryModintx8::<M>::convert_from_u32slice(v);
            w.store(v.as_mut_ptr() as _);
        });
        let tail = data.len() - (data.len() & 0b111);
        data[tail..]
            .iter_mut()
            .for_each(|v| *v = MontgomeryModint::<M>::new(*v).rawval());
        Self { row, col, data: unsafe { transmute(data) } }
    }
}

impl<M: Modulo> From<Vec<Vec<StaticModint<M>>>> for Matrix<StaticModint<M>> {
    fn from(value: Vec<Vec<StaticModint<M>>>) -> Self {
        Self::from_vec(value)
    }
}

impl<M: Modulo> From<Vec<Vec<MontgomeryModint<M>>>> for Matrix<MontgomeryModint<M>> {
    fn from(value: Vec<Vec<MontgomeryModint<M>>>) -> Self {
        Self::from_vec(value)
    }
}
