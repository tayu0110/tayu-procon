use super::modint::{
    Mint, Modulo
};
use std::convert::From;

#[derive(Clone)]
pub struct Matrix<T: Modulo> {
    row: usize,
    column: usize,
    matrix: Box<[Mint<T>]>
}

#[allow(dead_code)]
impl<T: Modulo> Matrix<T> {
    #[inline]
    pub fn new(row: usize, column: usize) -> Self {
        debug_assert!(row > 0 && column > 0);
        Matrix {
            row,
            column,
            matrix: (vec![Default::default(); row * column]).into_boxed_slice()
        }
    }
    
    #[inline]
    const fn row(&self) -> usize {
        self.row
    }
    
    #[inline]
    const fn column(&self) -> usize {
        self.column
    }
    
    #[inline]
    fn set(&mut self, row: usize, column: usize, val: Mint<T>) {
        debug_assert!(row < self.row() && column < self.column());
        let c = self.column();

        self.matrix[c*row+column] = val;
    }
    
    #[inline]
    const fn get(&self, row: usize, column: usize) -> Mint<T> {
        debug_assert!(row < self.row() && column < self.column());

        self.matrix[row*self.column() + column]
    }
    
    #[inline]
    fn id(size: usize) -> Self {
        let mut matrix = vec![Mint::<T>::zero(); size * size];
        matrix
            .iter_mut()
            .enumerate()
            .filter(|(i, _)| i % (size + 1) == 0)
            .for_each(|(_, v)| *v = Mint::one());
        Self {
            row: size,
            column: size,
            matrix: matrix.into_boxed_slice()
        }
    }

    #[inline]
    fn add(&self, rhs: &Self) -> Self {
        debug_assert!(self.row() == rhs.row() && self.column() == rhs.column());
        
        let matrix = self.matrix
            .iter()
            .zip(rhs.matrix.iter())
            .map(|(x, y)| *x + *y)
            .collect();
        Self {
            row: self.row(),
            column: self.column(),
            matrix
        }
    }

    #[inline]
    fn sub(&self, rhs: &Self) -> Self {
        debug_assert!(self.row() == rhs.row() && self.column() == rhs.column());

        let matrix = self.matrix
            .iter()
            .zip(rhs.matrix.iter())
            .map(|(x, y)| *x - *y)
            .collect();
        Self {
            row: self.row(),
            column: self.column(),
            matrix
        }
    }

    #[inline]
    fn mul(&self, rhs: &Self) -> Self {
        unsafe { self.mul_sub(rhs) }
    }

    #[target_feature(enable = "avx2")]
    unsafe fn mul_sub(&self, rhs: &Self) -> Self {
        let (lrow, lcolumn, rrow, rcolumn) = (self.row(), self.column(), rhs.row(), rhs.column());

        debug_assert!(lcolumn == rrow);
        
        let mut matrix = (vec![Default::default(); lrow*rcolumn]).into_boxed_slice();
        for (s, t) in matrix
                                                    .chunks_exact_mut(rcolumn)
                                                    .zip(self.matrix.chunks_exact(lcolumn)) {
            for (v, u) in t
                                                .iter()
                                                .zip(rhs.matrix.chunks_exact(rcolumn)) {
                for (x, y) in s
                                                    .iter_mut()
                                                    .zip(u.iter()) {
                    *x += *v * *y;
                }
            }
        }
        Self {
            row: lrow,
            column: rcolumn,
            matrix
        }
    }

    fn pow(&self, mut n: usize) -> Self {
        debug_assert!(self.row() == self.column());

        let (mut ret, mut now) = (Self::id(self.row()), self.clone());
        while n > 0 {
            if n & 1 == 1 {
                ret = ret.mul(&now);
            }
            now = now.mul(&now);
            n >>= 1;
        }
        ret
    }
}

impl<T: Modulo> From<Vec<Vec<Mint<T>>>> for Matrix<T> {
    fn from(from: Vec<Vec<Mint<T>>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter()
                        .flatten()
                        .collect()
        }
    }
}

impl<T: Modulo> From<Vec<Vec<i64>>> for Matrix<T> {
    fn from(from: Vec<Vec<i64>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter()
                        .flatten()
                        .map(|v| Mint::<T>::new(v))
                        .collect()
        }
    }
}

impl<T: Modulo> From<Vec<Vec<i32>>> for Matrix<T> {
    fn from(from: Vec<Vec<i32>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter()
                        .flatten()
                        .map(|v| Mint::<T>::new(v as i64))
                        .collect()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::matrix::Matrix;
    use super::super::modint::{
        Mint, Mod998244353
    };

    #[test]
    fn matrix_test() {
        let matrix_i64: Vec<Vec<i64>> =
            vec![
                vec![3, 2, 1],
                vec![4, 2, 2],
                vec![5, 1, 3],
            ];
        let matrix_i32: Vec<Vec<i32>> =
            vec![
                vec![2, 5, 4],
                vec![5, 1, 2],
                vec![4, 2, 3],
            ];
        let flattened_matrix_i64: Vec<Mint<Mod998244353>> =
            vec![
                Mint::raw(3), Mint::raw(2), Mint::raw(1),
                Mint::raw(4), Mint::raw(2), Mint::raw(2),
                Mint::raw(5), Mint::raw(1), Mint::raw(3),
            ];
        let flattened_matrix_i32: Vec<Mint<Mod998244353>> =
            vec![
                Mint::raw(2), Mint::raw(5), Mint::raw(4),
                Mint::raw(5), Mint::raw(1), Mint::raw(2),
                Mint::raw(4), Mint::raw(2), Mint::raw(3)
            ];

        let a = Matrix::<Mod998244353>::from(matrix_i64);
        let b = Matrix::<Mod998244353>::from(matrix_i32);
        
        assert_eq!(Matrix::<Mod998244353>::new(4, 3).matrix, vec![Mint::zero(); 12].into_boxed_slice());
        assert_eq!(
            Matrix::<Mod998244353>::id(3).matrix,
            vec![
                Mint::raw(1), Mint::raw(0), Mint::raw(0),
                Mint::raw(0), Mint::raw(1), Mint::raw(0),
                Mint::raw(0), Mint::raw(0), Mint::raw(1)
            ].into_boxed_slice());
        assert_eq!(a.matrix, flattened_matrix_i64.clone().into_boxed_slice());
        assert_eq!(b.matrix, flattened_matrix_i32.clone().into_boxed_slice());

        //     |3 2 1|       |2 5 4|
        // a = |4 2 2| , b = |5 1 2|
        //     |5 1 3|       |4 2 3|
        assert_eq!(
            a.add(&b).matrix,
            vec![
                Mint::raw(5), Mint::raw(7), Mint::raw(5),
                Mint::raw(9), Mint::raw(3), Mint::raw(4),
                Mint::raw(9), Mint::raw(3), Mint::raw(6)
            ].into_boxed_slice());
        assert_eq!(
            a.sub(&b).matrix,
            vec![
                Mint::raw(1), Mint::raw(998244350), Mint::raw(998244350),
                Mint::raw(998244352), Mint::raw(1), Mint::raw(0),
                Mint::raw(1), Mint::raw(998244352), Mint::raw(0)
            ].into_boxed_slice());
        assert_eq!(
            a.mul(&b).matrix,
            vec![
                Mint::raw(20), Mint::raw(19), Mint::raw(19),
                Mint::raw(26), Mint::raw(26), Mint::raw(26),
                Mint::raw(27), Mint::raw(32), Mint::raw(31)
            ].into_boxed_slice());
        assert_eq!(
            a.pow(324355).matrix,
            vec![
                Mint::raw(957495479), Mint::raw(800953849), Mint::raw(608722515),
                Mint::raw(419297532), Mint::raw(552242599), Mint::raw(607036125),
                Mint::raw(417611142), Mint::raw(618274426), Mint::raw(347086574)
            ].into_boxed_slice());
    }
}