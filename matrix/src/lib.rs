mod affine_transform;
mod element;

pub use crate::affine_transform::*;
use crate::element::MatrixElement;
use std::{convert::From, fmt::Debug};

#[derive(Debug, Clone)]
pub struct Matrix<T: MatrixElement> {
    row: usize,
    column: usize,
    matrix: Vec<T>,
}

impl<T: MatrixElement + Debug> Matrix<T> {
    #[inline]
    pub fn new(row: usize, column: usize) -> Self {
        debug_assert!(row > 0 && column > 0);
        Matrix { row, column, matrix: vec![T::zero(); row * column] }
    }

    #[inline]
    pub fn row(&self) -> usize { self.row }

    #[inline]
    pub fn column(&self) -> usize { self.column }

    #[inline]
    pub fn set(&mut self, row: usize, column: usize, val: T) {
        debug_assert!(row < self.row() && column < self.column());
        let c = self.column();
        self.matrix[c * row + column] = val;
    }

    #[inline]
    pub fn get(&self, row: usize, column: usize) -> T {
        debug_assert!(row < self.row() && column < self.column());
        unsafe { *self.matrix.get_unchecked(row * self.column() + column) }
    }

    #[inline]
    pub fn id(size: usize) -> Self {
        let mut matrix = vec![T::zero(); size * size];
        matrix.iter_mut().enumerate().filter(|(i, _)| i % (size + 1) == 0).for_each(|(_, v)| *v = T::one());
        Self { row: size, column: size, matrix }
    }

    #[inline]
    pub fn add(&self, rhs: &Self) -> Self {
        debug_assert!(self.row() == rhs.row() && self.column() == rhs.column());
        let matrix = self.matrix.iter().zip(rhs.matrix.iter()).map(|(x, y)| *x + *y).collect();
        Self { row: self.row(), column: self.column(), matrix }
    }

    #[inline]
    pub fn sub(&self, rhs: &Self) -> Self {
        debug_assert!(self.row() == rhs.row() && self.column() == rhs.column());
        let matrix = self.matrix.iter().zip(rhs.matrix.iter()).map(|(x, y)| *x - *y).collect();
        Self { row: self.row(), column: self.column(), matrix }
    }

    #[inline]
    pub fn mul(&self, rhs: &Self) -> Self {
        let (lrow, lcolumn, rrow, rcolumn) = (self.row(), self.column(), rhs.row(), rhs.column());
        debug_assert!(lcolumn == rrow);
        let mut matrix = vec![T::zero(); lrow * rcolumn];
        for (s, t) in matrix.chunks_exact_mut(rcolumn).zip(self.matrix.chunks_exact(lcolumn)) {
            for (v, u) in t.iter().zip(rhs.matrix.chunks_exact(rcolumn)) {
                for (x, y) in s.iter_mut().zip(u.iter()) {
                    *x = *x + *v * *y;
                }
            }
        }
        Self { row: lrow, column: rcolumn, matrix }
    }

    pub fn pow(&self, mut n: usize) -> Self {
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

    pub fn determinant(&self) -> T {
        let mut res = T::one();

        let mut matrix = self.matrix.clone();
        for i in 0..self.row() {
            let irow = i * self.column();
            if matrix[irow + i].is_zero() {
                for j in i + 1..self.row() {
                    let jrow = j * self.column();
                    if !matrix[jrow + i].is_zero() {
                        for k in 0..self.column() {
                            matrix[irow + k] = matrix[irow + k] + matrix[jrow + k];
                        }
                        break;
                    }

                    if j == self.row() - 1 {
                        return T::zero();
                    }
                }
            }

            res = res * matrix[irow + i];
            for j in i + 1..self.row() {
                let jrow = j * self.column();
                let t = matrix[jrow + i] / matrix[irow + i];
                for k in i..self.column() {
                    matrix[jrow + k] = matrix[jrow + k] - t * matrix[irow + k];
                }
            }
        }

        res
    }

    pub fn rank(&self) -> usize {
        let mut matrix = self.matrix.clone();
        let mut next_row = 0;
        for i in 0..self.column() {
            if matrix[next_row * self.column() + i].is_zero() {
                for j in next_row + 1..self.row() {
                    if !matrix[j * self.column() + i].is_zero() {
                        for k in 0..self.column() {
                            matrix.swap(next_row * self.column() + k, j * self.column() + k);
                        }

                        break;
                    }
                }
            }

            if matrix[next_row * self.column() + i].is_zero() {
                continue;
            }

            for j in 0..self.row() {
                if j == next_row {
                    continue;
                }
                let jrow = j * self.column();
                let t = matrix[jrow + i] / matrix[next_row * self.column() + i];
                for k in i..self.column() {
                    matrix[jrow + k] = matrix[jrow + k] - t * matrix[next_row * self.column() + k];
                }
            }

            next_row += 1;
        }

        next_row
    }
}

impl<T: MatrixElement + From<U>, U> From<Vec<Vec<U>>> for Matrix<T> {
    fn from(from: Vec<Vec<U>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter().flatten().map(|v| T::from(v)).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Matrix;
    use modint::{Mod998244353, Modint};

    #[test]
    fn matrix_test() {
        let matrix_i64: Vec<Vec<i64>> = vec![vec![3, 2, 1], vec![4, 2, 2], vec![5, 1, 3]];
        let matrix_i32: Vec<Vec<i32>> = vec![vec![2, 5, 4], vec![5, 1, 2], vec![4, 2, 3]];
        let flattened_matrix_i64: Vec<Modint<Mod998244353>> = vec![3.into(), 2.into(), 1.into(), 4.into(), 2.into(), 2.into(), 5.into(), 1.into(), 3.into()];
        let flattened_matrix_i32: Vec<Modint<Mod998244353>> = vec![2.into(), 5.into(), 4.into(), 5.into(), 1.into(), 2.into(), 4.into(), 2.into(), 3.into()];

        let a = Matrix::<Modint<Mod998244353>>::from(matrix_i64);
        let b = Matrix::<Modint<Mod998244353>>::from(matrix_i32);

        assert_eq!(Matrix::<Modint<Mod998244353>>::new(4, 3).matrix, vec![Modint::zero(); 12]);
        assert_eq!(
            Matrix::<Modint<Mod998244353>>::id(3).matrix,
            vec![1.into(), 0.into(), 0.into(), 0.into(), 1.into(), 0.into(), 0.into(), 0.into(), 1.into()]
        );
        assert_eq!(a.matrix, flattened_matrix_i64.clone());
        assert_eq!(b.matrix, flattened_matrix_i32.clone());

        //     |3 2 1|       |2 5 4|
        // a = |4 2 2| , b = |5 1 2|
        //     |5 1 3|       |4 2 3|
        assert_eq!(a.add(&b).matrix, vec![5.into(), 7.into(), 5.into(), 9.into(), 3.into(), 4.into(), 9.into(), 3.into(), 6.into()]);
        assert_eq!(
            a.sub(&b).matrix,
            vec![1.into(), 998244350.into(), 998244350.into(), 998244352.into(), 1.into(), 0.into(), 1.into(), 998244352.into(), 0.into(),]
        );
        assert_eq!(
            a.mul(&b).matrix,
            vec![20.into(), 19.into(), 19.into(), 26.into(), 26.into(), 26.into(), 27.into(), 32.into(), 31.into()]
        );
        assert_eq!(
            a.pow(324355).matrix,
            vec![
                957495479.into(),
                800953849.into(),
                608722515.into(),
                419297532.into(),
                552242599.into(),
                607036125.into(),
                417611142.into(),
                618274426.into(),
                347086574.into()
            ]
        );
    }
}
