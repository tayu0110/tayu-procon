use modint::{Modint, Modulo};
use numeric::{One, Zero};
use std::convert::From;
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone)]
pub struct Matrix<T: Modulo> {
    row: usize,
    column: usize,
    matrix: Vec<Modint<T>>,
}

impl<T: Modulo> Matrix<T> {
    #[inline]
    pub fn new(row: usize, column: usize) -> Self {
        debug_assert!(row > 0 && column > 0);
        Matrix { row, column, matrix: vec![Modint::zero(); row * column] }
    }

    #[inline]
    pub fn row(&self) -> usize { self.row }

    #[inline]
    pub fn column(&self) -> usize { self.column }

    #[inline]
    pub fn set(&mut self, row: usize, column: usize, val: Modint<T>) {
        debug_assert!(row < self.row() && column < self.column());
        let c = self.column();

        self.matrix[c * row + column] = val;
    }

    #[inline]
    pub fn get(&self, row: usize, column: usize) -> Modint<T> {
        debug_assert!(row < self.row() && column < self.column());

        unsafe { *self.matrix.get_unchecked(row * self.column() + column) }
    }

    #[inline]
    pub fn id(size: usize) -> Self {
        let mut matrix = vec![Modint::<T>::zero(); size * size];
        matrix.iter_mut().enumerate().filter(|(i, _)| i % (size + 1) == 0).for_each(|(_, v)| *v = Modint::one());
        Self { row: size, column: size, matrix: matrix }
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
    pub fn mul(&self, rhs: &Self) -> Self { unsafe { self.mul_sub(rhs) } }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2")]
    unsafe fn mul_sub(&self, rhs: &Self) -> Self {
        let (lrow, lcolumn, rrow, rcolumn) = (self.row(), self.column(), rhs.row(), rhs.column());

        debug_assert!(lcolumn == rrow);

        let mut matrix = vec![Modint::zero(); lrow * rcolumn];
        for (s, t) in matrix.chunks_exact_mut(rcolumn).zip(self.matrix.chunks_exact(lcolumn)) {
            for (v, u) in t.iter().zip(rhs.matrix.chunks_exact(rcolumn)) {
                for (x, y) in s.iter_mut().zip(u.iter()) {
                    let res = x.val() + (v.val() as u64 * y.val() as u64 % T::MOD as u64) as u32;
                    *x = if res < T::MOD { Modint::raw(res) } else { Modint::raw(res - T::MOD) };
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
}

impl<T: Modulo> From<Vec<Vec<Modint<T>>>> for Matrix<T> {
    fn from(from: Vec<Vec<Modint<T>>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter().flatten().collect(),
        }
    }
}

impl<T: Modulo> From<Vec<Vec<i64>>> for Matrix<T> {
    fn from(from: Vec<Vec<i64>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter().flatten().map(|v| Modint::<T>::new_signed(v)).collect(),
        }
    }
}

impl<T: Modulo> From<Vec<Vec<i32>>> for Matrix<T> {
    fn from(from: Vec<Vec<i32>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter().flatten().map(|v| Modint::<T>::new_signed(v as i64)).collect(),
        }
    }
}

impl<T: Modulo> From<Vec<Vec<u32>>> for Matrix<T> {
    fn from(from: Vec<Vec<u32>>) -> Self {
        Self {
            row: from.len(),
            column: from[0].len(),
            matrix: from.into_iter().flatten().map(|v| Modint::<T>::new(v as u64)).collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AffineTransformation<T: One + Zero + Clone + Copy + Add<T, Output = T> + Sub + Mul<T, Output = T> + Div + Neg> {
    matrix: [T; 9],
}

impl<T: One + Zero + Clone + Copy + Add<T, Output = T> + Sub + Mul<T, Output = T> + Div + Neg<Output = T>> AffineTransformation<T> {
    #[inline]
    pub fn new() -> Self {
        let mut matrix = [T::zero(); 9];
        matrix[0] = T::one();
        matrix[4] = T::one();
        matrix[8] = T::one();
        Self { matrix }
    }

    #[inline]
    // | 1 0 x | | a b c |   | a+gx b+hx c+ix |
    // | 0 1 y | | d e f | = | d+gy e+hy f+iy |
    // | 0 0 1 | | g h i |   |   g    h    i  |
    pub fn translation(&self, dx: T, dy: T) -> Self {
        let mut matrix = self.matrix.clone();
        (0..3).for_each(|i| matrix[i] = matrix[i] + matrix[i + 6] * dx);
        (3..6).for_each(|i| matrix[i] = matrix[i] + matrix[i + 3] * dy);
        Self { matrix }
    }

    #[inline]
    // if x { x = -1 } else { x = 1 }
    // if y { y = -1 } else { y = 1 }
    // | x 0 0 | | a b c |   | ax bx cx |
    // | 0 y 0 | | d e f | = | dy ey fy |
    // | 0 0 1 | | g h i |   | g  h  i  |
    pub fn reflection(&self, x: bool, y: bool) -> Self {
        let mut matrix = self.matrix.clone();
        if x {
            (0..3).for_each(|i| matrix[i] = -matrix[i]);
        }
        if y {
            (3..6).for_each(|i| matrix[i] = -matrix[i]);
        }
        Self { matrix }
    }

    #[inline]
    // | x 0 0 | | a b c |   | ax bx cx |
    // | 0 y 0 | | d e f | = | dy ey fy |
    // | 0 0 1 | | g h i |   | g  h  i  |
    pub fn scale(&self, x: T, y: T) -> Self {
        let mut matrix = self.matrix.clone();
        (0..3).for_each(|i| {
            matrix[i] = matrix[i] * x;
            matrix[i + 3] = matrix[i + 3] * y;
        });
        Self { matrix }
    }

    #[inline]
    // | cos(-PI/2) -sin(-PI/2) 0 | | a b c |   |  0 1 0 | | a b c |   |  d  e  f |
    // | sin(-PI/2)  cos(-PI/2) 0 | | d e f | = | -1 0 0 | | d e f | = | -a -b -c |
    // | 0           0          1 | | g h i |   |  0 0 1 | | g h i |   |  g  h  i |
    pub fn rotate_clockwise(&self) -> Self {
        let mut matrix = self.matrix.clone();
        (0..3).for_each(|i| {
            matrix.swap(i, i + 3);
            matrix[i + 3] = -matrix[i + 3];
        });
        Self { matrix }
    }

    #[inline]
    // | cos(PI/2) -sin(PI/2) 0 | | a b c |   | 0 -1 0 | | a b c |   | -d -e -f |
    // | sin(PI/2)  cos(PI/2) 0 | | d e f | = | 1  0 0 | | d e f | = |  a  b  c |
    // | 0          0         1 | | g h i |   | 0  0 1 | | g h i |   |  g  h  i |
    pub fn rotate_counterclockwise(&self) -> Self {
        let mut matrix = self.matrix.clone();
        (0..3).for_each(|i| {
            matrix.swap(i, i + 3);
            matrix[i] = -matrix[i];
        });
        Self { matrix }
    }

    #[inline]
    pub fn transform(&self, x: T, y: T) -> (T, T) { (self.matrix[0] * x + self.matrix[1] * y + self.matrix[2], self.matrix[3] * x + self.matrix[4] * y + self.matrix[5]) }
}

#[cfg(test)]
mod tests {
    use super::Matrix;
    use modint::{Mod998244353, Modint};

    #[test]
    fn matrix_test() {
        let matrix_i64: Vec<Vec<i64>> = vec![vec![3, 2, 1], vec![4, 2, 2], vec![5, 1, 3]];
        let matrix_i32: Vec<Vec<i32>> = vec![vec![2, 5, 4], vec![5, 1, 2], vec![4, 2, 3]];
        let flattened_matrix_i64: Vec<Modint<Mod998244353>> = vec![
            Modint::raw(3),
            Modint::raw(2),
            Modint::raw(1),
            Modint::raw(4),
            Modint::raw(2),
            Modint::raw(2),
            Modint::raw(5),
            Modint::raw(1),
            Modint::raw(3),
        ];
        let flattened_matrix_i32: Vec<Modint<Mod998244353>> = vec![
            Modint::raw(2),
            Modint::raw(5),
            Modint::raw(4),
            Modint::raw(5),
            Modint::raw(1),
            Modint::raw(2),
            Modint::raw(4),
            Modint::raw(2),
            Modint::raw(3),
        ];

        let a = Matrix::<Mod998244353>::from(matrix_i64);
        let b = Matrix::<Mod998244353>::from(matrix_i32);

        assert_eq!(Matrix::<Mod998244353>::new(4, 3).matrix, vec![Modint::zero(); 12]);
        assert_eq!(
            Matrix::<Mod998244353>::id(3).matrix,
            vec![
                Modint::raw(1),
                Modint::raw(0),
                Modint::raw(0),
                Modint::raw(0),
                Modint::raw(1),
                Modint::raw(0),
                Modint::raw(0),
                Modint::raw(0),
                Modint::raw(1)
            ]
        );
        assert_eq!(a.matrix, flattened_matrix_i64.clone());
        assert_eq!(b.matrix, flattened_matrix_i32.clone());

        //     |3 2 1|       |2 5 4|
        // a = |4 2 2| , b = |5 1 2|
        //     |5 1 3|       |4 2 3|
        assert_eq!(
            a.add(&b).matrix,
            vec![
                Modint::raw(5),
                Modint::raw(7),
                Modint::raw(5),
                Modint::raw(9),
                Modint::raw(3),
                Modint::raw(4),
                Modint::raw(9),
                Modint::raw(3),
                Modint::raw(6)
            ]
        );
        assert_eq!(
            a.sub(&b).matrix,
            vec![
                Modint::raw(1),
                Modint::raw(998244350),
                Modint::raw(998244350),
                Modint::raw(998244352),
                Modint::raw(1),
                Modint::raw(0),
                Modint::raw(1),
                Modint::raw(998244352),
                Modint::raw(0)
            ]
        );
        assert_eq!(
            a.mul(&b).matrix,
            vec![
                Modint::raw(20),
                Modint::raw(19),
                Modint::raw(19),
                Modint::raw(26),
                Modint::raw(26),
                Modint::raw(26),
                Modint::raw(27),
                Modint::raw(32),
                Modint::raw(31)
            ]
        );
        assert_eq!(
            a.pow(324355).matrix,
            vec![
                Modint::raw(957495479),
                Modint::raw(800953849),
                Modint::raw(608722515),
                Modint::raw(419297532),
                Modint::raw(552242599),
                Modint::raw(607036125),
                Modint::raw(417611142),
                Modint::raw(618274426),
                Modint::raw(347086574)
            ]
        );
    }
}
