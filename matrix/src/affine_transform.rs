use crate::MatrixElement;
use std::ops::{Div, Neg};

#[derive(Debug, Clone)]
pub struct AffineTransformation<T: MatrixElement + Neg> {
    matrix: [T; 9],
}

impl<T: MatrixElement + Div + Neg<Output = T>> AffineTransformation<T> {
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
