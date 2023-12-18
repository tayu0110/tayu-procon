mod affine_transform;
mod convert;
mod determinant;
mod fixed;
mod product;
mod rank;
mod square;

pub use affine_transform::*;
use arbitrary_modint::ArbitraryModint;
pub use determinant::*;
pub use fixed::*;
use montgomery_modint::MontgomeryModint;
pub use product::{dot::*, frobenius::*, hadamard::*, scalar::*};
pub use rank::*;
pub use square::*;
use static_modint::{Modulo, StaticModint};
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign, Sub, SubAssign};
use zero_one::{One, Zero};

#[derive(Debug, Clone)]
pub struct Matrix<T: Clone> {
    row: u32,
    col: u32,
    data: Vec<T>,
}

impl<T: Clone> Matrix<T> {
    /// Return the shape as (row, col).
    pub fn shape(&self) -> (usize, usize) {
        (self.row as usize, self.col as usize)
    }

    pub fn from_vec(v: Vec<Vec<T>>) -> Self {
        let row = v.len() as u32;
        let col = v.first().map_or(0, |v| v.len()) as u32;
        Self { row, col, data: v.into_iter().flatten().collect() }
    }

    pub fn from_vec_as_shape(row: usize, col: usize, v: Vec<T>) -> Self {
        debug_assert_eq!(row * col, v.len());
        Self { row: row as u32, col: col as u32, data: v }
    }

    pub fn get(&self, row: usize, col: usize) -> &T {
        let (r, c) = self.shape();
        debug_assert!(row < r && col < c);
        &self.data[row * c + col]
    }

    pub fn get_mut(&mut self, row: usize, col: usize) -> &mut T {
        let (r, c) = self.shape();
        debug_assert!(row < r && col < c);
        &mut self.data[row * c + col]
    }

    pub fn set(&mut self, row: usize, col: usize, val: T) {
        let (r, c) = self.shape();
        debug_assert!(row < r && col < c);
        self.data[row * c + col] = val;
    }

    pub fn transpose(&self) -> Self {
        let (r, c) = self.shape();
        let mut data = self.data.clone();
        if r == 1 || c == 1 {
            return Self { row: self.col, col: self.row, data };
        }

        for i in 0..r {
            for j in 0..c {
                data[j * r + i] = self.data[i * c + j].clone();
            }
        }
        Self { row: self.col, col: self.row, data }
    }

    pub fn split_at_row(self, at: usize) -> (Self, Self) {
        let (row, col) = self.shape();
        if at == row {
            return (self, Self { row: 0, col: 0, data: vec![] });
        }
        let (upper, lower) = self.data.split_at(at * col);
        (
            Self { row: at as u32, col: col as u32, data: upper.to_vec() },
            Self {
                row: (row - at) as u32,
                col: col as u32,
                data: lower.to_vec(),
            },
        )
    }

    pub fn split_at_col(self, at: usize) -> (Self, Self) {
        let (row, col) = self.shape();
        if at == col {
            return (self, Self { row: 0, col: 0, data: vec![] });
        }
        assert!(at <= col);
        let (left, right) = self.data.chunks_exact(col).fold(
            (
                Vec::with_capacity(row * at),
                Vec::with_capacity(row * (col - at)),
            ),
            |mut s, v| {
                s.0.extend_from_slice(&v[..at]);
                s.1.extend_from_slice(&v[at..]);
                s
            },
        );
        (
            Self { row: row as u32, col: at as u32, data: left },
            Self { row: row as u32, col: (col - at) as u32, data: right },
        )
    }

    pub fn merge_horizontal(left: Self, right: Self) -> Self {
        let (lrow, lcol) = left.shape();
        let (rrow, rcol) = right.shape();
        assert_eq!(lrow, rrow);
        let data = left
            .data
            .chunks_exact(lcol)
            .zip(right.data.chunks_exact(rcol))
            .fold(Vec::with_capacity(lrow * (lcol + rcol)), |mut s, (v, w)| {
                s.extend_from_slice(v);
                s.extend_from_slice(w);
                s
            });
        Self { row: lrow as u32, col: (lcol + rcol) as u32, data }
    }

    pub fn merge_vertical(mut upper: Self, lower: Self) -> Self {
        let (urow, ucol) = upper.shape();
        let (lrow, lcol) = lower.shape();
        assert_eq!(ucol, lcol);
        upper.data.extend(lower.data);
        upper.row = urow as u32 + lrow as u32;
        upper
    }
}

impl<T: Clone + Zero> Matrix<T> {
    pub fn zeros(row: usize, col: usize) -> Self {
        let data = vec![T::zero(); row * col];
        Self { row: row as u32, col: col as u32, data }
    }

    pub fn resize(&mut self, row: usize, col: usize, val: T) {
        let (r, c) = self.shape();
        if row == r && col == c {
            return;
        }

        if col == c {
            self.data.resize(row * col, val);
            self.row = row as u32;
            return;
        }

        let mut new = vec![val; row * col];
        let window = col.min(c);
        new.chunks_exact_mut(col)
            .zip(self.data.chunks_exact(c))
            .for_each(|(to, from)| to[..window].clone_from_slice(&from[..window]));
        self.data = new;
        self.row = row as u32;
        self.col = col as u32;
    }
}

impl<T: Clone + Zero + One> Matrix<T> {
    pub fn id(n: usize) -> Self {
        let mut data = vec![T::zero(); n * n];
        (0..n).for_each(|i| data[i * n + i] = T::one());
        Self { row: n as u32, col: n as u32, data }
    }
}

impl<T> Matrix<T>
where
    T: Debug + Clone + Zero + One + Mul<Output = T> + AddAssign,
{
    pub fn pow(&self, mut exp: u64) -> Self {
        let (row, col) = self.shape();
        debug_assert_eq!(row, col);
        let (mut res, mut val) = (Self::id(row), self.clone());
        if exp == 0 {
            return res;
        }
        while exp > 1 {
            if exp & 1 != 0 {
                res.dot_assign(&val);
            }
            val.dot_assign(&val.clone());
            exp >>= 1;
        }
        res.dot_assign(&val);
        res
    }
}

impl<T: Clone + Mul<U, Output = T>, U: Clone> ScalarProduct<U> for Matrix<T> {
    type Output = Matrix<T>;
    fn scalar_product(self, rhs: U) -> Self::Output {
        let mut data = self.data.clone();
        data.iter_mut().for_each(|l| *l = l.clone() * rhs.clone());
        Matrix { row: self.row, col: self.col, data }
    }
}

impl<T: Clone + MulAssign<U>, U: Clone> ScalarProductAssign<U> for Matrix<T> {
    fn scalar_product_assign(&mut self, rhs: U) {
        self.data.iter_mut().for_each(|l| *l *= rhs.clone());
    }
}

impl<T, U> HadamardProduct<&Matrix<U>> for &Matrix<T>
where
    T: Clone + Mul<U, Output = T>,
    U: Clone,
{
    type Output = Matrix<T>;
    fn hadamard(self, rhs: &Matrix<U>) -> Self::Output {
        debug_assert!(self.shape() == rhs.shape());
        let mut data = self.data.clone();
        data.iter_mut()
            .zip(&rhs.data)
            .for_each(|(l, r)| *l = l.clone() * r.clone());
        Matrix { row: self.row, col: self.col, data }
    }
}

impl<'a, T, U> DotProduct<&'a Matrix<U>> for Matrix<T>
where
    T: Clone + Zero + Add<Output = T> + Mul<&'a U, Output = T>,
    U: Clone,
{
    type Output = Matrix<T>;
    fn dot(self, rhs: &'a Matrix<U>) -> Self::Output {
        debug_assert!(self.shape().1 == rhs.shape().0);
        let (lrow, lcol) = self.shape();
        let (_, rcol) = rhs.shape();
        let mut data = vec![T::zero(); lrow * rcol];
        for (s, t) in data
            .chunks_exact_mut(rcol)
            .zip(self.data.chunks_exact(lcol))
        {
            for (v, u) in t.iter().zip(rhs.data.chunks_exact(rcol)) {
                for (x, y) in s.iter_mut().zip(u.iter()) {
                    *x = x.clone() + v.clone() * y;
                }
            }
        }
        Matrix { row: lrow as u32, col: rcol as u32, data }
    }
}

impl<T, U> DotProduct<&Matrix<U>> for &Matrix<T>
where
    T: Clone + Zero + Add<Output = T> + Mul<U, Output = T>,
    U: Clone,
{
    type Output = Matrix<T>;
    fn dot(self, rhs: &Matrix<U>) -> Self::Output {
        debug_assert!(self.shape().1 == rhs.shape().0);
        let (lrow, lcol) = self.shape();
        let (_, rcol) = rhs.shape();
        let mut data = vec![T::zero(); lrow * rcol];
        for (s, t) in data
            .chunks_exact_mut(rcol)
            .zip(self.data.chunks_exact(lcol))
        {
            for (v, u) in t.iter().zip(rhs.data.chunks_exact(rcol)) {
                for (x, y) in s.iter_mut().zip(u.iter()) {
                    *x = x.clone() + v.clone() * y.clone();
                }
            }
        }
        Matrix { row: lrow as u32, col: rcol as u32, data }
    }
}

impl<'a, T, U> DotProductAssign<&'a Matrix<U>> for Matrix<T>
where
    T: Clone + Zero + Mul<U, Output = T> + AddAssign,
    U: Clone,
{
    fn dot_assign(&mut self, rhs: &'a Matrix<U>) {
        debug_assert!(self.shape().1 == rhs.shape().0);
        let (lrow, lcol) = self.shape();
        let (_, rcol) = rhs.shape();
        let mut data = vec![T::zero(); lrow * rcol];
        for (s, t) in data
            .chunks_exact_mut(rcol)
            .zip(self.data.chunks_exact(lcol))
        {
            for (v, u) in t.iter().zip(rhs.data.chunks_exact(rcol)) {
                for (x, y) in s.iter_mut().zip(u.iter()) {
                    *x += v.clone() * y.clone();
                }
            }
        }
        self.data = data;
    }
}

impl<T, U> FrobeniusProduct<&Matrix<U>> for &Matrix<T>
where
    T: Clone + Zero + Add<Output = T> + Mul<U, Output = T>,
    U: Clone,
{
    type Output = T;
    fn frobenius(self, rhs: &Matrix<U>) -> Self::Output {
        self.hadamard(rhs)
            .data
            .into_iter()
            .fold(T::zero(), |s, v| s + v)
    }
}

impl<T: Clone + Add<U, Output = T>, U: Clone> Add<Matrix<U>> for Matrix<T> {
    type Output = Matrix<T>;
    fn add(mut self, rhs: Matrix<U>) -> Self::Output {
        debug_assert!(self.shape() == rhs.shape());
        self.data
            .iter_mut()
            .zip(rhs.data)
            .for_each(|(l, r)| *l = l.clone() + r);
        self
    }
}

impl<'a, T: Clone + Add<&'a U, Output = T>, U: Clone> Add<&'a Matrix<U>> for Matrix<T> {
    type Output = Matrix<T>;
    fn add(mut self, rhs: &'a Matrix<U>) -> Self::Output {
        debug_assert!(self.shape() == rhs.shape());
        self.data
            .iter_mut()
            .zip(&rhs.data)
            .for_each(|(l, r)| *l = l.clone() + r);
        self
    }
}

impl<T: Clone + Sub<U, Output = T>, U: Clone> Sub<Matrix<U>> for Matrix<T> {
    type Output = Matrix<T>;
    fn sub(mut self, rhs: Matrix<U>) -> Self::Output {
        debug_assert!(self.shape() == rhs.shape());
        self.data
            .iter_mut()
            .zip(rhs.data)
            .for_each(|(l, r)| *l = l.clone() - r);
        self
    }
}

impl<'a, T: Clone + Sub<&'a U, Output = T>, U: Clone> Sub<&'a Matrix<U>> for Matrix<T> {
    type Output = Matrix<T>;
    fn sub(mut self, rhs: &'a Matrix<U>) -> Self::Output {
        debug_assert!(self.shape() == rhs.shape());
        self.data
            .iter_mut()
            .zip(&rhs.data)
            .for_each(|(l, r)| *l = l.clone() - r);
        self
    }
}

impl<T, U> Mul<Matrix<U>> for Matrix<T>
where
    T: Clone + Zero + Add<Output = T> + Mul<U, Output = T>,
    U: Clone,
    Matrix<T>: DotProduct<Matrix<U>, Output = Matrix<T>>,
{
    type Output = Matrix<T>;
    fn mul(self, rhs: Matrix<U>) -> Self::Output {
        self.dot(rhs)
    }
}

impl<T, U> Mul<&Matrix<U>> for &Matrix<T>
where
    T: Clone + Zero + Add<Output = T> + Mul<U, Output = T>,
    U: Clone,
{
    type Output = Matrix<T>;
    fn mul(self, rhs: &Matrix<U>) -> Self::Output {
        self.dot(rhs)
    }
}

impl<T: Clone + AddAssign<U>, U: Clone> AddAssign<&Matrix<U>> for Matrix<T> {
    fn add_assign(&mut self, rhs: &Matrix<U>) {
        debug_assert!(self.shape() == rhs.shape());
        self.data
            .iter_mut()
            .zip(&rhs.data)
            .for_each(|(l, r)| *l += r.clone());
    }
}

impl<T: Clone + SubAssign<U>, U: Clone> SubAssign<&Matrix<U>> for Matrix<T> {
    fn sub_assign(&mut self, rhs: &Matrix<U>) {
        debug_assert!(self.shape() == rhs.shape());
        self.data
            .iter_mut()
            .zip(&rhs.data)
            .for_each(|(l, r)| *l -= r.clone());
    }
}

impl<'a, T, U> MulAssign<&'a Matrix<U>> for Matrix<T>
where
    T: Clone,
    U: Clone,
    Matrix<T>: DotProductAssign<&'a Matrix<U>>,
{
    fn mul_assign(&mut self, rhs: &'a Matrix<U>) {
        self.dot_assign(rhs);
    }
}

macro_rules! impl_determinant {
    ($ty:ty $(, $($tt:tt)* )*) => {
        impl<$($($tt)*)*> Determinant for Matrix<$ty> {
            type Output = $ty;
            fn determinant(&self) -> Self::Output {
                let mut res = <$ty>::one();
                let (row, col) = self.shape();

                let mut data = self.data.clone();
                for i in 0..row {
                    let irow = i * col;
                    if data[irow + i] == <$ty>::zero() {
                        for j in i + 1..row {
                            let jrow = j * col;
                            if data[jrow + i] != <$ty>::zero() {
                                for k in 0..col {
                                    data[irow + k] = data[irow + k] + data[jrow + k];
                                }
                                break;
                            }

                            if j == row - 1 {
                                return <$ty>::zero();
                            }
                        }
                    }

                    res *= data[irow + i];
                    let inv = data[irow + i].inv();
                    for j in i + 1..row {
                        let jrow = j * col;
                        let t = data[jrow + i] * inv;
                        if t != <$ty>::zero() {
                            for k in i..col {
                                data[jrow + k] = data[jrow + k] - t * data[irow + k];
                            }
                        }
                    }
                }

                res
            }
        }
    };
}
impl_determinant!(StaticModint<M>, M: Modulo);
impl_determinant!(MontgomeryModint<M>, M: Modulo);

// https://twitter.com/toomerhs/status/1711424713699016962?s=20
// https://noshi91.hatenablog.com/entry/2020/11/28/115621
impl Determinant for Matrix<ArbitraryModint> {
    type Output = ArbitraryModint;
    fn determinant(&self) -> Self::Output {
        let mut res = ArbitraryModint::one();
        let (row, col) = self.shape();

        let mut data = self.data.clone();
        for i in 0..row {
            let irow = i * col;
            if data[irow + i] == ArbitraryModint::zero() {
                for j in i + 1..row {
                    let jrow = j * col;
                    if data[jrow + i] != ArbitraryModint::zero() {
                        for k in 0..col {
                            data[irow + k] = data[irow + k] + data[jrow + k];
                        }
                        break;
                    }

                    if j == row - 1 {
                        return ArbitraryModint::zero();
                    }
                }
            }

            for j in i + 1..row {
                let jrow = j * col;
                if data[jrow + i] != ArbitraryModint::zero() {
                    let (s, t) = data.split_at_mut(jrow);
                    let (mut s, mut t) = (&mut s[irow..irow + col], &mut t[0..col]);
                    let (mut sa, mut ta) = (s[i].val(), t[i].val());
                    while sa != 0 {
                        if sa <= ta {
                            let d = -ArbitraryModint::raw(ta / sa);
                            ta %= sa;
                            for k in i..col {
                                t[k] = ArbitraryModint::new(
                                    t[k].val() as u64 + d.val() as u64 * s[k].val() as u64,
                                );
                            }
                        }
                        (s, t) = (t, s);
                        (sa, ta) = (ta, sa);
                    }
                }

                if data[irow + i] == ArbitraryModint::zero() {
                    let (s, t) = data.split_at_mut(jrow);
                    s[irow..irow + col]
                        .iter_mut()
                        .zip(t.iter_mut())
                        .for_each(|(l, r)| std::mem::swap(l, r));
                    res = -res;
                }
            }
            res *= data[irow + i];
        }

        res
    }
}

macro_rules! impl_rank {
    ($ty:ty $(, $($tt:tt)* )*) => {
        impl<$($($tt)*)*> Rank for Matrix<$ty> {
            fn rank(&self) -> usize {
                let mut data = self.data.clone();
                let (row, col) = self.shape();
                let mut next_row = 0;
                for i in 0..col {
                    if data[next_row * col + i] == <$ty>::zero() {
                        for j in next_row + 1..row {
                            if data[j * col + i] != <$ty>::zero() {
                                for k in 0..col {
                                    data.swap(next_row * col + k, j * col + k);
                                }
                                break;
                            }
                        }
                    }

                    if data[next_row * col + i] == <$ty>::zero() {
                        continue;
                    }

                    for j in 0..row {
                        if j == next_row {
                            continue;
                        }
                        let jrow = j * col;
                        let t = data[jrow + i] / data[next_row * col + i];
                        for k in i..col {
                            data[jrow + k] = data[jrow + k] - t * data[next_row * col + k];
                        }
                    }

                    next_row += 1;
                }

                next_row
            }
        }
    };
}
impl_rank!(StaticModint<M>, M: Modulo);
impl_rank!(MontgomeryModint<M>, M: Modulo);

impl<T: Clone> Index<(usize, usize)> for Matrix<T> {
    type Output = T;
    fn index(&self, index: (usize, usize)) -> &Self::Output {
        let (row, col) = index;
        let (r, c) = self.shape();
        assert!(row < r && col < c);
        self.get(row, col)
    }
}

impl<T: Clone> Index<(u32, u32)> for Matrix<T> {
    type Output = T;
    fn index(&self, index: (u32, u32)) -> &Self::Output {
        let (row, col) = index;
        let (r, c) = self.shape();
        assert!(row < r as u32 && col < c as u32);
        self.get(row as usize, col as usize)
    }
}

impl<T: Clone> IndexMut<(usize, usize)> for Matrix<T> {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut Self::Output {
        let (row, col) = index;
        let (r, c) = self.shape();
        assert!(row < r && col < c);
        self.get_mut(row, col)
    }
}

impl<T: Clone> IndexMut<(u32, u32)> for Matrix<T> {
    fn index_mut(&mut self, index: (u32, u32)) -> &mut Self::Output {
        let (row, col) = index;
        let (r, c) = self.shape();
        assert!(row < r as u32 && col < c as u32);
        self.get_mut(row as usize, col as usize)
    }
}

#[cfg(test)]
mod tests {
    use crate::Determinant;

    use super::Matrix;
    use static_modint::{Mod998244353, StaticModint};

    #[test]
    fn matrix_test() {
        assert_eq!(
            Matrix::<StaticModint<Mod998244353>>::zeros(4, 3).data,
            vec![StaticModint::zero(); 12]
        );
        assert_eq!(
            Matrix::<StaticModint<Mod998244353>>::id(3).data,
            vec![
                1.into(),
                0.into(),
                0.into(),
                0.into(),
                1.into(),
                0.into(),
                0.into(),
                0.into(),
                1.into()
            ]
        );

        let a = Matrix::<StaticModint<Mod998244353>>::from_vec(vec![
            vec![3.into(), 2.into(), 1.into()],
            vec![4.into(), 2.into(), 2.into()],
            vec![5.into(), 1.into(), 3.into()],
        ]);
        let b = Matrix::<StaticModint<Mod998244353>>::from_vec(vec![
            vec![2.into(), 5.into(), 4.into()],
            vec![5.into(), 1.into(), 2.into()],
            vec![4.into(), 2.into(), 3.into()],
        ]);
        //     |3 2 1|       |2 5 4|
        // a = |4 2 2| , b = |5 1 2|
        //     |5 1 3|       |4 2 3|
        assert_eq!(
            (a.clone() + b.clone()).data,
            vec![
                5.into(),
                7.into(),
                5.into(),
                9.into(),
                3.into(),
                4.into(),
                9.into(),
                3.into(),
                6.into()
            ]
        );
        assert_eq!(
            (a.clone() - b.clone()).data,
            vec![
                1.into(),
                998244350.into(),
                998244350.into(),
                998244352.into(),
                1.into(),
                0.into(),
                1.into(),
                998244352.into(),
                0.into(),
            ]
        );
        assert_eq!(
            (&a * &b).data,
            vec![
                20.into(),
                19.into(),
                19.into(),
                26.into(),
                26.into(),
                26.into(),
                27.into(),
                32.into(),
                31.into()
            ]
        );
        assert_eq!(
            a.pow(324355).data,
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

    #[test]
    fn matrix_determinant_test() {
        let mat = Matrix::<StaticModint<Mod998244353>>::from_vec(vec![
            vec![3.into(), 1.into(), 4.into()],
            vec![1.into(), 5.into(), 9.into()],
            vec![2.into(), 6.into(), 5.into()],
        ]);
        assert_eq!(mat.determinant().val(), 998244263);

        let mat = Matrix::<StaticModint<Mod998244353>>::from_vec(vec![
            vec![1.into(), 2.into(), 3.into()],
            vec![4.into(), 5.into(), 6.into()],
            vec![7.into(), 8.into(), 9.into()],
        ]);
        assert_eq!(mat.determinant().val(), 0);
    }
}
