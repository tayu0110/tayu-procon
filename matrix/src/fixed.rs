use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use zero_one::{One, Zero};

#[derive(Debug, Clone, Copy)]
pub struct FixedMatrix<T: Clone + Copy, const ROW: usize, const COL: usize> {
    data: [[T; COL]; ROW],
}

impl<T: Clone + Copy, const ROW: usize, const COL: usize> FixedMatrix<T, ROW, COL> {
    pub const fn from_array(arr: [[T; COL]; ROW]) -> Self {
        Self { data: arr }
    }

    pub const fn shape(&self) -> (usize, usize) {
        (ROW, COL)
    }

    pub fn set(&mut self, row: usize, col: usize, data: T) {
        debug_assert!(row < ROW && col < COL);
        self.data[row][col] = data;
    }

    pub const fn get(&self, row: usize, col: usize) -> T {
        debug_assert!(row < ROW && col < COL);
        self.data[row][col]
    }
}

impl<T, const ROW: usize, const COL: usize> FixedMatrix<T, ROW, COL>
where
    T: Clone + Copy + Zero,
{
    pub fn transpose(&self) -> FixedMatrix<T, COL, ROW> {
        let mut res = [[T::zero(); ROW]; COL];
        for i in 0..ROW {
            for (j, res) in res.iter_mut().enumerate() {
                res[i] = self.data[i][j];
            }
        }
        FixedMatrix { data: res }
    }

    pub fn zero() -> Self {
        <Self as Zero>::zero()
    }
}

impl<T, const N: usize> FixedMatrix<T, N, N>
where
    T: Clone + Copy + Zero + One,
{
    pub fn one() -> Self {
        <Self as One>::one()
    }
}

impl<T, const N: usize> FixedMatrix<T, N, N>
where
    T: Clone + Copy + Zero + One + Mul<Output = T>,
{
    pub fn pow(self, mut exp: u64) -> Self {
        let (mut res, mut val) = (Self::one(), self);
        while exp > 1 {
            if exp & 1 != 0 {
                res *= val;
            }
            val *= val;
            exp >>= 1;
        }
        res *= val;
        res
    }
}

impl<T, const ROW: usize, const COL: usize> Add<Self> for FixedMatrix<T, ROW, COL>
where
    T: Clone + Copy + Add<Output = T>,
{
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        self.data
            .iter_mut()
            .flatten()
            .zip(rhs.data.iter().flatten())
            .for_each(|(l, r)| *l = *l + *r);
        self
    }
}

impl<T, const ROW: usize, const COL: usize> Sub<Self> for FixedMatrix<T, ROW, COL>
where
    T: Clone + Copy + Sub<Output = T>,
{
    type Output = Self;
    fn sub(mut self, rhs: Self) -> Self::Output {
        self.data
            .iter_mut()
            .flatten()
            .zip(rhs.data.iter().flatten())
            .for_each(|(l, r)| *l = *l - *r);
        self
    }
}

impl<T, const ROW: usize, const COL: usize, const M: usize> Mul<FixedMatrix<T, COL, M>>
    for FixedMatrix<T, ROW, COL>
where
    T: Clone + Copy + Mul<Output = T> + Zero,
{
    type Output = FixedMatrix<T, ROW, M>;
    fn mul(self, rhs: FixedMatrix<T, COL, M>) -> Self::Output {
        let mut res = [[T::zero(); M]; ROW];
        for (i, res) in res.iter_mut().enumerate() {
            for j in 0..COL {
                for (k, res) in res.iter_mut().enumerate() {
                    *res = self.data[i][j] * rhs.data[j][k];
                }
            }
        }
        FixedMatrix { data: res }
    }
}

impl<T, const ROW: usize, const COL: usize> Zero for FixedMatrix<T, ROW, COL>
where
    T: Clone + Copy + Zero,
{
    fn zero() -> Self {
        Self { data: [[T::zero(); COL]; ROW] }
    }
}

impl<T, const N: usize> One for FixedMatrix<T, N, N>
where
    T: Clone + Copy + Zero + One,
{
    fn one() -> Self {
        let mut res = Self::zero();
        for i in 0..N {
            res.data[i][i] = T::one();
        }
        res
    }
}

impl<T, const ROW: usize, const COL: usize> AddAssign for FixedMatrix<T, ROW, COL>
where
    T: Clone + Copy + Add<Output = T>,
{
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<T, const ROW: usize, const COL: usize> SubAssign for FixedMatrix<T, ROW, COL>
where
    T: Clone + Copy + Sub<Output = T>,
{
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<T, const N: usize> MulAssign for FixedMatrix<T, N, N>
where
    T: Clone + Copy + Mul<Output = T> + Zero,
{
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}
