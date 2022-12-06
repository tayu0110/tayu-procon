use numeric::{signed::Signed, IntoFloat, Numeric};
use std::convert::{From, Into, TryFrom};
use std::ops::{Add, AddAssign, Neg, Sub, SubAssign};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
struct Vector<T: Numeric + Signed + IntoFloat>(T, T);

impl<T: Numeric + Signed + IntoFloat> From<(T, T)> for Vector<T> {
    fn from(from: (T, T)) -> Self { Self(from.0, from.1) }
}

impl<T: Numeric + Signed + IntoFloat> From<[T; 2]> for Vector<T> {
    fn from(from: [T; 2]) -> Self { Self(from[0], from[1]) }
}

impl<T: Numeric + Signed + IntoFloat> TryFrom<Vec<T>> for Vector<T> {
    type Error = Error;
    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        match value.len() {
            2 => Ok(Self(value[0], value[1])),
            _ => Err(Error(
                "Failed to generate the instance of geometry::Vector because the length of the argument Vec<i64> is not 2.",
            )),
        }
    }
}

#[allow(dead_code)]
impl<T: Numeric + Signed + IntoFloat> Vector<T> {
    fn new(from: [T; 2], to: [T; 2]) -> Self { Self(to[0] - from[0], to[1] - from[1]) }

    fn inner_product(&self, rhs: &Vector<T>) -> T { self.0 * rhs.0 + self.1 * rhs.1 }

    fn outer_product(&self, rhs: &Vector<T>) -> T { self.0 * rhs.1 - self.1 * rhs.0 }

    fn scalar_product(&self, rhs: T) -> Self { Self(self.0 * rhs, self.1 * rhs) }

    fn is_vertical(&self, rhs: &Vector<T>) -> bool { self.inner_product(rhs) == T::zero() }

    fn is_parallel(&self, rhs: &Vector<T>) -> bool { self.outer_product(rhs) == T::zero() }

    // 0 <= theta <= 180
    fn arg(&self, rhs: &Vector<T>) -> f64 {
        ((self.0 * rhs.0 + self.1 * rhs.1).as_f64() / ((self.0 * self.0 + self.1 * self.1) * (rhs.0 * rhs.0 + rhs.1 * rhs.1)).as_f64().sqrt()).acos()
    }
}

impl<T: Numeric + Signed + IntoFloat> Add for Vector<T> {
    type Output = Vector<T>;
    fn add(self, rhs: Self) -> Self::Output { Self(self.0 + rhs.0, self.1 + rhs.1) }
}

impl<T: Numeric + Signed + IntoFloat> Sub for Vector<T> {
    type Output = Vector<T>;
    fn sub(self, rhs: Self) -> Self::Output { Self(self.0 - rhs.0, self.1 - rhs.1) }
}

impl<T: Numeric + Signed + IntoFloat> Neg for Vector<T> {
    type Output = Vector<T>;
    fn neg(self) -> Self::Output { Self(-self.0, -self.1) }
}

impl<T: Numeric + Signed + IntoFloat> AddAssign for Vector<T> {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
        self.1 += rhs.1;
    }
}

impl<T: Numeric + Signed + IntoFloat> SubAssign for Vector<T> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
        self.1 -= rhs.1;
    }
}

#[derive(Debug)]
pub struct Error(&'static str);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.0) }
}

impl std::error::Error for Error {}

// 凸包の構成点をx座標が最も小さいものから時計回りに返す
pub fn convex_hull<T: Numeric + Signed + IntoFloat>(mut points: Vec<(T, T)>) -> Vec<(T, T)> {
    if points.len() < 2 {
        return points;
    }

    points.sort_by(|v, w| v.partial_cmp(w).unwrap_or(std::cmp::Ordering::Equal));

    let mut convex = vec![vec![]; 2];
    let check = [std::cmp::Ordering::Less, std::cmp::Ordering::Greater];
    for (x, y) in points {
        for (i, convex) in convex.iter_mut().enumerate() {
            while convex.len() >= 2 {
                let ((sx, sy), (fx, fy)) = (convex.pop().unwrap(), *convex.last().unwrap());
                let (f, s) = (Vector::new([fx, fy], [sx, sy]), Vector::new([sx, sy], [x, y]));

                let outer_product = f.outer_product(&s);
                if outer_product.partial_cmp(&T::zero()) == Some(check[i]) || outer_product == T::zero() {
                    convex.push((sx, sy));
                    break;
                }
            }
            convex.push((x, y));
        }
    }
    convex
        .into_iter()
        .enumerate()
        .flat_map(|(i, mut v)| {
            if i == 0 {
                v
            } else {
                v.reverse();
                let len = v.len();
                v[1..len - 1].into()
            }
        })
        .collect()
}

// points(周上の順番であることが必要)に含まれる点を結んだ線を周とする多角形の面積求める
pub fn points_to_area<T: Numeric + Signed>(points: &Vec<(T, T)>) -> T {
    let len = points.len();
    let mut res = T::zero();
    for (i, (x, y)) in points.into_iter().enumerate() {
        let (nx, ny) = points[(i + 1) % len];
        res += (*x - nx) * (*y + ny);
    }

    if res < T::zero() {
        res = -res;
    }
    res / (T::one() + T::one())
}

pub fn sort_by_arg<T: Numeric>(mut points: Vec<(T, T)>) -> Vec<(T, T)> {
    points.sort_by(|&(x0, y0), &(x1, y1)| {
        ((y0, x0) < (T::zero(), T::zero()))
            .cmp(&((y1, x1) < (T::zero(), T::zero())))
            .then_with(|| (x1 * y0).partial_cmp(&(x0 * y1)).unwrap())
    });

    points
}
