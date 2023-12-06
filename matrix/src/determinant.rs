pub trait Determinant {
    type Output;
    fn determinant(&self) -> Self::Output;
}
