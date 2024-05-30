/// Provides a method to perform Montgomery Reduction.
///
/// `Montgomery::convert` can convert an integer to a Montgomery representation, and `Montgomery::reduce` can restore a normal integer representation.  
/// None of the other methods do the conversion internally.
///
/// ```rust
/// use math::Montgomery;
///
/// const M: Montgomery<u8> = Montgomery::<u8>::new(17);
///
/// let a = M.convert(3);
/// assert_eq!(M.multiply(a, a), M.convert(9));
/// assert_eq!(M.pow(a, 3), M.convert(10));
/// assert_eq!(M.reduce(a), 3);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Montgomery<T> {
    pub(crate) modulo: T,
    pub(crate) modulo_inv: T,
    pub(crate) r: T,
    pub(crate) r2: T,
}

macro_rules! impl_primitive_montgomery {
    ( $t:ty, $expand:ty ) => {
        impl Montgomery<$t> {
            /// Convert Montgomery representation to a normal integer representation.
            // t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
            //  if t < 0 then return t + N else return t
            //      T := a (0 <= T < NR)
            //      N := MOD
            //      N':= MOD_INV    NN' = 1 (mod R)
            //      R := R
            pub const fn reduce(&self, val: $t) -> $t {
                let (t, f) = (((val.wrapping_mul(self.modulo_inv) as $expand)
                    .wrapping_mul(self.modulo as $expand)
                    >> <$t>::BITS) as $t)
                    .overflowing_neg();
                t.wrapping_add(self.modulo * f as $t)
            }

            /// Multiply `lhs` and `rhs`.
            /// `lhs` and `rhs` must be Montgomery representations.
            pub const fn multiply(&self, lhs: $t, rhs: $t) -> $t {
                let a = lhs as $expand * rhs as $expand;
                let (t, f) = ((a >> <$t>::BITS) as $t).overflowing_sub(
                    (((a as $t).wrapping_mul(self.modulo_inv) as $expand)
                        .wrapping_mul(self.modulo as $expand)
                        >> <$t>::BITS) as $t,
                );
                t.wrapping_add(self.modulo * f as $t)
            }

            pub const fn add(&self, lhs: $t, rhs: $t) -> $t {
                let (res, f) = lhs.overflowing_add(rhs);
                res.wrapping_sub(self.modulo & ((f || res >= self.modulo) as $t).wrapping_neg())
            }

            pub const fn sub(&self, lhs: $t, rhs: $t) -> $t {
                let (res, f) = lhs.overflowing_sub(rhs);
                res.wrapping_add(self.modulo & (f as $t).wrapping_neg())
            }

            /// Convert a normal integer representation to Montgomery representation.
            ///
            /// To restore, you can use `Montgomery::reduce`.
            ///
            /// # Examples
            /// ```rust
            /// use math::Montgomery;
            ///
            /// const M: Montgomery<u8> = Montgomery::<u8>::new(17);
            /// assert_eq!(M.reduce(M.convert(3)), 3);
            /// ```
            pub const fn convert(&self, val: $t) -> $t {
                self.multiply(val, self.r2)
            }

            /// Calculate `val^exp (mod modulo)`.
            ///
            /// `val` must be Montgomery representation, but `exp` must be a normal integer representation.
            pub const fn pow(&self, val: $t, mut exp: u64) -> $t {
                let (mut res, mut val) = (self.r, val);
                while exp > 0 {
                    if exp & 1 != 0 {
                        res = self.multiply(res, val);
                    }
                    val = self.multiply(val, val);
                    exp >>= 1;
                }
                res
            }

            /// Constructor.
            ///
            /// # Panics
            /// - `modulo` must be odd.
            pub const fn new(modulo: $t) -> Self {
                assert!(modulo & 1 != 0);
                let r = (((1 as $expand) << <$t>::BITS) % modulo as $expand) as $t;
                let r2 = ((modulo as $expand).wrapping_neg() % modulo as $expand) as $t;
                let modulo_inv = {
                    let mut inv = modulo;
                    while modulo.wrapping_mul(inv) != 1 {
                        inv = inv.wrapping_mul((2 as $t).wrapping_sub(modulo.wrapping_mul(inv)));
                    }
                    inv
                };
                Self { modulo, modulo_inv, r, r2 }
            }

            /// Return `0` in Montgomery representation.
            pub const fn zero(&self) -> $t {
                0
            }

            /// Return `1` in Montgomery representation.
            pub const fn one(&self) -> $t {
                self.r
            }

            /// Return the modulus.
            pub const fn modulus(&self) -> $t {
                self.modulo
            }
        }
    };
}

impl_primitive_montgomery!(u8, u16);
impl_primitive_montgomery!(u16, u32);
impl_primitive_montgomery!(u32, u64);
impl_primitive_montgomery!(u64, u128);
impl_primitive_montgomery!(usize, u128);
