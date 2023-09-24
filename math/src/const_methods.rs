use arbitrary_modint::ArbitraryStaticModint;

/// The given number is determined to be prime or not prime using the Miller-Rabin primality test.
pub const fn miller_rabin_test_const<const P: u64>() -> bool {
    if P == 1 || P & 1 == 0 {
        return P == 2;
    }

    let s = (P - 1).trailing_zeros();
    let t = (P - 1) >> s;

    const A: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
    let mut i = 0;
    let neg = P - 1;
    while i < 7 {
        let a = ArbitraryStaticModint::<P>::new(A[i]);
        if a.val() != 0 {
            let mut at = a.pow(t);
            // a^t = 1 (mod p) or a^t = -1 (mod p)
            if at.val() != 1 && at.val() != neg {
                let mut j = 1;
                let mut f = false;
                // found i satisfying a^((2^i)*t) = -1 (mod p)
                while j < s {
                    at = at.mul_raw(at.val());
                    if at.val() == neg {
                        f = true;
                        break;
                    }
                    j += 1;
                }

                if !f {
                    return false;
                }
            }
        }

        i += 1;
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn miller_rabin_test_test() {
        assert!(miller_rabin_test_const::<998244353>());
        assert!(miller_rabin_test_const::<2>());
        assert!(!miller_rabin_test_const::<4>());
        assert!(!miller_rabin_test_const::<91>());
        assert!(!miller_rabin_test_const::<561>());
        assert!(!miller_rabin_test_const::<999381247093216751>());
    }
}
