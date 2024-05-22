use convolution::{convolution, convolution_mod_2_64};
use montgomery_modint::{Mod4194304001, Mod998244353};

#[test]
fn convolution_test() {
    let a = vec![1, 2, 3, 4];
    let b = vec![1, 2, 4, 8];
    let c = convolution::<Mod998244353>(a, b);
    assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
}

#[test]
fn convolution_large_mod_test() {
    let a = vec![1, 2, 3, 4];
    let b = vec![1, 2, 4, 8];
    let c = convolution::<Mod4194304001>(a, b);
    assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
}

#[test]
fn convolution_mod_2_64_test() {
    let a = vec![1, 2, 3, 4];
    let b = vec![1, 2, 4, 8];
    let c = convolution_mod_2_64(a, b);
    assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
}
