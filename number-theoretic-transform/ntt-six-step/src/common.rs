#[inline]
// reference: https://www.kurims.kyoto-u.ac.jp/~ooura/fftman/ftmn1_25.html#sec1_2_5
pub fn bit_reverse<T>(a: &mut [T]) {
    let deg = a.len();
    let nh = deg >> 1;
    let nh1 = nh + 1;
    let mut i = 0;
    for j in (0..nh).step_by(2) {
        if j < i {
            a.swap(i, j);
            a.swap(i + nh1, j + nh1);
        }
        a.swap(j + nh, i + 1);
        let mut k = nh >> 1;
        i ^= k;
        while k > i {
            k >>= 1;
            i ^= k;
        }
    }
}
