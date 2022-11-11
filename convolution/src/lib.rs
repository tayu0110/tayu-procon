use complex::Complex;

pub fn fft_cooley_tukey_radix_2(a: &mut [Complex<f64>], inv: bool) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in 0..log {
        // backet_num = 1 << i;
        // Split backet_num (deg / backet_num)-order DFT into (deg / backet_num / 2)-order DFT.
        let backet_width = deg >> i;
        let half_width = backet_width >> 1;
        // W = exp(2PI/N), N = backet_width
        let root = Complex::from_polar(1.0, if inv { 2.0 } else { -2.0 } * std::f64::consts::PI / backet_width as f64);
        for base in (0..deg).step_by(backet_width) {
            let mut w = Complex::new(1.0, 0.0);
            for k in 0..half_width {
                let (w0, w1) = (a[base+k] + a[base+k+half_width], a[base+k] - a[base+k+half_width]);

                a[base+k] = w0;
                a[base+k+half_width] = w1 * w;
                w *= root;
            }
        }
    }

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
            if inv {
                a[i] = a[i].conjugate();
                a[i] /= Complex::new(deg as f64, 0.0);
                if i != rev_i {
                    a[rev_i] = a[rev_i].conjugate();
                    a[rev_i] /= Complex::new(deg as f64, 0.0);
                }
            }
        }
    }
}

pub fn fft_cooley_tukey_radix_4(a: &mut [Complex<f64>], inv: bool) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in (0..log).step_by(2) {
        // backet_num = 1 << i
        // Split backet_num (deg / backet_num)-order DFT into (deg / backet_num / 2 or 4)-order DFT.
        let backet_width = deg >> i;
        let root = Complex::from_polar(1.0, if !inv { 2.0 } else { -2.0 } * std::f64::consts::PI / backet_width as f64);
        if i + 1 == log {
            let half_width = backet_width >> 1;
            for base in (0..deg).step_by(backet_width) {
                let mut w = Complex::from(1.0f64);
                for k in base..base+half_width {
                    let (w0, w1) = (a[k] + a[k+half_width], a[k] - a[k+half_width]);

                    a[k] = w0;
                    a[k+half_width] = w1 * w;
                    w *= root;
                }
            }
        } else {
            let quarter_width = backet_width >> 2;
            for base in (0..deg).step_by(backet_width) {
                let mut w = 1.0f64.into();
                for k in base..base+quarter_width {
                    let (c0, c1, c2, c3) = (a[k], a[k+quarter_width], a[k+2*quarter_width], a[k+3*quarter_width]);
                    let (w0, w1, w2, w3) = 
                        if !inv {
                            // If W = exp(2PIi/N), then
                            // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |
                            // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1   i  -1  -i |
                            // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |
                            // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1  -i  -1   i |
                            (
                                c0 + c1 + c2 + c3,
                                c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()),
                                c0 - c1 + c2 - c3,
                                c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()),
                            )
                        } else {
                            // If W = exp(-2PIi/N), then
                            // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |
                            // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1  -i  -1   i |
                            // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |
                            // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1   i  -1  -i |
                            (
                                c0 + c1 + c2 + c3,
                                c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()),
                                c0 - c1 + c2 - c3,
                                c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()),
                            )
                        };

                    a[k] = w0;
                    let mut nw = w;
                    a[k+2*quarter_width] = w1 * nw;
                    nw *= w;
                    a[k+quarter_width] = w2 * nw;
                    nw *= w;
                    a[k+3*quarter_width] = w3 * nw;
                    w *= root;
                }
            }
        }
    }

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
            if inv {
                a[i] = a[i].conjugate();
                a[i] /= (deg as f64).into();
                if i != rev_i {
                    a[rev_i] = a[rev_i].conjugate();
                    a[rev_i] /= (deg as f64).into();
                }
            }
        }
    }
}

pub fn fconvolution(a: &Vec<f64>, b: &Vec<f64>) -> Vec<f64> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    
    let mut a2 = vec![Complex::from(0.0); n];
    a.into_iter()
        .zip(a2.iter_mut())
        .for_each(|(v, w)| *w = (*v).into());
    
    let mut b2 = vec![Complex::from(0.0); n];
    b.into_iter()
        .zip(b2.iter_mut())
        .for_each(|(v, w)| *w = (*v).into());
    
    fft_cooley_tukey_radix_4(&mut a2, false);
    fft_cooley_tukey_radix_4(&mut b2, false);

    a2
        .iter_mut()
        .zip(b2.into_iter())
        .for_each(|(l, r)| *l *= r);
    fft_cooley_tukey_radix_4(&mut a2, true);
    
    a2[0..deg]
        .into_iter()
        .map(|v| v.real())
        .collect()
}

pub fn iconvolution(a: &Vec<i64>, b: &Vec<i64>) -> Vec<i64> {
    let a = a
        .iter()
        .map(|v| *v as f64)
        .collect::<Vec<_>>();
    let b = b
        .iter()
        .map(|v| *v as f64)
        .collect::<Vec<_>>();
    fconvolution(&a, &b)
        .into_iter()
        .map(|v| v.round() as i64)
        .collect()
}
                 
type Mint = modint::Mint<modint::Mod998244353>;

// Only usable 998244353 for modulo.
fn ntt(a: &mut Vec<Mint>, inv: bool) {
    let n = a.len();
    assert!(n == 1 << n.trailing_zeros());
    if n == 1 {
        return;
    }
    let root = Mint::nth_root(n as i64 * if inv { -1 } else { 1 });
    let mut roots = vec![Mint::one(); n/2+1];
    
    for i in 0..n/2 {
        roots[i+1] = roots[i] * root;
    }
    
    let mut b = vec![Mint::zero(); n];
    for (w, i) in (0..n.trailing_zeros()).map(|v| 1 << v).zip((0..n.trailing_zeros()).rev().map(|v| 1 << v)) {
        for j in 0..i {
            for k in 0..w {
                b[k+((w*j)<<1)] = a[k+w*j] + a[k+w*j+(n>>1)];
                b[k+((w*j)<<1)+w] = roots[w*j] * (a[k+w*j] - a[k+w*j+(n>>1)]);
            }
        }
        std::mem::swap(a, &mut b);
    }
}

pub fn convolution(a: &Vec<Mint>, b: &Vec<Mint>) -> Vec<Mint> {
    let mut n = 1;
    let deg = a.len() + b.len() - 1;
    while n < deg {
        n <<= 1;
    }
    
    let mut na = a.clone();
    let mut nb = b.clone();
    na.resize(n, Mint::new(0));
    nb.resize(n, Mint::new(0));
    ntt(&mut na, false);
    ntt(&mut nb, false);
    
    let mut nc = na
        .into_iter()
        .zip(nb.into_iter())
        .map(|(l, r)| l * r)
        .collect::<Vec<_>>();
    ntt(&mut nc, true);
    
    let ninv = Mint::new(n as i64).inv();
    nc[0..deg]
        .into_iter()
        .map(|v| *v * ninv)
        .collect()
}


#[cfg(test)]
mod tests {
    use complex::Complex;
    use super::{
        fft_cooley_tukey_radix_2,
        fft_cooley_tukey_radix_4,
        fconvolution
    };

    fn calc_diff(a: &[Complex], b: &[Complex]) -> f64 {
        let mut diff_max = 0.0;
        for (d, v) in a.into_iter().zip(b.into_iter()) {
            if (d.real() - v.real()).abs() > diff_max {
                diff_max = (d.real() - v.real()).abs();
            }
            if (d.imag() - v.imag()).abs() > diff_max {
                diff_max = (d.imag() - v.imag()).abs();
            }
        }

        diff_max
    }

    #[test]
    fn cooley_tukey_radix_2_test() {
        let mut data1 = vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(3.0, 0.0), Complex::new(4.0, 0.0)];
        fft_cooley_tukey_radix_2(&mut data1, false);
        fft_cooley_tukey_radix_2(&mut data1, true);
        let diff_max = calc_diff(&vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(3.0, 0.0), Complex::new(4.0, 0.0)], &data1);
        assert!(diff_max < 1e-10);
        
        let mut data2 = vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(4.0, 0.0), Complex::new(8.0, 0.0)];
        fft_cooley_tukey_radix_2(&mut data2, false);
        fft_cooley_tukey_radix_2(&mut data2, true);
        let diff_max = calc_diff(&vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(4.0, 0.0), Complex::new(8.0, 0.0)], &data2);
        assert!(diff_max < 1e-10);        
    }
    
    #[test]
    fn cooley_tukey_radix_4_test() {
        let mut data1 = vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(3.0, 0.0), Complex::new(4.0, 0.0)];
        fft_cooley_tukey_radix_4(&mut data1, false);
        fft_cooley_tukey_radix_4(&mut data1, true);
        let diff_max = calc_diff(&vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(3.0, 0.0), Complex::new(4.0, 0.0)], &data1);
        assert!(diff_max < 1e-10);

        let mut data2 = vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(4.0, 0.0), Complex::new(8.0, 0.0)];
        fft_cooley_tukey_radix_4(&mut data2, false);
        fft_cooley_tukey_radix_4(&mut data2, true);
        let diff_max = calc_diff(&vec![Complex::new(1.0, 0.0), Complex::new(2.0, 0.0), Complex::new(4.0, 0.0), Complex::new(8.0, 0.0)], &data2);
        assert!(diff_max < 1e-10);        
    }

    #[test]
    fn convolution_test() {
        let a = vec![1.0, 2.0, 3.0, 4.0];
        let b = vec![1.0, 2.0, 4.0, 8.0];

        let c = fconvolution(&a, &b);
        let c = c.into_iter().map(|c| c.round() as i32).collect::<Vec<_>>();
        assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
    }
}