use complex::Complex;
use modint::{
    Mint, Mod998244353
};

pub fn fft_gentleman_sande_radix_2(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in 0..log {
        let backet_width = deg >> i;
        let half_width = backet_width >> 1;
        // W = exp(2PI/N), N = backet_width
        let root = Complex::from_polar(1.0, -2.0 * std::f64::consts::PI / backet_width as f64);
        for base in (0..deg).step_by(backet_width) {
            let mut w: Complex = 1.0.into();
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
        }
    }
}

pub fn ifft_gentleman_sande_radix_2(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in 0..log {
        let backet_width = deg >> i;
        let half_width = backet_width >> 1;
        // W = exp(2PI/N), N = backet_width
        let root = Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / backet_width as f64);
        for base in (0..deg).step_by(backet_width) {
            let mut w: Complex = 1.0.into();
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
            a[i] = a[i].conjugate();
            a[i] /= deg as f64;
            if i != rev_i {
                a[rev_i] = a[rev_i].conjugate();
                a[rev_i] /= deg as f64;
            }
        }
    }
}

pub fn fft_cooley_tukey_radix_2(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
        }
    }

    for i in 0..log {
        let backet_width = 1 << (i+1);
        let half_width = backet_width >> 1;
        // W = exp(-2PI/N), N = backet_width
        let root = Complex::from_polar(1.0, -2.0 * std::f64::consts::PI / backet_width as f64);
        for base in (0..deg).step_by(backet_width) {
            let mut w: Complex = 1.0.into();
            for k in base..base+half_width {
                let (w0, w1) = (a[k] + a[k+half_width] * w, a[k] - a[k+half_width] * w);

                a[k] = w0;
                a[k+half_width] = w1;
                w *= root;
            }
        }
    }
}

pub fn ifft_cooley_tukey_radix_2(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
        }
    }

    for i in 0..log {
        let backet_width = 1 << (i+1);
        let half_width = backet_width >> 1;
        // W = exp(2PI/N), N = backet_width
        let root = Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / backet_width as f64);
        for base in (0..deg).step_by(backet_width) {
            let mut w: Complex = 1.0.into();
            for k in base..base+half_width {
                let (w0, w1) = (a[k] + a[k+half_width] * w, a[k] - a[k+half_width] * w);

                a[k] = w0;
                a[k+half_width] = w1;
                w *= root;
            }
        }
    }

    for i in 0..deg {
        a[i] = a[i].conjugate();
        a[i] /= deg as f64;
    }
}

pub fn fft_gentleman_sande_radix_4(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros();
    debug_assert_eq!(a.len(), 1 << log);

    for i in (0..log).step_by(2) {
        let backet_width = deg >> i;
        let root = Complex::from_polar(1.0, -2.0 * std::f64::consts::PI / backet_width as f64);
        if i + 1 == log {
            let half_width = backet_width >> 1;
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0f64.into();
                for k in base..base+half_width {
                    let (w0, w1) = (a[k] + a[k+half_width], a[k] - a[k+half_width]);

                    a[k] = w0;
                    a[k+half_width] = w1 * w;
                    w *= root;
                }
            }
        } else {
            let quarter = backet_width >> 2;
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0f64.into();
                for k in base..base+quarter {
                    let (c0, c1, c2, c3) = (a[k], a[k+quarter], a[k+quarter*2], a[k+quarter*3]);

                    // If W = exp(-2PIi/N), then
                    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
                    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1  -i  -1   i | => | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
                    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
                    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1   i  -1  -i |    | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
                    let (w0, w1, w2, w3) = 
                        (
                            Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
                            Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real()),
                            Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
                            Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real())
                        );

                    a[k] = w0;
                    let mut nw = w;
                    a[k+quarter*2] = w1 * nw;
                    nw *= w;
                    a[k+quarter] = w2 * nw;
                    nw *= w;
                    a[k+quarter*3] = w3 * nw;
                    w *= root;
                }
            }
        }
    }

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) as u32 - log);
        if i <= rev_i {
            a.swap(i, rev_i);
        }
    }
}

pub fn ifft_gentleman_sande_radix_4(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros();
    debug_assert_eq!(a.len(), 1 << log);

    for i in (0..log).step_by(2) {
        // Split backet_num (deg / backet_num)-order DFT into (deg / backet_num / 2 or 4)-order DFT.
        let backet_width = deg >> i;
        let root = Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / backet_width as f64);
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
            let quarter = backet_width >> 2;
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0f64.into();
                for k in base..base+quarter {
                    let (c0, c1, c2, c3) = (a[k], a[k+quarter], a[k+quarter*2], a[k+quarter*3]);
                    // If W = exp(2PIi/N), then
                    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
                    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1   i  -1  -i | => | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
                    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
                    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1  -i  -1   i |    | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
                    let (w0, w1, w2, w3) = 
                        (
                            Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
                            Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real()),
                            Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
                            Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real())
                        );

                    a[k] = w0;
                    let mut nw = w;
                    a[k+quarter*2] = w1 * nw;
                    nw *= w;
                    a[k+quarter] = w2 * nw;
                    nw *= w;
                    a[k+quarter*3] = w3 * nw;
                    w *= root;
                }
            }
        }
    }

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) as u32 - log);
        if i <= rev_i {
            a.swap(i, rev_i);
            a[i] = a[i].conjugate();
            a[i] /= deg as f64;
            if i != rev_i {
                a[rev_i] = a[rev_i].conjugate();
                a[rev_i] /= deg as f64;
            }
        }
    }
}

pub fn fft_cooley_tukey_radix_4(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
        }
    }

    for i in (0..log).step_by(2) {
        if i + 1 == log {
            let backet_width = 1 << (i+1);
            let half_width = backet_width >> 1;
            // W = exp(-2PI/N), N = backet_width
            let root = Complex::from_polar(1.0, -2.0 * std::f64::consts::PI / backet_width as f64);
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0.into();
                for k in base..base+half_width {
                    let (w0, w1) = (a[k] + a[k+half_width] * w, a[k] - a[k+half_width] * w);
    
                    a[k] = w0;
                    a[k+half_width] = w1;
                    w *= root;
                }
            }
        } else {
            let backet_width = 1 << (i+2);
            let quarter = backet_width >> 2;
            // W = exp(-2PI/N), N = backet_width
            let root = Complex::from_polar(1.0, -2.0 * std::f64::consts::PI / backet_width as f64);
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0.into();
                for k in base..base+quarter {
                    let (c0, mut c1, mut c2, mut c3) = (a[k], a[k+quarter*2], a[k+quarter], a[k+quarter*3]);
                    let mut nw = w;
                    c1 *= nw;
                    nw *= w;
                    c2 *= nw;
                    nw *= w;
                    c3 *= nw;

                    // If W = exp(-2PIi/N), then
                    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
                    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1  -i  -1   i | => | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
                    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
                    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1   i  -1  -i |    | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
                    let (w0, w1, w2, w3) = 
                        (
                            Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
                            Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real()),
                            Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
                            Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real())
                        );

                    a[k] = w0;
                    a[k+quarter] = w1;
                    a[k+quarter*2] = w2;
                    a[k+quarter*3] = w3;
                    w *= root;
                }
            }
        }
    }
}

pub fn ifft_cooley_tukey_radix_4(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in 0..deg {
        let rev_i = i.reverse_bits() >> ((std::mem::size_of::<usize>() << 3) - log);
        if i <= rev_i {
            a.swap(i, rev_i);
        }
    }

    for i in (0..log).step_by(2) {
        if i + 1 == log {
            let backet_width = 1 << (i+1);
            let half_width = backet_width >> 1;
            // W = exp(-2PI/N), N = backet_width
            let root = Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / backet_width as f64);
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0.into();
                for k in base..base+half_width {
                    let (w0, w1) = (a[k] + a[k+half_width] * w, a[k] - a[k+half_width] * w);
    
                    a[k] = w0;
                    a[k+half_width] = w1;
                    w *= root;
                }
            }
        } else {
            let backet_width = 1 << (i+2);
            let quarter = backet_width >> 2;
            // W = exp(-2PI/N), N = backet_width
            let root = Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / backet_width as f64);
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0.into();
                for k in base..base+quarter {
                    let (c0, mut c1, mut c2, mut c3) = (a[k], a[k+quarter*2], a[k+quarter], a[k+quarter*3]);
                    let mut nw = w;
                    c1 *= nw;
                    nw *= w;
                    c2 *= nw;
                    nw *= w;
                    c3 *= nw;

                    // If W = exp(2PIi/N), then
                    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
                    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1   i  -1  -i | => | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
                    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
                    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1  -i  -1   i |    | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
                    let (w0, w1, w2, w3) = 
                        (
                            Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
                            Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real()),
                            Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
                            Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real())
                        );

                    a[k] = w0;
                    a[k+quarter] = w1;
                    a[k+quarter*2] = w2;
                    a[k+quarter*3] = w3;
                    w *= root;
                }
            }
        }
    }

    a.iter_mut().for_each(|c| *c = Complex::new(c.real() / deg as f64, -c.imag() / deg as f64));
}

pub fn fft_gentleman_sande_radix_4_without_bitreverse(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros();
    debug_assert_eq!(a.len(), 1 << log);

    for i in (0..log).step_by(2) {
        // Split backet_num (deg / backet_num)-order DFT into (deg / backet_num / 2 or 4)-order DFT.
        let backet_width = deg >> i;
        let root = Complex::from_polar(1.0, -2.0 * std::f64::consts::PI / backet_width as f64);
        if i + 1 == log {
            let half_width = backet_width >> 1;
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0f64.into();
                for k in base..base+half_width {
                    let (w0, w1) = (a[k] + a[k+half_width], a[k] - a[k+half_width]);

                    a[k] = w0;
                    a[k+half_width] = w1 * w;
                    w *= root;
                }
            }
        } else {
            let quarter = backet_width >> 2;
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0f64.into();
                for k in base..base+quarter {
                    let (c0, c1, c2, c3) = (a[k], a[k+quarter], a[k+quarter*2], a[k+quarter*3]);

                    // If W = exp(-2PIi/N), then
                    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
                    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1  -i  -1   i | => | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
                    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
                    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1   i  -1  -i |    | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
                    let (w0, w1, w2, w3) = 
                        (
                            Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
                            Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real()),
                            Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
                            Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real())
                        );

                    a[k] = w0;
                    let mut nw = w;
                    a[k+quarter*2] = w1 * nw;
                    nw *= w;
                    a[k+quarter] = w2 * nw;
                    nw *= w;
                    a[k+quarter*3] = w3 * nw;
                    w *= root;
                }
            }
        }
    }
}

pub fn ifft_cooley_tukey_radix_4_without_bitreverse(a: &mut [Complex<f64>]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);

    for i in (0..log).step_by(2) {
        if i + 1 == log {
            let backet_width = 1 << (i+1);
            let half_width = backet_width >> 1;
            // W = exp(2PI/N), N = backet_width
            let root = Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / backet_width as f64);
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0.into();
                for k in base..base+half_width {
                    let (w0, w1) = (a[k] + a[k+half_width] * w, a[k] - a[k+half_width] * w);
    
                    a[k] = w0;
                    a[k+half_width] = w1;
                    w *= root;
                }
            }
        } else {
            let backet_width = 1 << (i+2);
            let quarter = backet_width >> 2;
            // W = exp(2PI/N), N = backet_width
            let root = Complex::from_polar(1.0, 2.0 * std::f64::consts::PI / backet_width as f64);
            for base in (0..deg).step_by(backet_width) {
                let mut w: Complex = 1.0.into();
                for k in base..base+quarter {
                    let (c0, mut c1, mut c2, mut c3) = (a[k], a[k+quarter*2], a[k+quarter], a[k+quarter*3]);
                    let mut nw = w;
                    c1 *= nw;
                    nw *= w;
                    c2 *= nw;
                    nw *= w;
                    c3 *= nw;

                    // If W = exp(2PIi/N), then
                    // | W^0  W^0  W^0  W^0 |   | W^0  W^0  W^0  W^0 |   | 1   1   1   1 |    | c0 + c1 + c2 + c3                                                                   |
                    // | W^0  W^1  W^2  W^3 | = | W^0  W^1  W^2  W^3 | = | 1   i  -1  -i | => | c0 + Complex::new(-c1.imag(), c1.real()) - c2 - Complex::new(-c3.imag(), c3.real()) |
                    // | W^0  W^2  W^4  W^6 |   | W^0  W^2  W^0  W^2 |   | 1  -1   1  -1 |    | c0 - c1 + c2 - c3                                                                   |
                    // | W^0  W^3  W^6  W^9 |   | W^0  W^3  W^2  W^1 |   | 1  -i  -1   i |    | c0 - Complex::new(-c1.imag(), c1.real()) - c2 + Complex::new(-c3.imag(), c3.real()) |
                    let (w0, w1, w2, w3) = 
                        (
                            Complex::new(c0.real() + c1.real() + c2.real() + c3.real(), c0.imag() + c1.imag() + c2.imag() + c3.imag()),
                            Complex::new(c0.real() - c1.imag() - c2.real() + c3.imag(), c0.imag() + c1.real() - c2.imag() - c3.real()),
                            Complex::new(c0.real() - c1.real() + c2.real() - c3.real(), c0.imag() - c1.imag() + c2.imag() - c3.imag()),
                            Complex::new(c0.real() + c1.imag() - c2.real() - c3.imag(), c0.imag() - c1.real() - c2.imag() + c3.real())
                        );

                    a[k] = w0;
                    a[k+quarter] = w1;
                    a[k+quarter*2] = w2;
                    a[k+quarter*3] = w3;
                    w *= root;
                }
            }
        }
    }

    a.iter_mut().for_each(|c| *c = Complex::new(c.real() / deg as f64, -c.imag() / deg as f64));
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
    
    fft_gentleman_sande_radix_4_without_bitreverse(&mut a2);
    fft_gentleman_sande_radix_4_without_bitreverse(&mut b2);

    a2
        .iter_mut()
        .zip(b2.into_iter())
        .for_each(|(l, r)| *l *= r);
    ifft_cooley_tukey_radix_4_without_bitreverse(&mut a2);
    
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
                 
type Mint998244353 = Mint<Mod998244353>;

// Only usable 998244353 for modulo.
fn ntt(a: &mut Vec<Mint998244353>, inv: bool) {
    let n = a.len();
    assert!(n == 1 << n.trailing_zeros());
    if n == 1 {
        return;
    }
    let root = Mint998244353::nth_root(n as i64 * if inv { -1 } else { 1 });
    let mut roots = vec![Mint998244353::one(); n/2+1];
    
    for i in 0..n/2 {
        roots[i+1] = roots[i] * root;
    }
    
    let mut b = vec![Mint998244353::zero(); n];
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

pub fn convolution(a: &Vec<Mint998244353>, b: &Vec<Mint998244353>) -> Vec<Mint998244353> {
    let mut n = 1;
    let deg = a.len() + b.len() - 1;
    while n < deg {
        n <<= 1;
    }
    
    let mut na = a.clone();
    let mut nb = b.clone();
    na.resize(n, Mint998244353::new(0));
    nb.resize(n, Mint998244353::new(0));
    ntt(&mut na, false);
    ntt(&mut nb, false);
    
    let mut nc = na
        .into_iter()
        .zip(nb.into_iter())
        .map(|(l, r)| l * r)
        .collect::<Vec<_>>();
    ntt(&mut nc, true);
    
    let ninv = Mint998244353::new(n as i64).inv();
    nc[0..deg]
        .into_iter()
        .map(|v| *v * ninv)
        .collect()
}


#[cfg(test)]
mod tests {
    use complex::Complex;
    use super::{
        fft_gentleman_sande_radix_2, ifft_gentleman_sande_radix_2,
        fft_gentleman_sande_radix_4, ifft_gentleman_sande_radix_4,
        fft_cooley_tukey_radix_2, ifft_cooley_tukey_radix_2,
        fft_cooley_tukey_radix_4, ifft_cooley_tukey_radix_4,
        fft_gentleman_sande_radix_4_without_bitreverse, ifft_cooley_tukey_radix_4_without_bitreverse,
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
    fn gentleman_sande_radix_2_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_2(&mut data1);
        ifft_gentleman_sande_radix_2(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn cooley_tukey_radix_2_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        fft_cooley_tukey_radix_2(&mut data1);
        ifft_cooley_tukey_radix_2(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn gentleman_sande_cooley_tukey_radix_2_compare_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1: Vec<Complex> = data.clone();
        let mut data2 = data.clone();
        fft_gentleman_sande_radix_2(&mut data1);
        fft_cooley_tukey_radix_2(&mut data2);
        let diff_max = calc_diff(&data1, &data2);
        assert!(diff_max < 1e-10);
        
        ifft_gentleman_sande_radix_2(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);

        ifft_cooley_tukey_radix_2(&mut data2);
        let diff_max = calc_diff(&data, &data2);
        assert!(diff_max < 1e-10);
    }
    
    #[test]
    fn gentleman_sande_radix_4_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_4(&mut data1);
        ifft_gentleman_sande_radix_4(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn cooley_tukey_radix_4_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        fft_cooley_tukey_radix_4(&mut data1);
        ifft_cooley_tukey_radix_4(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);
    }

    
    #[test]
    fn gentleman_sande_radix_2_radix_4_compare_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        let mut data2 = data.clone();
        fft_gentleman_sande_radix_2(&mut data1);
        fft_gentleman_sande_radix_4(&mut data2);
        let diff_max = calc_diff(&data1, &data2);
        assert!(diff_max < 1e-10);
        
        ifft_gentleman_sande_radix_2(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);

        ifft_gentleman_sande_radix_4(&mut data2);
        let diff_max = calc_diff(&data, &data2);
        assert!(diff_max < 1e-10);
    }


    #[test]
    fn cooley_tukey_radix_2_radix_4_compare_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        let mut data2 = data.clone();
        fft_cooley_tukey_radix_2(&mut data1);
        fft_cooley_tukey_radix_4(&mut data2);
        let diff_max = calc_diff(&data1, &data2);
        assert!(diff_max < 1e-10);
        
        ifft_cooley_tukey_radix_2(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);

        ifft_cooley_tukey_radix_4(&mut data2);
        let diff_max = calc_diff(&data, &data2);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn gentleman_sande_cooley_tukey_radix_4_compare_test() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        let mut data2 = data.clone();
        fft_gentleman_sande_radix_4(&mut data1);
        fft_cooley_tukey_radix_4(&mut data2);
        let diff_max = calc_diff(&data1, &data2);
        assert!(diff_max < 1e-10);
        
        ifft_gentleman_sande_radix_4(&mut data1);
        let diff_max = calc_diff(&data, &data1);
        assert!(diff_max < 1e-10);

        ifft_cooley_tukey_radix_4(&mut data2);
        let diff_max = calc_diff(&data, &data2);
        assert!(diff_max < 1e-10);
    }

    #[test]
    fn cooley_tukey_radix_4_test_without_bitreverse() {
        let data: Vec<Complex> = vec![
            1.0.into(), 2.0.into(), 3.0.into(), 4.0.into(), 5.0.into(), 6.0.into(), 7.0.into(), 8.0.into(),
            9.0.into(), 10.0.into(), 11.0.into(), 12.0.into(), 13.0.into(), 14.0.into(), 15.0.into(), 16.0.into()];
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_4_without_bitreverse(&mut data1);
        ifft_cooley_tukey_radix_4_without_bitreverse(&mut data1);
        let diff_max = calc_diff(&data, &data1);
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