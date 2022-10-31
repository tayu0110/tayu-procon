type Mint = modint::Mint<modint::Mod998244353>;

// const COMPLEX_ONE: num::Complex<f64> = num::Complex::new(1f64, 0f64);
// const PI2: f64 = std::f64::consts::PI * 2f64;

// #[allow(dead_code)]
// fn fft(a: &mut Vec<num::Complex<f64>>, inv: bool) {
//     let n = a.len();
//     let mut r = num::Complex::from_polar(&1f64, &(PI2 / n as f64));
//     if inv {
//         r = r.inv();
//     }
    
//     let b = &mut vec![num::Complex::default(); n];
//     for i in (0..n.trailing_zeros()).map(|v| 1usize << v).rev() {
//         let z = r.powu(i as u32);
//         let mut z2 = COMPLEX_ONE;
//         for j in (0..n).step_by(i*2) {
//             for k in 0..i {
//                 a[i+j+k] *= z2;
//                 b[j/2+k] = a[j+k] + a[i+j+k];
//                 b[n/2+j/2+k] = a[j+k] - a[i+j+k];
//             }
//             z2 *= z;
//         }
//         std::mem::swap(a, b);
//     }
//     if inv {
//         a.iter_mut().for_each(|now| *now /= num::Complex::new(n as f64, 0f64));
//     }
// }

#[allow(dead_code)]
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

#[allow(dead_code)]
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

// #[allow(dead_code)]
// pub fn fconvolution(a: &Vec<f64>, b: &Vec<f64>) -> Vec<f64> {
//     let deg = a.len() + b.len() - 1;
//     let mut n = 1;
//     while n < deg {
//         n <<= 1;
//     }
    
//     let mut a2 = vec![num::Complex::default(); n];
//     a.into_iter()
//         .enumerate()
//         .for_each(|(i, v)| a2[i] = num::Complex::new(*v, 0f64));
    
//     let mut b2 = vec![num::Complex::default(); n];
//     b.into_iter()
//         .enumerate()
//         .for_each(|(i, v)| b2[i] = num::Complex::new(*v, 0f64));
    
//     fft(&mut a2, false);
//     fft(&mut b2, false);

//     let mut c2 = a2
//         .into_iter()
//         .zip(b2.into_iter())
//         .map(|(l, r)| l * r)
//         .collect::<Vec<_>>();
//     fft(&mut c2, true);
    
//     c2[0..deg]
//         .into_iter()
//         .map(|v| v.re)
//         .collect()
// }

// #[allow(dead_code)]
// pub fn iconvolution(a: &Vec<i64>, b: &Vec<i64>) -> Vec<i64> {
//     let a = a
//         .iter()
//         .map(|v| *v as f64)
//         .collect::<Vec<_>>();
//     let b = b
//         .iter()
//         .map(|v| *v as f64)
//         .collect::<Vec<_>>();
//     fconvolution(&a, &b)
//         .into_iter()
//         .map(|v| v.round() as i64)
//         .collect()
// }