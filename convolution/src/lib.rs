mod common;
mod fft_cache;
pub mod cooley_tukey;
pub mod gentleman_sande;

use fft_cache::FftCache;
use gentleman_sande::{
    gentleman_sande_radix_4_butterfly,
    gentleman_sande_radix_4_butterfly_f32,
    gentleman_sande_radix_4_butterfly_modint
    // gentleman_sande_radix_2_butterfly_modint
};
use cooley_tukey::{
    cooley_tukey_radix_4_butterfly_inv,
    cooley_tukey_radix_4_butterfly_inv_f32,
    cooley_tukey_radix_4_butterfly_inv_modint
    // cooley_tukey_radix_2_butterfly_inv_modint
};

use complex::Complex;
use modint::{
    Mint, Mod998244353
};

pub fn convolution_f64(a: &Vec<f64>, b: &Vec<f64>) -> Vec<f64> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;
    
    let mut a2 = vec![Complex::from(0.0); n];
    a.into_iter()
        .zip(a2.iter_mut())
        .for_each(|(v, w)| *w = (*v).into());
    
    let mut b2 = vec![Complex::from(0.0); n];
    b.into_iter()
        .zip(b2.iter_mut())
        .for_each(|(v, w)| *w = (*v).into());

    let cache = FftCache::<Complex>::new(log);
    
    unsafe {
        gentleman_sande_radix_4_butterfly(n, log, &mut a2, &cache);
        gentleman_sande_radix_4_butterfly(n, log, &mut b2, &cache);
    }

    a2
        .iter_mut()
        .zip(b2.into_iter())
        .for_each(|(l, r)| *l *= r);
    unsafe {
        cooley_tukey_radix_4_butterfly_inv(n, log, &mut a2, &cache);
    }
    
    a2[0..deg]
        .into_iter()
        .map(|v| v.real() / n as f64)
        .collect()
}

pub fn convolution_f32(a: &Vec<f32>, b: &Vec<f32>) -> Vec<f32> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;
    
    let mut a2 = vec![Complex::from(0.0); n];
    a.into_iter()
        .zip(a2.iter_mut())
        .for_each(|(v, w)| *w = (*v).into());
    
    let mut b2 = vec![Complex::from(0.0); n];
    b.into_iter()
        .zip(b2.iter_mut())
        .for_each(|(v, w)| *w = (*v).into());
    
    let cache = FftCache::<Complex<f32>>::new(log);

    unsafe {
        gentleman_sande_radix_4_butterfly_f32(n, log, &mut a2, &cache);
        gentleman_sande_radix_4_butterfly_f32(n, log, &mut b2, &cache);
    }

    a2
        .iter_mut()
        .zip(b2.into_iter())
        .for_each(|(l, r)| *l *= r);
    unsafe {
        cooley_tukey_radix_4_butterfly_inv_f32(n, log, &mut a2, &cache);
    }
    
    a2[0..deg]
        .into_iter()
        .map(|v| v.real() / n as f32)
        .collect()
}
                 
type Mint998244353 = Mint<Mod998244353>;

// Only usable 998244353 for modulo.
// fn ntt(a: &mut Vec<Mint998244353>, inv: bool) {
//     let n = a.len();
//     assert!(n == 1 << n.trailing_zeros());
//     if n == 1 {
//         return;
//     }
//     let root = Mint998244353::nth_root(n as i64 * if inv { -1 } else { 1 });
//     let mut roots = vec![Mint998244353::one(); n/2+1];
    
//     for i in 0..n/2 {
//         roots[i+1] = roots[i] * root;
//     }
    
//     let mut b = vec![Mint998244353::zero(); n];
//     for (w, i) in (0..n.trailing_zeros()).map(|v| 1 << v).zip((0..n.trailing_zeros()).rev().map(|v| 1 << v)) {
//         for j in 0..i {
//             for k in 0..w {
//                 b[k+((w*j)<<1)] = a[k+w*j] + a[k+w*j+(n>>1)];
//                 b[k+((w*j)<<1)+w] = roots[w*j] * (a[k+w*j] - a[k+w*j+(n>>1)]);
//             }
//         }
//         std::mem::swap(a, &mut b);
//     }
// }

pub fn convolution(a: &Vec<Mint998244353>, b: &Vec<Mint998244353>) -> Vec<Mint998244353> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;
    
    let mut na = a.clone();
    let mut nb = b.clone();
    na.resize(n, Mint998244353::zero());
    nb.resize(n, Mint998244353::zero());

    let cache = FftCache::<Mint998244353>::new(log);

    unsafe {
        gentleman_sande_radix_4_butterfly_modint(n, log, &mut na, &cache);
        gentleman_sande_radix_4_butterfly_modint(n, log, &mut nb, &cache);
    }

    // ntt(&mut na, false);
    // ntt(&mut nb, false);
    
    na.iter_mut()
        .zip(nb.into_iter())
        .for_each(|(a, b)| *a *= b);
    unsafe {
        cooley_tukey_radix_4_butterfly_inv_modint(n, log, &mut na, &cache);
    }
    // cooley_tukey_radix_2_butterfly_inv_modint(n, log, &mut na, &cache);

    // let mut nc = na
    //     .into_iter()
    //     .zip(nb.into_iter())
    //     .map(|(l, r)| l * r)
    //     .collect::<Vec<_>>();
    // ntt(&mut nc, true);
    
    let ninv = Mint998244353::new(n as i64).inv();
    na[0..deg]
        .into_iter()
        .map(|v| *v * ninv)
        .collect()
    // nc[0..deg]
    //     .into_iter()
    //     .map(|v| *v * ninv)
    //     .collect()
}


#[cfg(test)]
mod tests {
    use complex::Complex;
    use modint::{
        Mint, Mod998244353
    };
    use super::{
        gentleman_sande::{
            fft_gentleman_sande_radix_2, ifft_gentleman_sande_radix_2,
            fft_gentleman_sande_radix_4, ifft_gentleman_sande_radix_4
        },
        cooley_tukey::{
            fft_cooley_tukey_radix_2, ifft_cooley_tukey_radix_2,
            fft_cooley_tukey_radix_4, ifft_cooley_tukey_radix_4
        },
        convolution_f64,
        convolution
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
    fn convolution_test() {
        let a = vec![1.0, 2.0, 3.0, 4.0];
        let b = vec![1.0, 2.0, 4.0, 8.0];

        let c = convolution_f64(&a, &b);
        let c = c.into_iter().map(|c| c.round() as i32).collect::<Vec<_>>();
        assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);

        type Mint998244353 = Mint<Mod998244353>;
        let a = vec![Mint998244353::raw(1), Mint998244353::raw(2), Mint998244353::raw(3), Mint998244353::raw(4)];
        let b = vec![Mint998244353::raw(1), Mint998244353::raw(2), Mint998244353::raw(4), Mint998244353::raw(8)];
        let c = convolution(&a, &b);
        assert_eq!(c, vec![Mint::raw(1), Mint::raw(4), Mint::raw(11), Mint::raw(26), Mint::raw(36), Mint::raw(40), Mint::raw(32)]);
    }
}