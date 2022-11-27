mod common;
pub mod cooley_tukey;
mod fft_cache;
pub mod gentleman_sande;

use cooley_tukey::{
    cooley_tukey_radix_4_butterfly_inv, cooley_tukey_radix_4_butterfly_inv_f32,
    cooley_tukey_radix_8_butterfly_inv_montgomery_modint,
};
use fft_cache::FftCache;
use gentleman_sande::{
    gentleman_sande_radix_4_butterfly, gentleman_sande_radix_4_butterfly_f32,
    gentleman_sande_radix_8_butterfly_montgomery_modint,
};

use complex::Complex;
use modint::{Mod998244353, MontgomeryModint};

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

    gentleman_sande_radix_4_butterfly(n, log, &mut a2, &cache);
    gentleman_sande_radix_4_butterfly(n, log, &mut b2, &cache);

    a2.iter_mut().zip(b2.into_iter()).for_each(|(l, r)| *l *= r);

    cooley_tukey_radix_4_butterfly_inv(n, log, &mut a2, &cache);

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

    gentleman_sande_radix_4_butterfly_f32(n, log, &mut a2, &cache);
    gentleman_sande_radix_4_butterfly_f32(n, log, &mut b2, &cache);

    a2.iter_mut().zip(b2.into_iter()).for_each(|(l, r)| *l *= r);

    cooley_tukey_radix_4_butterfly_inv_f32(n, log, &mut a2, &cache);

    a2[0..deg]
        .into_iter()
        .map(|v| v.real() / n as f32)
        .collect()
}

type Mint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;

pub fn convolution(mut a: Vec<Mint998244353>, mut b: Vec<Mint998244353>) -> Vec<Mint998244353> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;

    a.resize(n, Mint998244353::zero());
    b.resize(n, Mint998244353::zero());

    let cache = FftCache::<Mint998244353>::new(log);

    gentleman_sande_radix_8_butterfly_montgomery_modint(n, log, &mut a, &cache);
    gentleman_sande_radix_8_butterfly_montgomery_modint(n, log, &mut b, &cache);

    a.iter_mut().zip(b.into_iter()).for_each(|(a, b)| *a *= b);

    cooley_tukey_radix_8_butterfly_inv_montgomery_modint(n, log, &mut a, &cache);

    let ninv = Mint998244353::new(n as u32).inv();
    a.resize(deg, Mint998244353::zero());
    a.iter_mut().for_each(|v| *v *= ninv);
    a
}

#[cfg(test)]
mod tests {
    use super::{
        convolution, convolution_f64,
        cooley_tukey::{
            fft_cooley_tukey_radix_2, fft_cooley_tukey_radix_4, ifft_cooley_tukey_radix_2,
            ifft_cooley_tukey_radix_4,
        },
        gentleman_sande::{
            fft_gentleman_sande_radix_2, fft_gentleman_sande_radix_4, ifft_gentleman_sande_radix_2,
            ifft_gentleman_sande_radix_4,
        },
    };
    use complex::Complex;
    use modint::{Mod998244353, MontgomeryModint};

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
    fn gentleman_sande_cooley_tukey_radix_2_compare_test() {
        let data: Vec<Complex> = vec![
            1.0.into(),
            2.0.into(),
            3.0.into(),
            4.0.into(),
            5.0.into(),
            6.0.into(),
            7.0.into(),
            8.0.into(),
            9.0.into(),
            10.0.into(),
            11.0.into(),
            12.0.into(),
            13.0.into(),
            14.0.into(),
            15.0.into(),
            16.0.into(),
        ];
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
    fn gentleman_sande_cooley_tukey_radix_4_compare_test() {
        let data: Vec<Complex> = (1..=16).map(|v| (v as f64).into()).collect();
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

        type Mint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;
        let a = vec![
            Mint998244353::new(1),
            Mint998244353::new(2),
            Mint998244353::new(3),
            Mint998244353::new(4),
        ];
        let b = vec![
            Mint998244353::new(1),
            Mint998244353::new(2),
            Mint998244353::new(4),
            Mint998244353::new(8),
        ];
        let c = convolution(a, b);
        assert_eq!(
            c,
            vec![
                Mint998244353::new(1),
                Mint998244353::new(4),
                Mint998244353::new(11),
                Mint998244353::new(26),
                Mint998244353::new(36),
                Mint998244353::new(40),
                Mint998244353::new(32)
            ]
        );
    }
}
