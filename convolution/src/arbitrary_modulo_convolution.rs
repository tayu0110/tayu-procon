use super::convolution;
use montgomery_modint::{
    Mod645922817, Mod754974721, Mod880803841, Mod897581057, Mod998244353, Modulo, MontgomeryModint,
};

type Modint<M> = MontgomeryModint<M>;

pub fn arbitrary_convolution<const M: u64>(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let c1 = convolution::<Mod880803841>(a.clone(), b.clone());
    let c2 = convolution::<Mod897581057>(a.clone(), b.clone());
    let c3 = convolution::<Mod998244353>(a, b);

    const P: [u64; 3] = [
        Mod880803841::N as u64,
        Mod897581057::N as u64,
        Mod998244353::N as u64,
    ];
    const P1P2: u64 = P[0] * P[1] % P[2];
    let p1p2mod: u64 = P[0] * P[1] % M;
    let p1i = Modint::<Mod897581057>::new(P[0] as u32).inv().val() as u64;
    let p2i = Modint::<Mod998244353>::new(P1P2 as u32).inv().val() as u64;
    c1.into_iter()
        .zip(c2.into_iter().zip(c3))
        .map(|(c1, (c2, c3))| {
            let t1 = (c2 as u64 + P[1] - c1 as u64) * p1i % P[1];
            let res2 = (c1 as u64 + t1 * P[0]) % P[2];
            let res3 = (c1 as u64 + t1 * P[0]) % M;
            let t2 = (c3 as u64 + P[2] - res2) * p2i % P[2];
            ((res3 + t2 * p1p2mod) % M) as u32
        })
        .collect()
}

pub fn convolution_1e97(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let c1 = convolution::<Mod880803841>(a.clone(), b.clone());
    let c2 = convolution::<Mod897581057>(a.clone(), b.clone());
    let c3 = convolution::<Mod998244353>(a, b);

    const MOD: u64 = 1_000_000_007;
    const P: [u64; 3] = [
        Mod880803841::N as u64,
        Mod897581057::N as u64,
        Mod998244353::N as u64,
    ];
    const P1P2: u64 = P[0] * P[1] % P[2];
    const P1P2MOD: u64 = P[0] * P[1] % MOD;
    let p1i = Modint::<Mod897581057>::new(P[0] as u32).inv().val() as u64;
    let p2i = Modint::<Mod998244353>::new(P1P2 as u32).inv().val() as u64;
    c1.into_iter()
        .zip(c2.into_iter().zip(c3))
        .map(|(c1, (c2, c3))| {
            let t1 = (c2 as u64 + P[1] - c1 as u64) * p1i % P[1];
            let res2 = (c1 as u64 + t1 * P[0]) % P[2];
            let res3 = (c1 as u64 + t1 * P[0]) % MOD;
            let t2 = (c3 as u64 + P[2] - res2) * p2i % P[2];
            ((res3 + t2 * P1P2MOD) % MOD) as u32
        })
        .collect()
}

pub fn convolution_mod_2_64(a: Vec<u64>, b: Vec<u64>) -> Vec<u64> {
    let c1 = convolution::<Mod645922817>(
        a.iter()
            .cloned()
            .map(|a| (a % Mod645922817::N as u64) as u32)
            .collect(),
        b.iter()
            .cloned()
            .map(|b| (b % Mod645922817::N as u64) as u32)
            .collect(),
    );
    let c2 = convolution::<Mod754974721>(
        a.iter()
            .cloned()
            .map(|a| (a % Mod754974721::N as u64) as u32)
            .collect(),
        b.iter()
            .cloned()
            .map(|b| (b % Mod754974721::N as u64) as u32)
            .collect(),
    );
    let c3 = convolution::<Mod880803841>(
        a.iter()
            .cloned()
            .map(|a| (a % Mod880803841::N as u64) as u32)
            .collect(),
        b.iter()
            .cloned()
            .map(|b| (b % Mod880803841::N as u64) as u32)
            .collect(),
    );
    let c4 = convolution::<Mod897581057>(
        a.iter()
            .cloned()
            .map(|a| (a % Mod897581057::N as u64) as u32)
            .collect(),
        b.iter()
            .cloned()
            .map(|b| (b % Mod897581057::N as u64) as u32)
            .collect(),
    );
    let c5 = convolution::<Mod998244353>(
        a.into_iter()
            .map(|a| (a % Mod998244353::N as u64) as u32)
            .collect(),
        b.into_iter()
            .map(|b| (b % Mod998244353::N as u64) as u32)
            .collect(),
    );

    const P: [u64; 5] = [
        Mod645922817::N as u64,
        Mod754974721::N as u64,
        Mod880803841::N as u64,
        Mod897581057::N as u64,
        Mod998244353::N as u64,
    ];
    const PROD01: u64 = P[0].wrapping_mul(P[1]);
    const PROD012: u64 = PROD01.wrapping_mul(P[2]);
    const PROD0123: u64 = PROD012.wrapping_mul(P[3]);
    const P0P1: u64 = P[0] * P[1] % P[2];
    const P0P1P2: u64 = P[0] * P[1] % P[3] * P[2] % P[3];
    const P0P1P2P3: u64 = P[0] * P[1] % P[4] * P[2] % P[4] * P[3] % P[4];
    let pi = [
        Modint::<Mod754974721>::new(P[0] as u32).inv().val() as u64,
        Modint::<Mod880803841>::from(P0P1).inv().val() as u64,
        Modint::<Mod897581057>::from(P0P1P2).inv().val() as u64,
        Modint::<Mod998244353>::from(P0P1P2P3).inv().val() as u64,
    ];
    let mut res = vec![];
    for i in 0..c1.len() {
        let t0 = c1[i] as u64;
        let mut w = [t0; 5];
        let mut prod = [P[0]; 5];
        for (j, c) in vec![c2[i], c3[i], c4[i], c5[i]].into_iter().enumerate() {
            let t = ((c + P[j + 1] as u32 - w[j + 1] as u32) as u64 * pi[j]) % P[j + 1];
            for (k, &p) in P.iter().enumerate().skip(j + 2) {
                w[k] = (w[k] + (t * prod[k])) % p;
                prod[k] = (prod[k] * P[j + 1]) % p;
            }
            w[j] = t;
        }

        res.push(
            t0.wrapping_add(w[0].wrapping_mul(Mod645922817::N as u64))
                .wrapping_add(w[1].wrapping_mul(PROD01))
                .wrapping_add(w[2].wrapping_mul(PROD012))
                .wrapping_add(w[3].wrapping_mul(PROD0123)),
        )
    }
    res
}
