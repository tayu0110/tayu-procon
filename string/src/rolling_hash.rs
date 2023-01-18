use std::cell::RefCell;
use std::time::SystemTime;

const CHARS: u64 = 1 << 8;
const MOD: u64 = (1 << 61) - 1;
const RT: u64 = 37;

thread_local! {
    static BASE: RefCell<u64> = RefCell::new(0);
}

fn mul(a: u64, b: u64) -> u64 {
    let t = a as u128 * b as u128;
    let t = (t >> 61) as u64 + (t as u64 & MOD);
    if t >= MOD {
        t - MOD
    } else {
        t
    }
}

fn mod_pow(a: u64, mut n: u64) -> u64 {
    let (mut res, mut pow) = (1, a);
    while n != 0 {
        if n & 1 != 0 {
            res = mul(res, pow);
        }
        pow = mul(pow, pow);
        n >>= 1;
    }
    res
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b > 0 {
        a %= b;
        std::mem::swap(&mut a, &mut b);
    }
    a
}

fn get_rand() -> u64 {
    let mut ns = (SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos() % (MOD - 1) as u128) as u64 + 1;
    while gcd(ns, MOD - 1) != 1 {
        ns = (SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos() % (MOD - 1) as u128) as u64 + 1;
    }
    ns
}

fn get_base() -> u64 {
    BASE.with(|base| {
        if *base.borrow() == 0 {
            loop {
                let res = mod_pow(RT, get_rand());
                if res > CHARS {
                    *base.borrow_mut() = res;
                    break;
                }
            }
        }
        base.borrow().clone()
    })
}

pub struct RollingHash<'a> {
    _base: u64,
    hash: Vec<u64>,
    pow: &'a [u64],
}

impl<'a> RollingHash<'a> {
    #[inline]
    pub fn new(s: &str, pow: &'a [u64]) -> Self {
        let base = get_base();
        let mut hash = vec![0; s.len() + 1];

        for (i, c) in s.bytes().enumerate() {
            hash[i + 1] = c as u64 + mul(hash[i], base);
            if hash[i + 1] >= MOD {
                hash[i + 1] -= MOD;
            }
        }

        Self { _base: base, hash, pow }
    }

    #[inline]
    /// return the hash of s[l..r)
    pub fn get_hash(&self, l: usize, r: usize) -> u64 {
        let (res, f) = self.hash[r].overflowing_sub(mul(self.hash[l], self.pow[r - l]));
        if f {
            res.wrapping_add(MOD)
        } else {
            res
        }
    }
}

static mut POW_CACHE: Vec<u64> = Vec::new();

pub fn prepare(size: usize) -> impl Fn(&str) -> RollingHash {
    let base = get_base();

    let pow = unsafe {
        POW_CACHE = vec![0; size + 1];
        POW_CACHE[0] = 1;
        for i in 0..size {
            POW_CACHE[i + 1] = mul(POW_CACHE[i], base);
        }

        &POW_CACHE
    };

    move |s: &str| -> RollingHash { RollingHash::new(s, pow) }
}
