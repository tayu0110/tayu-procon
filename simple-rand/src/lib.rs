use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hasher};

pub fn gen_seed() -> u64 {
    let hasher = RandomState::new().build_hasher();

    hasher.finish()
}

pub fn xor_shift32(seed: u64) -> impl Iterator<Item = u32> {
    let mut random = seed as u32;

    std::iter::repeat_with(move || {
        random ^= random << 13;
        random ^= random >> 17;
        random ^= random << 5;
        random
    })
}

pub fn xor_shift(seed: u64) -> impl Iterator<Item = u64> {
    let mut random = seed;

    std::iter::repeat_with(move || {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        random
    })
}

pub fn xor_shift128(seed: u64) -> impl Iterator<Item = u128> {
    let mut x64 = xor_shift(seed);

    std::iter::repeat_with(move || (x64.next().unwrap() as u128) << 64 | x64.next().unwrap() as u128)
}
