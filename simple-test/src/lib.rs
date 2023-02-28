use std::cell::RefCell;

use simple_rand::*;

thread_local! {
    static RND32: RefCell<Box<dyn Iterator<Item = u32>>> = RefCell::new(Box::new(xor_shift32(gen_seed())));
    static RND64: RefCell<Box<dyn Iterator<Item = u64>>> = RefCell::new(Box::new(xor_shift(gen_seed())));
    static RND128: RefCell<Box<dyn Iterator<Item = u128>>> = RefCell::new(Box::new(xor_shift128(gen_seed())));
}

fn get_u32() -> u32 { RND32.with(|rnd| rnd.borrow_mut().next().unwrap()) }
fn get_u64() -> u64 { RND64.with(|rnd| rnd.borrow_mut().next().unwrap()) }
fn get_u128() -> u128 { RND128.with(|rnd| rnd.borrow_mut().next().unwrap()) }
