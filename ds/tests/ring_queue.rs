#![feature(test)]
extern crate test;

use ds::FixedRingQueue;
use rand::{thread_rng, Rng};
use std::{collections::VecDeque, sync::Mutex};
use test::Bencher;

const SIZE: usize = 1 << 20;
static QUEUE: Mutex<FixedRingQueue<usize, SIZE>> = Mutex::new(FixedRingQueue::new());

#[bench]
fn ring_queue_bench(b: &mut Bencher) {
    let mut rng = thread_rng();
    let mut nt = QUEUE.lock().unwrap();

    b.iter(|| {
        for _ in 0..SIZE {
            nt.push(rng.gen::<usize>());
        }

        while let Some(_) = nt.pop() {}
    });
}

#[bench]
fn vec_deque_bench(b: &mut Bencher) {
    let mut rng = thread_rng();
    let mut nt = VecDeque::new();

    b.iter(|| {
        for _ in 0..SIZE {
            nt.push_back(rng.gen::<usize>());
        }

        while let Some(_) = nt.pop_front() {}
    });
}
