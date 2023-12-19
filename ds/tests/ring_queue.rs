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

        while nt.pop().is_some() {}
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

        while nt.pop_front().is_some() {}
    });
}

#[test]
fn ring_queue_test() {
    const SIZE: usize = 1 << 5;
    let mut nt = FixedRingQueue::<i32, SIZE>::new();

    assert!(nt.is_empty());

    nt.push(1);
    nt.push(2);
    nt.push(10);
    nt.push(5);

    assert_eq!(nt.len(), 4);
    assert!(!nt.is_full());
    assert_eq!(nt.pop().expect("why queue is empty?"), 1);

    for i in 0..(1 << 5) - 3 {
        nt.push(i);
    }

    assert!(nt.is_full());

    assert_eq!(nt.pop().expect("why queue is empty"), 2);
    assert_eq!(nt.pop().expect("why queue is empty"), 10);
    assert_eq!(nt.pop().expect("why queue is empty"), 5);
    assert_eq!(nt.pop().expect("why queue is empty"), 0);

    while nt.pop().is_some() {}

    assert!(nt.is_empty());
}
