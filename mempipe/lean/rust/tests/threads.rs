//! Run the generated state machines on real threads: one sender, several
//! receivers, random blocking and `Err` choices, and check the ghost logs:
//! every message is accepted exactly once, with its payload and length.
//!
//! The stop counter is harness bookkeeping. It uses only Relaxed operations,
//! which add no synchronization between the threads under test.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use mempipe_lean_model::{Pipe, RPc, Receiver, Sender, Status};

fn rng(seed: u64) -> impl FnMut() -> bool {
    let mut x = seed | 1;
    move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x % 5 != 0
    }
}

fn pay(k: usize) -> i64 {
    (k as i64) * 31 + 7
}

fn ln(k: usize) -> i64 {
    (k as i64) % 13
}

fn run(num_buffers: usize, num_receivers: usize, num_messages: usize, seed: u64) {
    let pipe = Arc::new(Pipe::new(num_buffers));
    let accepted = Arc::new(AtomicUsize::new(0));

    let receivers: Vec<_> = (0..num_receivers)
        .map(|r| {
            let pipe = pipe.clone();
            let accepted = accepted.clone();
            std::thread::spawn(move || {
                let mut recv = Receiver::new();
                let mut choose = rng(seed ^ (r as u64 + 1).wrapping_mul(0x9e37_79b9));
                // Stop only between buffers: a receiver that stops before its
                // release store strands the buffer (and a blocking sender)
                while accepted.load(Ordering::Relaxed) < num_messages
                    || matches!(recv.pc, RPc::Rel { .. })
                {
                    let before = recv.log.len();
                    assert_eq!(recv.step(&pipe, num_buffers, &mut choose), Status::Running);
                    if recv.log.len() > before {
                        accepted.fetch_add(1, Ordering::Relaxed);
                    }
                }
                recv.log
            })
        })
        .collect();

    let mut send = Sender::new();
    let mut choose = rng(seed);
    loop {
        match send.step(&pipe, num_buffers, num_messages, &pay, &ln, &mut choose) {
            Status::Running => {}
            Status::Halted => break,
            Status::Fault => panic!("sender fault"),
        }
    }

    let mut got: Vec<_> = receivers.into_iter().flat_map(|h| h.join().unwrap()).collect();
    got.sort();
    let want: Vec<_> = (0..num_messages).map(|k| (k as i64, pay(k), ln(k))).collect();
    assert_eq!(got, want);
    // Lean logs are newest first (`::`); the Rust ones oldest first (`push`)
    assert_eq!(send.log, want);
}

#[test]
fn deliver() {
    let n = if cfg!(miri) { 20 } else { 2000 };
    for (seed, (b, r)) in [(1, 1), (1, 3), (2, 2), (4, 3), (3, 1)].into_iter().enumerate() {
        run(b, r, n, seed as u64 + 1);
    }
}
