//! Two readers share one `RecvPipe` over a single buffer, and Miri's random
//! scheduler picks the interleaving. Every message must be delivered once with
//! its own bytes, without a data race, and the sender must not get stuck.
//!
//! Needs a Miri that models atomic orderings (nightly 2026-09 works) and Tree
//! Borrows (the chunk pointer is derived from its first byte):
//!
//! ```text
//! MIRIFLAGS="-Zmiri-ignore-leaks -Zmiri-tree-borrows -Zmiri-preemption-rate=0.3 \
//!     -Zmiri-many-seeds=0..400 -Zmiri-many-seeds-keep-going" \
//!     cargo +nightly miri test -p mempipe --test miri_random -- --nocapture
//! ```
#![cfg(miri)]

use mempipe::{RecvPipe, SendPipe};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

const MESSAGES: u64 = 3;

/// Scheduler yields the test waits for all messages before calling the pipe
/// stuck
const PATIENCE: usize = 20_000;

/// `SendPipe` holds a raw pointer; the sender thread is its only user
struct Sender(SendPipe<8, 1>);
unsafe impl Send for Sender {}

#[test]
fn two_readers_one_buffer() {
    let tx = SendPipe::<8, 1>::create().unwrap();
    let rx: &'static RecvPipe<8, 1> =
        Box::leak(Box::new(RecvPipe::open(tx.uid()).unwrap()));
    static DELIVERED: AtomicU64 = AtomicU64::new(0);
    static SENT: AtomicU64 = AtomicU64::new(0);
    static STOP: AtomicBool = AtomicBool::new(false);

    for _ in 0..2 {
        let mut ticket = rx.request_ticket();
        std::thread::spawn(move || {
            while !STOP.load(Ordering::SeqCst) {
                let (next, res) = rx.try_recv(ticket, |d| -> Result<u64, ()> {
                    Ok(u64::from_le_bytes(d.try_into().unwrap()))
                });
                ticket = next;
                if let Some(Ok((seq, payload))) = res {
                    assert_eq!(seq, payload,
                        "ticket {seq} read message {payload}");
                    DELIVERED.fetch_add(1, Ordering::SeqCst);
                }
                std::thread::yield_now();
            }
        });
    }

    let tx = Sender(tx);
    std::thread::spawn(move || {
        let mut tx = tx;
        for i in 0..MESSAGES {
            tx.0.alloc_buffer(false).send(i.to_le_bytes());
            SENT.store(i + 1, Ordering::SeqCst);
        }
    });

    for _ in 0..PATIENCE {
        if DELIVERED.load(Ordering::SeqCst) == MESSAGES { break; }
        std::thread::yield_now();
    }
    STOP.store(true, Ordering::SeqCst);
    assert_eq!(DELIVERED.load(Ordering::SeqCst), MESSAGES,
        "pipe stuck: sent {} of {MESSAGES}", SENT.load(Ordering::SeqCst));
}
