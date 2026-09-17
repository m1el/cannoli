//! Forces the stranded-buffer schedule with spin-sleeps (scheduler yields) at
//! the `miri_hooks` delay points. One buffer, readers R0 (ticket 0) and R1
//! (ticket 1):
//!
//! 1. main publishes seq 0 before any reader runs
//! 2. R1 passes its first load in `try_recv` for seq 0's publication, spins
//! 3. R0 consumes seq 0; the sender reuses the buffer, stores seq 1, then
//!    spins before storing `client_owned = true`
//! 4. R1 wakes and finishes its second load while seq 1 is unpublished
//!
//! If the receiver checks `client_owned` first, step 4 lets R1 read seq 1's
//! bytes without synchronizing with their write (a data race under Rust's
//! atomic ordering rules), then consume seq 1 before the sender's late
//! `client_owned = true` strands the buffer. If it checks the sequence first,
//! R1 can't pass its first load for seq 0 and every spin times out harmlessly.
//!
//! Data race (weak memory emulation off, so the Relaxed handshake below can't
//! read stale phases and miss the schedule):
//!
//! ```text
//! MIRIFLAGS="-Zmiri-ignore-leaks -Zmiri-tree-borrows \
//!     -Zmiri-disable-weak-memory-emulation \
//!     -Zmiri-many-seeds=0..64 -Zmiri-many-seeds-keep-going" \
//!     cargo +nightly miri test -p mempipe --test miri_delayed
//! ```
//!
//! Stranded buffer (race detector off, so execution continues past the race;
//! fails with "pipe stuck"):
//!
//! ```text
//! MIRIFLAGS="-Zmiri-ignore-leaks -Zmiri-tree-borrows \
//!     -Zmiri-disable-data-race-detector \
//!     -Zmiri-many-seeds=0..16 -Zmiri-many-seeds-keep-going" \
//!     cargo +nightly miri test -p mempipe --test miri_delayed
//! ```
#![cfg(miri)]

use mempipe::miri_hooks::{Hooks, HOOKS};
use mempipe::{RecvPipe, SendPipe};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering::Relaxed};

const MESSAGES: u64 = 3;

/// Yields a spin-sleep waits for the other side before giving up
const SPIN: usize = 5_000;

/// Yields the test waits for all messages before calling the pipe stuck
const PATIENCE: usize = 10_000;

// Handshake phases. Everything here is Relaxed on purpose: a Relaxed load
// acquires nothing in Miri, so the handshake adds no happens-before edges
// that would hide the race.
const R1_STALLED: u8 = 1 << 0;
const SEQ1_STORED: u8 = 1 << 1;
const R1_RECEIVED: u8 = 1 << 2;
static PHASE: AtomicU8 = AtomicU8::new(0);

fn set(phase: u8) {
    PHASE.fetch_or(phase, Relaxed);
}

/// Spin-sleep until `phase` is reached or `SPIN` yields pass
fn spin_sleep_until(phase: u8) {
    for _ in 0..SPIN {
        if PHASE.load(Relaxed) & phase != 0 { return; }
        std::thread::yield_now();
    }
}

fn between_loads(ticket: u64) {
    // Only R1 ever holds ticket 1, and it only stalls once
    if ticket == 1 && PHASE.load(Relaxed) & R1_STALLED == 0 {
        set(R1_STALLED);
        spin_sleep_until(SEQ1_STORED);
    }
}

fn before_owned_publish(seq: u64) {
    if seq == 1 {
        set(SEQ1_STORED);
        spin_sleep_until(R1_RECEIVED);
    }
}

/// `SendPipe` holds a raw pointer; the sender thread is its only user
struct Sender(SendPipe<8, 1>);
unsafe impl Send for Sender {}

#[test]
fn stranded_buffer_schedule() {
    HOOKS.set(Hooks { between_loads, before_owned_publish }).ok().unwrap();

    let mut tx = SendPipe::<8, 1>::create().unwrap();
    let rx: &'static RecvPipe<8, 1> =
        Box::leak(Box::new(RecvPipe::open(tx.uid()).unwrap()));
    static DELIVERED: AtomicU64 = AtomicU64::new(0);
    static STOP: AtomicBool = AtomicBool::new(false);

    let t0 = rx.request_ticket();
    let t1 = rx.request_ticket();
    tx.alloc_buffer(false).send(0u64.to_le_bytes());

    let reader = move |mut ticket, is_r1| move || {
        while !STOP.load(Relaxed) {
            let (next, res) = rx.try_recv(ticket, |d| -> Result<u64, ()> {
                Ok(u64::from_le_bytes(d.try_into().unwrap()))
            });
            ticket = next;
            if let Some(Ok((seq, payload))) = res {
                assert_eq!(seq, payload, "ticket {seq} read message {payload}");
                if is_r1 { set(R1_RECEIVED); }
                DELIVERED.fetch_add(1, Relaxed);
            }
            std::thread::yield_now();
        }
    };

    std::thread::spawn(reader(t1, true));
    spin_sleep_until(R1_STALLED);
    std::thread::spawn(reader(t0, false));

    let tx = Sender(tx);
    std::thread::spawn(move || {
        let mut tx = tx;
        for i in 1..MESSAGES {
            tx.0.alloc_buffer(false).send(i.to_le_bytes());
        }
    });

    for _ in 0..PATIENCE {
        if DELIVERED.load(Relaxed) == MESSAGES { break; }
        std::thread::yield_now();
    }
    STOP.store(true, Relaxed);
    assert_eq!(DELIVERED.load(Relaxed), MESSAGES, "pipe stuck");
}
