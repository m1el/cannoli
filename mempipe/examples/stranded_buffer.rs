//! Deterministic reproduction: a stale `client_owned` observation lets a
//! reader consume a buffer before the sender publishes it, and the sender's
//! late `client_owned = true` store overwrites the reader's acknowledgement.
//! The buffer stays owned by the client with a sequence number nobody holds a
//! ticket for, so the pipe is dead.
//!
//! ```text
//! cargo +nightly-2024-03-01 run -p mempipe --features repro-hooks \
//!     --example stranded_buffer
//! ```
//!
//! Schedule (one buffer, readers R0 and R1 sharing one `RecvPipe`):
//!
//! 1. sender publishes seq 0: len, seq=0, owned=true
//! 2. R1 (ticket 1) loads owned[0] == true, then stalls (hook)
//! 3. R0 (ticket 0) consumes seq 0 and stores owned[0] = false
//! 4. sender reallocates buffer 0, stores len and seq=1, stalls (hook)
//!    before owned[0] = true
//! 5. R1 resumes: seq[0] == 1 == its ticket, runs the callback on seq 1 and
//!    stores owned[0] = false (a no-op, it already is)
//! 6. sender stores owned[0] = true
//!
//! Now owned[0] == true, seq[0] == 1, and the live tickets are 2 and 3.
//! Nobody will ever return buffer 0; `alloc_buffer` spins forever (with
//! `blocking = true` the sender would already hang in step 6's drop).
//!
//! The hooks only widen windows that exist without them: every step above is
//! a single atomic load/store in `src/lib.rs`, and each hook sits between two
//! of them. No weak-memory behaviour is needed; this is a sequentially
//! consistent interleaving.

use mempipe::repro_hooks::{Hooks, HOOKS};
use mempipe::{RecvPipe, SendPipe};
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Duration;

const CHUNK_SIZE: usize = 16;
const NUM_BUFFERS: usize = 1;

/// Scheduling phases, advanced monotonically.
const START: u8 = 0;
const R1_STALLED: u8 = 1;
const SEQ1_STORED: u8 = 2;
const R1_ACKED: u8 = 3;
static PHASE: AtomicU8 = AtomicU8::new(START);

/// Sender progress: number of completed `ChunkWriter` drops.
static SENT: AtomicU64 = AtomicU64::new(0);
static STOP: AtomicBool = AtomicBool::new(false);

/// Deliveries as (reader, sequence, payload, sender had published owned=true).
static LOG: Mutex<Vec<(&str, u64, String, bool)>> = Mutex::new(Vec::new());

/// Wait until `phase` is reached, giving up after a second (the schedule may
/// be impossible, e.g. with the fix applied). Returns whether it was reached.
fn wait_for(phase: u8) -> bool {
    for _ in 0..1000 {
        if PHASE.load(Ordering::SeqCst) >= phase {
            return true;
        }
        std::thread::sleep(Duration::from_millis(1));
    }
    false
}

/// `try_recv` saw owned=true for `ticket` and has not yet loaded seq.
fn after_owned_acquire(ticket: u64) {
    if ticket == 1 && PHASE.load(Ordering::SeqCst) == START {
        PHASE.store(R1_STALLED, Ordering::SeqCst);
        if !wait_for(SEQ1_STORED) {
            println!("R1 stall: the sender never stored seq 1 while R1 waited");
        }
    }
}

/// The sender stored len and seq for `seq` and has not yet stored owned=true.
fn before_owned_publish(seq: u64) {
    if seq == 1 {
        PHASE.store(SEQ1_STORED, Ordering::SeqCst);
        if !wait_for(R1_ACKED) {
            println!("sender stall: R1 did not consume seq 1 before it was published");
        }
    }
}

fn reader(name: &'static str, rx: &RecvPipe<CHUNK_SIZE, NUM_BUFFERS>,
          mut ticket: mempipe::Ticket, on_first: Option<u8>) {
    let mut first = on_first;
    while !STOP.load(Ordering::Relaxed) {
        let (next, res) = rx.try_recv(ticket, |data| -> Result<String, ()> {
            Ok(String::from_utf8_lossy(data).into_owned())
        });
        ticket = next;
        if let Some(Ok((seq, payload))) = res {
            // try_recv has returned, so the owned=false store is done
            let published = SENT.load(Ordering::SeqCst) > seq;
            LOG.lock().unwrap().push((name, seq, payload, published));
            if let Some(phase) = first.take() {
                PHASE.store(phase, Ordering::SeqCst);
            }
        }
        std::thread::yield_now();
    }
}

fn report() {
    for (reader, seq, payload, published) in LOG.lock().unwrap().iter() {
        println!("{reader} received seq {seq} {payload:?}{}",
            if *published { "" }
            else { "  <-- before the sender stored owned=true" });
    }
}

fn main() -> Result<(), mempipe::Error> {
    HOOKS.set(Hooks { after_owned_acquire, before_owned_publish })
        .ok().expect("hooks already set");

    let mut tx = SendPipe::<CHUNK_SIZE, NUM_BUFFERS>::create()?;
    let rx = RecvPipe::<CHUNK_SIZE, NUM_BUFFERS>::open(tx.uid())?;
    let t0 = rx.request_ticket();
    let t1 = rx.request_ticket();

    // 1. publish seq 0
    tx.alloc_buffer(false).send(b"payload-0");
    SENT.store(1, Ordering::SeqCst);

    std::thread::scope(|s| {
        let rx = &rx;

        // 2. R1 observes owned=true for seq 0 and stalls
        s.spawn(move || reader("R1", rx, t1, Some(R1_ACKED)));
        if !wait_for(R1_STALLED) {
            println!("R1 never saw owned=true while holding ticket 1 before seq 0 was consumed");
        }

        // 3. R0 consumes seq 0
        s.spawn(move || reader("R0", rx, t0, None));

        // Watchdog: the sender below never returns if the bug triggers.
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(5));
            report();
            println!("\nBUG: alloc_buffer for seq 2 has not returned after \
                5s while both readers poll.\nbuffer 0 is owned=true with \
                seq 1, but ticket 1 was already spent on it; the pipe is \
                dead.");
            std::process::exit(1);
        });

        // 4-6. sender reuses the buffer for seq 1, then tries seq 2
        tx.alloc_buffer(false).send(b"payload-1");
        SENT.store(2, Ordering::SeqCst);
        tx.alloc_buffer(false).send(b"payload-2");
        SENT.store(3, Ordering::SeqCst);

        std::thread::sleep(Duration::from_millis(100));
        report();
        println!("\nno hang: the stranded-buffer schedule did not occur");
        STOP.store(true, Ordering::Relaxed);
    });
    Ok(())
}
