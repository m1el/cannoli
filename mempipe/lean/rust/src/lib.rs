//! The Lean model of mempipe (`mempipe/lean/Mempipe/Program.lean`), rendered
//! as Rust.
//!
//! `generated.rs` is produced by `lake env lean tools/ToRust.lean` from the
//! very definitions the Lean proofs are about, so it can be read side by side
//! with `mempipe/src/lib.rs`: every `step` arm is one instruction of the
//! model, with the Rust atomic operation and ordering the model uses. This
//! file is the hand-written runtime: a mirror of `RawMemPipe`'s shared fields
//! and the initial values of `SendPipe::create`.
//!
//! Differences from `mempipe/src/lib.rs` that are part of the model: a chunk
//! is one value (`Option<i64>`, `None` while uninitialized) instead of bytes,
//! and the ticket counter `RecvPipe::seq` lives next to the shared fields.

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize};

mod generated;
pub use generated::*;

/// The shared state of a pipe with `num_buffers` buffers.
pub struct Pipe {
    /// `RawMemPipe::client_owned`
    pub client_owned: Vec<AtomicBool>,
    /// `RawMemPipe::client_len`
    pub client_len: Vec<AtomicUsize>,
    /// `RawMemPipe::client_seq`
    pub client_seq: Vec<AtomicU64>,
    /// `RawMemPipe::cur_seq`
    pub cur_seq: AtomicU64,
    /// `RecvPipe::seq`, the ticket counter
    pub seq: AtomicU64,
    /// `RawMemPipe::chunks`, one value each
    chunks: Vec<UnsafeCell<Option<i64>>>,
}

// Chunks are accessed non-atomically, synchronized by the protocol
unsafe impl Sync for Pipe {}

/// `NO_SEQ` of `mempipe/src/lib.rs`, the model's `-1`.
pub const NO_SEQ: u64 = u64::MAX;

impl Pipe {
    /// A new pipe, initialized like `SendPipe::create` (the model's `initVal`).
    pub fn new(num_buffers: usize) -> Self {
        Pipe {
            client_owned: (0..num_buffers).map(|_| AtomicBool::new(false)).collect(),
            client_len: (0..num_buffers).map(|_| AtomicUsize::new(0)).collect(),
            client_seq: (0..num_buffers).map(|_| AtomicU64::new(NO_SEQ)).collect(),
            cur_seq: AtomicU64::new(0),
            seq: AtomicU64::new(0),
            chunks: (0..num_buffers).map(|_| UnsafeCell::new(None)).collect(),
        }
    }

    /// Write the chunk of buffer `i` (`ChunkWriter::send`).
    ///
    /// # Safety
    ///
    /// No other thread may access the chunk concurrently.
    pub unsafe fn write_chunk(&self, i: usize, v: i64) {
        *self.chunks[i].get() = Some(v);
    }

    /// Read the chunk of buffer `i` (the slice handed to the callback).
    ///
    /// # Safety
    ///
    /// No other thread may write the chunk concurrently.
    pub unsafe fn read_chunk(&self, i: usize) -> Option<i64> {
        *self.chunks[i].get()
    }
}

/// The result of a step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Running,
    Halted,
    Fault,
}

impl Sender {
    pub fn new() -> Self {
        Sender { pc: SPc::Start { k: 0 }, log: Vec::new() }
    }
}

impl Default for Sender {
    fn default() -> Self {
        Self::new()
    }
}

impl Receiver {
    pub fn new() -> Self {
        Receiver { pc: RPc::Init, log: Vec::new() }
    }
}

impl Default for Receiver {
    fn default() -> Self {
        Self::new()
    }
}
