import ORC11.Program

/-!
# The mempipe protocol as an ORC11 program

`mempipe/src/lib.rs`: one sender (`SendPipe::alloc_buffer`, `ChunkWriter::send`
/ `send_raw` and `ChunkWriter::drop`) and any number of receivers sharing one
`RecvPipe` (`request_ticket`, `try_recv`).

Parameters: `N` buffers, `M` messages to send; the `k`-th message has payload
`pay k` and length `ln k`. The chunk of a buffer is modeled as one
non-atomic location holding the whole payload, which is coarser than bytes and
so conservative for races. Values are integers: `false = 0`, `true = 1`,
`NO_SEQ = -1` (standing for `u64::MAX`; sequence numbers never get there).

Local states carry ghost logs: the sender logs `(seq, payload, len)` when it
publishes a buffer, a receiver logs `(ticket, payload, len)` when its callback
accepts a buffer. Logs are written by their own thread's transitions and never
read by them, so they do not constrain executions.
-/

namespace Mempipe

open ORC11

/-- The shared locations of a pipe. Buffer indices `i < N`. -/
inductive Loc where
  /-- `client_owned[i]: AtomicBool` -/
  | own (i : ℕ)
  /-- `client_len[i]: AtomicUsize` -/
  | len (i : ℕ)
  /-- `client_seq[i]: AtomicU64` -/
  | cseq (i : ℕ)
  /-- `chunks[i]`: plain bytes -/
  | chunk (i : ℕ)
  /-- `cur_seq: AtomicU64`, sender only -/
  | curSeq
  /-- `RecvPipe::seq: AtomicU64`, the ticket counter -/
  | tick
  deriving DecidableEq


/-- `u64::MAX` -/
def NO_SEQ : ℤ := -1

/-- Initial memory (`SendPipe::create` / `create_local`): chunks are left
uninitialized. -/
def initVal : Loc → Option ℤ
  | .own _ => some 0
  | .len _ => some 0
  | .cseq _ => some NO_SEQ
  | .chunk _ => none
  | .curSeq => some 0
  | .tick => some 0

/-- A log entry: sequence number (or ticket), payload, length. -/
abbrev Entry := ℤ × ℤ × ℤ

/-! ## Sender -/

/-- Sender program counter. `k` is the index of the message being sent, `b`
whether this send blocks, `i` a buffer index. -/
inductive SPc where
  /-- Start message `k`: halt if all `M` are sent, else choose `blocking`. -/
  | start (k : ℕ)
  /-- `alloc_buffer`: `client_owned[i].load(Acquire)`. -/
  | alloc (k : ℕ) (b : Bool) (i : ℕ)
  /-- `send`: write the chunk bytes. -/
  | chunk (k : ℕ) (b : Bool) (i : ℕ)
  /-- `drop` step 1: `client_len[i].store(len, Relaxed)`. -/
  | len (k : ℕ) (b : Bool) (i : ℕ)
  /-- `drop` step 2: `client_owned[i].store(true, Relaxed)`. -/
  | own (k : ℕ) (b : Bool) (i : ℕ)
  /-- `drop` step 3: `cur_seq.fetch_add(1, Relaxed)`. -/
  | fadd (k : ℕ) (b : Bool) (i : ℕ)
  /-- `drop` step 4: `client_seq[i].store(seq, Release)`. -/
  | pub (k : ℕ) (b : Bool) (i : ℕ) (s : ℤ)
  /-- `drop` step 5: `while client_owned[i].load(Relaxed) {}`. -/
  | spin (k : ℕ) (i : ℕ)
  /-- Read uninitialized memory. -/
  | fault
  deriving DecidableEq

structure SState where
  pc : SPc
  log : List Entry

/-- The sender. -/
def sprog (N M : ℕ) (pay ln : ℕ → ℤ) (σ : SState) : Instr Loc ℤ SState :=
  match σ.pc with
  | .start k =>
      if k < M then .choose fun b => { σ with pc := .alloc k b 0 } else .halt
  | .alloc k b i =>
      .read (.own i) .acqrel fun
        | none => { σ with pc := .fault }
        | some v => if v = 0 then { σ with pc := .chunk k b i }
                    else { σ with pc := .alloc k b ((i + 1) % N) }
  | .chunk k b i => .write (.chunk i) .na (pay k) { σ with pc := .len k b i }
  | .len k b i => .write (.len i) .rlx (ln k) { σ with pc := .own k b i }
  | .own k b i => .write (.own i) .rlx 1 { σ with pc := .fadd k b i }
  | .fadd k b i => .update .curSeq .rlx .rlx (· + 1) fun s => { σ with pc := .pub k b i s }
  | .pub k b i s =>
      .write (.cseq i) .acqrel s
        { pc := if b then .spin k i else .start (k + 1)
          log := (s, pay k, ln k) :: σ.log }
  | .spin k i =>
      .read (.own i) .rlx fun
        | none => { σ with pc := .fault }
        | some v => if v = 0 then { σ with pc := .start (k + 1) }
                    else { σ with pc := .spin k i }
  | .fault => .fault

/-! ## Receivers -/

/-- Receiver program counter, `t` the ticket held. -/
inductive RPc where
  /-- `request_ticket`: `seq.fetch_add(1, Relaxed)`. -/
  | init
  /-- `try_recv`: `client_seq[i].load(Acquire)`, compare with the ticket. -/
  | scan (t : ℤ) (i : ℕ)
  /-- `debug_assert!(client_owned[i].load(Relaxed))`. -/
  | own (t : ℤ) (i : ℕ)
  /-- `client_len[i].load(Relaxed)`. -/
  | len (t : ℤ) (i : ℕ)
  /-- Read the chunk bytes. -/
  | chunk (t : ℤ) (i : ℕ) (n : ℤ)
  /-- The callback returns `Ok` or `Err`. -/
  | cb (t : ℤ) (i : ℕ) (n p : ℤ)
  /-- `client_owned[i].store(false, Release)`, then a new ticket. -/
  | rel (t : ℤ) (i : ℕ)
  /-- The `debug_assert` failed, or uninitialized memory was read. -/
  | fault
  deriving DecidableEq

structure RState where
  pc : RPc
  log : List Entry

/-- A receiver. After scanning all buffers without a match (`try_recv`
returns `None`) or after `Err`, it calls `try_recv` again with its ticket. -/
def rprog (N : ℕ) (ρ : RState) : Instr Loc ℤ RState :=
  match ρ.pc with
  | .init => .update .tick .rlx .rlx (· + 1) fun t => { ρ with pc := .scan t 0 }
  | .scan t i =>
      .read (.cseq i) .acqrel fun
        | none => { ρ with pc := .fault }
        | some s => if s = t then { ρ with pc := .own t i }
                    else { ρ with pc := .scan t ((i + 1) % N) }
  | .own t i =>
      .read (.own i) .rlx fun
        | none => { ρ with pc := .fault }
        | some v => if v = 0 then { ρ with pc := .fault } else { ρ with pc := .len t i }
  | .len t i =>
      .read (.len i) .rlx fun
        | none => { ρ with pc := .fault }
        | some n => { ρ with pc := .chunk t i n }
  | .chunk t i n =>
      .read (.chunk i) .na fun
        | none => { ρ with pc := .fault }
        | some p => { ρ with pc := .cb t i n p }
  | .cb t i n p =>
      .choose fun ok =>
        if ok then { pc := .rel t i, log := (t, p, n) :: ρ.log }
        else { ρ with pc := .scan t 0 }
  | .rel _ i => .write (.own i) .acqrel 0 { ρ with pc := .init }
  | .fault => .fault

/-! ## The pool -/

/-- Threads: the sender and receivers indexed by any type `ρ`. -/
inductive TId (ρ : Type) where
  | sender
  | recv (r : ρ)
  deriving DecidableEq

/-- Local state types. -/
abbrev LS {ρ : Type} : TId ρ → Type
  | .sender => SState
  | .recv _ => RState

/-- Programs. -/
def prog {ρ : Type} (N M : ℕ) (pay ln : ℕ → ℤ) : (i : TId ρ) → LS i → Instr Loc ℤ (LS i)
  | .sender => sprog N M pay ln
  | .recv _ => rprog N

/-- Initial local states. -/
def init0 {ρ : Type} : (i : TId ρ) → LS i
  | .sender => ⟨.start 0, []⟩
  | .recv _ => ⟨.init, []⟩

abbrev Cfg (ρ : Type) := Config (TId ρ) LS Loc ℤ

/-- Reachable configurations of the pipe. -/
def Reach {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ) (c : Cfg ρ) : Prop :=
  Reachable (prog N M pay ln) init0 initVal c

end Mempipe
