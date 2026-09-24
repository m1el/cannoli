import Mempipe.Program
import ORC11.Exec

/-!
# The four Release/Acquire orderings are all needed

The programs of `Program.lean`, parameterized by the orderings of the four
accesses that the Miri experiments found necessary: the `client_seq` store
(Release) and its load in `try_recv` (Acquire), and the `client_owned = false`
store in `try_recv` (Release) and its load in `alloc_buffer` (Acquire). With all
four at `acqrel` they are the verified programs (`progO_strong`).

Weakening any one of them to `rlx` breaks the protocol: for each, a concrete
schedule with one buffer and one receiver reaches a data race on a chunk. The
schedules are run by the sound interpreter of `ORC11/Exec.lean` and checked by
evaluation in the kernel (`decide`), so each counterexample is a checked ORC11
execution.

- `client_seq` store or load relaxed: the receiver matches its sequence number
  without acquiring the sender's view, and reads the chunk without having
  seen the sender's write of it.
- `client_owned = false` store or `alloc_buffer`'s load relaxed: the sender
  reuses the buffer without having seen the receiver's read of the chunk, and
  overwrites it.

As a control, the same schedules with all four orderings reach the same
program points without a race.
-/

namespace Mempipe

open ORC11

/-- The orderings of the four synchronizing accesses. -/
structure Ords where
  /-- `client_seq[i].store(seq, Release)` in `ChunkWriter::drop` -/
  seqSt : MemOrder
  /-- `client_seq[i].load(Acquire)` in `try_recv` -/
  seqLd : MemOrder
  /-- `client_owned[i].store(false, Release)` in `try_recv` -/
  relSt : MemOrder
  /-- `client_owned[i].load(Acquire)` in `alloc_buffer` -/
  allocLd : MemOrder

/-- The orderings of `mempipe/src/lib.rs`. -/
def Ords.strong : Ords := ⟨.acqrel, .acqrel, .acqrel, .acqrel⟩

/-- `sprog` with orderings `os`. -/
def sprogO (os : Ords) (N M : ℕ) (pay ln : ℕ → ℤ) (σ : SState) : Instr Loc ℤ SState :=
  match σ.pc with
  | .start k =>
      if k < M then .choose fun b => { σ with pc := .alloc k b 0 } else .halt
  | .alloc k b i =>
      .read (.own i) os.allocLd fun
        | none => { σ with pc := .fault }
        | some v => if v = 0 then { σ with pc := .chunk k b i }
                    else { σ with pc := .alloc k b ((i + 1) % N) }
  | .chunk k b i => .write (.chunk i) .na (pay k) { σ with pc := .len k b i }
  | .len k b i => .write (.len i) .rlx (ln k) { σ with pc := .own k b i }
  | .own k b i => .write (.own i) .rlx 1 { σ with pc := .fadd k b i }
  | .fadd k b i => .update .curSeq .rlx .rlx (· + 1) fun s => { σ with pc := .pub k b i s }
  | .pub k b i s =>
      .write (.cseq i) os.seqSt s
        { pc := if b then .spin k i else .start (k + 1)
          log := (s, pay k, ln k) :: σ.log }
  | .spin k i =>
      .read (.own i) .rlx fun
        | none => { σ with pc := .fault }
        | some v => if v = 0 then { σ with pc := .start (k + 1) }
                    else { σ with pc := .spin k i }
  | .fault => .fault

/-- `rprog` with orderings `os`. -/
def rprogO (os : Ords) (N : ℕ) (ρ : RState) : Instr Loc ℤ RState :=
  match ρ.pc with
  | .init => .update .tick .rlx .rlx (· + 1) fun t => { ρ with pc := .scan t 0 }
  | .scan t i =>
      .read (.cseq i) os.seqLd fun
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
  | .rel _ i => .write (.own i) os.relSt 0 { ρ with pc := .init }
  | .fault => .fault

def progO {ρ : Type} (os : Ords) (N M : ℕ) (pay ln : ℕ → ℤ) :
    (i : TId ρ) → LS i → Instr Loc ℤ (LS i)
  | .sender => sprogO os N M pay ln
  | .recv _ => rprogO os N

theorem sprogO_strong (N M : ℕ) (pay ln : ℕ → ℤ) :
    sprogO Ords.strong N M pay ln = sprog N M pay ln := by
  funext σ; unfold sprogO sprog; cases σ.pc <;> rfl

theorem rprogO_strong (N : ℕ) : rprogO Ords.strong N = rprog N := by
  funext σ; unfold rprogO rprog; cases σ.pc <;> rfl

/-- With the orderings of the code, these are the verified programs. -/
theorem progO_strong {ρ : Type} (N M : ℕ) (pay ln : ℕ → ℤ) :
    progO (ρ := ρ) Ords.strong N M pay ln = prog N M pay ln := by
  funext i; cases i
  · exact sprogO_strong N M pay ln
  · exact rprogO_strong N

/-! ## Schedules -/

/-- One receiver. -/
abbrev S1 (b : Bool) : TId Unit × Bool := (.sender, b)
abbrev R1 (b : Bool) : TId Unit × Bool := (.recv (), b)

/-- Send message 0 (non-blocking), then let the receiver take its ticket and
read the chunk's length. -/
def schedDeliver : List (TId Unit × Bool) :=
  [S1 false, S1 false, S1 false, S1 false, S1 false, S1 false, S1 false,
   R1 false, R1 false, R1 false, R1 false]

/-- Deliver message 0, then let the sender take the same buffer for message 1. -/
def schedReuse : List (TId Unit × Bool) :=
  schedDeliver ++ [R1 false, R1 true, R1 false, S1 false, S1 false]

/-- The programs of the counterexamples: one buffer, one receiver, `M`
messages with payload 7 and length 3. -/
abbrev P (os : Ords) (M : ℕ) := progO (ρ := Unit) os 1 M (fun _ => 7) (fun _ => 3)

def racyAt (os : Ords) (M : ℕ) (i : TId Unit) (sched : List (TId Unit × Bool)) : Bool :=
  (run? (P os M) (initConfig init0 initVal) sched).any
    fun c => !decide ((P os M i (c.th i).1).DrfPreOk c.na (c.th i).2 c.mem)

/-- The program counters a schedule ends at, if it runs. -/
def pcsAt (os : Ords) (M : ℕ) (sched : List (TId Unit × Bool)) : Option (SPc × RPc) :=
  (run? (P os M) (initConfig init0 initVal) sched).map
    fun c => ((c.th .sender).1.pc, (c.th (.recv ())).1.pc)

/-! ## Controls: with the orderings of the code, no race -/

/-- The receiver is about to read the chunk, without a race. -/
example : pcsAt Ords.strong 1 schedDeliver = some (.start 1, .chunk 0 0 3) := by decide
example : racyAt Ords.strong 1 (.recv ()) schedDeliver = false := by decide

/-- The sender took the buffer again and is about to write the chunk. -/
example : pcsAt Ords.strong 2 schedReuse = some (.chunk 1 false 0, .init) := by decide
example : racyAt Ords.strong 2 .sender schedReuse = false := by decide

/-! ## Each weakening races -/

def Ords.weakSeqSt : Ords := { Ords.strong with seqSt := .rlx }
def Ords.weakSeqLd : Ords := { Ords.strong with seqLd := .rlx }
def Ords.weakRelSt : Ords := { Ords.strong with relSt := .rlx }
def Ords.weakAllocLd : Ords := { Ords.strong with allocLd := .rlx }

/-- The weakened runs stop at the same program points as the controls: the
receiver about to read the chunk, or the sender about to overwrite it. -/
example : pcsAt Ords.weakSeqSt 1 schedDeliver = some (.start 1, .chunk 0 0 3) := by decide
example : pcsAt Ords.weakSeqLd 1 schedDeliver = some (.start 1, .chunk 0 0 3) := by decide
example : pcsAt Ords.weakRelSt 2 schedReuse = some (.chunk 1 false 0, .init) := by decide
example : pcsAt Ords.weakAllocLd 2 schedReuse = some (.chunk 1 false 0, .init) := by decide

/-- `client_seq` store relaxed: the receiver's chunk read races with the
sender's write. -/
theorem weakSeqSt_racy :
    ∃ c, Reachable (P Ords.weakSeqSt 1) init0 initVal c ∧ Racy (P Ords.weakSeqSt 1) c :=
  racy_of_run (l := schedDeliver) (i := .recv ()) (by decide)

/-- `client_seq` load in `try_recv` relaxed: same race. -/
theorem weakSeqLd_racy :
    ∃ c, Reachable (P Ords.weakSeqLd 1) init0 initVal c ∧ Racy (P Ords.weakSeqLd 1) c :=
  racy_of_run (l := schedDeliver) (i := .recv ()) (by decide)

/-- `client_owned = false` store relaxed: the sender's chunk write for the next
message races with the receiver's read. -/
theorem weakRelSt_racy :
    ∃ c, Reachable (P Ords.weakRelSt 2) init0 initVal c ∧ Racy (P Ords.weakRelSt 2) c :=
  racy_of_run (l := schedReuse) (i := .sender) (by decide)

/-- `client_owned` load in `alloc_buffer` relaxed: same race. -/
theorem weakAllocLd_racy :
    ∃ c, Reachable (P Ords.weakAllocLd 2) init0 initVal c ∧ Racy (P Ords.weakAllocLd 2) c :=
  racy_of_run (l := schedReuse) (i := .sender) (by decide)

end Mempipe
