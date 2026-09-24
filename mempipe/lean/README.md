# mempipe on ORC11, in Lean

A Lean 4 model of mempipe's shared-memory protocol (`mempipe/src/lib.rs`) on a
port of the ORC11 memory model (Dang, Jourdan, Kaiser, Dreyer, "RustBelt Meets
Relaxed Memory", POPL 2020), with proofs, for **any** number of buffers,
receivers and messages, of:

1. **Correct delivery**: every buffer a receiver accepts has exactly the payload
   and length the sender published under that sequence number, and no sequence
   number is accepted twice.
2. **No memory-ordering violations**: ORC11's race detector never fires, so
   there is no data race on the chunk bytes; the `debug_assert!(client_owned)`
   in `try_recv` never fails; nobody reads uninitialized memory.
3. **No stranding**: from every reachable state, some continuation delivers
   every message.

Build with `lake build` (Lean `v4.34.0`, Mathlib `v4.34.0`; run
`lake exe cache get` first). `scripts/check_axioms.sh` builds everything and
checks that the entry points in `ProofAudit.lean` use no `sorry` and no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`.

## The theorems

`N` buffers, `M` messages, payloads `pay : ℕ → ℤ` and lengths `ln : ℕ → ℤ`
(message `k` carries `pay k`, `ln k`), receivers indexed by any type `ρ`.
`Reach N M pay ln c` means configuration `c` is reachable from the initial one.
All in `Mempipe/Safety.lean` and `Mempipe/Progress.lean`:

```lean
theorem no_race (hr : Reach N M pay ln c) : ¬ Racy (prog N M pay ln) c
theorem no_fault (hr : Reach N M pay ln c) : ¬ Faulty (prog N M pay ln) c
theorem sender_log (hr : Reach N M pay ln c) : c.s.log = sentLog pay ln c.s.pc.npub
theorem recv_correct (hr : Reach N M pay ln c) (he : e ∈ (c.r r).log) : e ∈ c.s.log
theorem recv_once (hr : Reach N M pay ln c) :
    (∀ r, ((c.r r).log.map Prod.fst).Nodup) ∧
    (∀ r r', r ≠ r' → ∀ t ∈ (c.r r).log.map Prod.fst, t ∉ (c.r r').log.map Prod.fst)
theorem progress (hN : 0 < N) [Nonempty ρ] (hr : Reach N M pay ln c) :
    ∃ c', Relation.ReflTransGen (StepL (prog N M pay ln)) c c' ∧
      c'.s.pc = .start M ∧ ∀ k < M, ∃ r, ((k : ℤ), pay k, ln k) ∈ (c'.r r).log
```

- `Racy c`: some thread's next instruction fails ORC11's `drf_pre`.
- `Faulty c`: some thread is at `fault`. Receivers go there when the
  `debug_assert` fails or a read returns uninitialized memory; the sender goes
  there on reading uninitialized memory.
- The sender logs `(seq, payload, len)` when it publishes a buffer, and each
  receiver logs `(ticket, payload, len)` when its callback accepts one. These
  ghost logs are written only by their own thread's transitions and never
  read, so they do not constrain executions.
- `sentLog pay ln k = [(k-1, pay (k-1), ln (k-1)), …, (0, pay 0, ln 0)]`: the
  sender publishes message `k` under sequence number `k`.
- `StepL` is `Step` restricted to *latest* steps. Every load reads the
  mo-latest write of its location and every store goes after all writes to its
  location, so the continuation is sequentially consistent, and hence
  RC11-consistent. `StepL.reflTransGen_toStep` shows it is an ORC11 run. This
  is a progress result, not a fair-liveness theorem. In the final state the
  sender has halted (`start M`) and every message is accepted.

## The orderings are all needed

`Mempipe/Weak.lean` parameterizes the programs by the orderings of the four
synchronizing accesses: the `client_seq` store (Release) and its load in
`try_recv` (Acquire), and the `client_owned = false` store (Release) and its
load in `alloc_buffer` (Acquire). `progO_strong` shows that with all four at
`acqrel` these are the verified programs. For each single weakening to
`rlx`, a concrete schedule (one buffer, one receiver) reaches a data race:

| Weakened | Theorem | Race |
|---|---|---|
| `client_seq` store | `weakSeqSt_racy` | receiver reads the chunk without seeing the sender's write |
| `client_seq` load | `weakSeqLd_racy` | same |
| `client_owned = false` store | `weakRelSt_racy` | sender overwrites the chunk without seeing the receiver's read |
| `alloc_buffer` load | `weakAllocLd_racy` | same |

This matches the Miri experiments. The schedules run on an executable
latest-step interpreter (`ORC11/Exec.lean`, proved sound: `run?_reachable`),
and the kernel checks them with `decide`. As controls, the same schedules
with the code's orderings reach the same program points without a race.

## Layout

| File | Contents |
|---|---|
| `ORC11/Basic.lean` | memory orders, `TimeInfo`, views, thread views, messages, memory |
| `ORC11/Machine.lean` | `read_helper`, `write_helper`, `memory_write`, `read_step`, `write_step`, `machine_step`, `drf_pre`, `drf_post` |
| `ORC11/Program.lean` | instructions, the combined thread step (`TStep`), the thread pool, `Reachable`, `Racy`, `Faulty` |
| `ORC11/Lemmas.lean` | step inversions; unique positive times per location |
| `ORC11/Exec.lean` | executable latest steps and schedules, proved sound |
| `ORC11/Wf.lean` | closed, well-formed views and messages (`WfInv`); latest steps (`TStepL`, `StepL`) and their existence |
| `Mempipe/Program.lean` | the sender and receiver programs, initial memory, the pool |
| `Mempipe/Invariant.lean` | the safety invariant `Inv` and its initial case |
| `Mempipe/Frame.lean` | steps that do not touch a buffer preserve its phase |
| `Mempipe/SenderStep.lean`, `Mempipe/RecvStep.lean` | every step preserves `Inv` |
| `Mempipe/Safety.lean` | the safety theorems |
| `Mempipe/Idx.lean`, `Mempipe/ProgressInv.lean` | invariants used only for progress |
| `Mempipe/Progress.lean` | the continuation: publish, hand out the ticket, accept, in order |
| `Mempipe/Weak.lean` | the programs with weakened orderings, and their races |

## The invariant, in words

Each buffer `i` is in one of four phases:

- **free**: the latest `client_owned[i]` is `false`. Any `false` the sender
  can still read is that message. Every non-atomic read of the chunk is in the
  sender's view or in that message's view (which the sender's `Acquire` load
  picks up).
- **fill**: the sender took the buffer and has seen every read of the chunk.
- **sealing**: `client_owned[i] = true` is written and is the latest.
- **published `s`**: the latest `client_seq[i]` is `s`, and its `Release`
  view covers the chunk, the length and `client_owned[i] = true`. Only the
  holder of ticket `s` works on the buffer, having acquired that view. Every
  read of the chunk is in the sender's view or the holder's view. Once `s` is
  consumed, the holder is at its `client_owned[i] = false` store.

Around that: the sender is the only writer of chunks, lengths and sequence
numbers. `cur_seq` and the ticket counter are contiguous chains of
`fetch_add`s, so the `k`-th `fetch_add` returns `k`. Tickets are unique across
receivers, and logs are correct.

## Deviations from ORC11

The port follows the Coq development `gpfsl` at commit
`6cb903691a1553a3cbe4c3fede7caa41330bcfbb` (`gpfsl/orc11/`, `gpfsl/lang/lang.v`).
Each definition cites the Coq definition it ports. Deviations:

1. **Fragment.** Only reads, writes and updates (RMWs). There are no fences,
   no SC accesses, no failing CAS, no allocation or deallocation, and no system
   calls; mempipe uses none of them.
2. **Times and read ids** are `ℕ` rather than `positive`. Real messages have
   time `≥ 1`, and `0` stands for "no entry".
3. **Views are total** functions `Loc → TimeInfo`, with `⊥ = ⟨0, ∅, ∅, ∅⟩` for
   an absent entry, rather than finite partial maps. The encodings differ only
   when comparing against an absent entry (`Some x ⊑ None` is false in the
   Coq), or when the race detector adds an id to an absent entry (a no-op in
   the Coq). Neither happens here: every thread view and the race detector
   contain every location from the start, and `GenInv.cur` proves
   `cur(l).w ≥ 1`.
4. **Memory** is a list of messages per location rather than
   `gmap (loc * time)`. There is no `DVal`, since nothing is deallocated. An
   uninitialized value (`AVal`) is `none`, and a read of it hands `none` to the
   program, where the Coq's language turns it into poison.
5. **Initial state.** Every location starts with one message at time 1: its
   initial value, or `none` for the chunks, which `create` leaves
   uninitialized. The race detector has seen those non-atomic writes, and every
   thread starts from `forkView` of a view containing them. This stands in for
   the allocation and initialization before the threads are forked. The thread
   pool is fixed, with no `fork`.
6. **Fresh read ids**: any id not yet recorded, rather than the Coq's canonical
   `fresh`. This allows more behaviors.
7. **`rel ⊑ cur ⊑ acq`** is a separate predicate (`TView.Wf`), proved invariant
   in `Wf.lean`, rather than proof fields of the record.
8. **Programs** are per-thread state machines rather than the λ-calculus of
   `lang.v`. Reads are receptive by construction: continuations are functions
   of the value read.
9. **The combined step** (`lang.v` `impure_step`, appendix Fig. 10) requires
   `drf_pre` for the event of the current instruction. `drf_pre` does not
   depend on the value read, so this is the Coq's condition. `Racy` flags any
   thread whose next instruction fails `drf_pre`, whether or not the machine
   could take the event. That is stronger than the Coq's stuckness, so
   `no_race` implies the Coq's notion.

## Deviations from the Rust code

- The chunk of a buffer is one non-atomic location holding the whole payload.
  That is coarser than bytes, and conservative for races.
- Values are integers: `false = 0`, `true = 1`, `NO_SEQ = -1` (for
  `u64::MAX`). Sequence numbers never wrap.
- One `SendPipe` (its `&mut self` makes a single writer) and one `RecvPipe`
  shared by all receivers. Each receiver holds one ticket at a time and runs
  forever (`request_ticket`, then `try_recv` until `Ok`, then again). A
  receiver that stops while holding a ticket strands a buffer, which the
  documentation of `request_ticket` forbids. A `try_recv` returning `None`, and
  a callback returning `Err`, both retry with the same ticket.
- The sender sends exactly `M` messages, with arbitrary payloads and lengths,
  and chooses nondeterministically, per message, whether the send blocks.
  The callback chooses `Ok` or `Err` nondeterministically.
- `alloc_buffer`, `try_recv` and the blocking wait are the loops in the Rust
  code, unrolled one load per step.

## Not done yet

- Stage 2: mechanize RC11 ⇒ ORC11 (every RC11-consistent execution is an
  ORC11 run), so that the trust base shrinks to the RC11 axioms.
- Optional herdtools7 cross-check on small litmus tests.
