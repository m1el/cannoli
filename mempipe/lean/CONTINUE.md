# Continue: Lean model of mempipe on ORC11

Handoff for continuing this work in a new session (moved to `corey`, the
64-core Linux box: the Mac has ~11 GB free, too little for Mathlib builds).

## Goal (decided with the user)

A Lean model of mempipe's protocol proving, for **arbitrary** numbers of
buffers, receivers and messages:

1. **Delivery is correct**: every received message has exactly the payload and
   length the sender wrote for that sequence number, and each sequence number
   is received at most once.
2. **No memory-ordering violations**: no data race on the chunk bytes (ORC11's
   race detector never fires), and the `debug_assert!(client_owned)` in
   `try_recv` can never fail.
3. **No stranding**: from every reachable state there is a continuation that
   delivers every sent message.

Decisions and constraints:

- **Memory model: a faithful Lean port of ORC11** (Dang, Jourdan, Kaiser,
  Dreyer, "RustBelt Meets Relaxed Memory", POPL 2020), not a custom machine.
  The user wants a reusable, established rule set rather than bespoke rules.
  Port rule by rule, cite the Coq source for each, and list every deviation.
- **Stage 2 (later)**: mechanize RC11 ⇒ ORC11 (every RC11-consistent execution
  is an ORC11 run), upgrading the appendix's paper sketch to a checked theorem,
  so the trust base shrinks to the RC11 axioms. Stage 1 must not depend on it.
- **Progress** is proved for continuations whose loads read the latest write
  (trivially RC11-consistent); no fair-liveness theorem.
- **Mathlib is OK.** Lean `v4.34.0` (same as `../rearm-barrier`), Mathlib tag
  `v4.34.0` (exists, `5ed2965`).
- **At most 3 subagents** for the whole task (user's explicit limit).
- Optional cross-check: herdtools7 with its RC11 `.cat` model on small mempipe
  litmus tests vs exhaustive exploration of the Lean machine.

## State of the repo

- Branch `mempipe-lean-orc11`, from `origin/main` at `cbb9c62` (PR #23 merged:
  heap-backed `create_local`/`open_raw` Miri harness; PR #22: the stranded
  buffer fix).
- `mempipe/lean/`: `lakefile.toml` (Mathlib dep, libs `ORC11` and `Mempipe`),
  `lean-toolchain`, `.gitignore`. **No Lean sources yet.** Run `lake update`
  then `lake exe cache get` on corey (was interrupted on the Mac).
- Rust toolchain in the repo is still `nightly-2024-03-01` (not relevant to the
  Lean work).

## The protocol being verified (`mempipe/src/lib.rs` on main)

Shared per buffer `i < N`: `client_owned[i]: AtomicBool` (init false),
`client_len[i]: AtomicUsize`, `client_seq[i]: AtomicU64` (init `NO_SEQ =
u64::MAX`), `chunks[i]` (plain bytes). Also `cur_seq: AtomicU64` (sender only)
and, in `RecvPipe`, the ticket counter `seq: AtomicU64`.

Sender (one thread; `&mut self` makes it one writer):

- `alloc_buffer` (~L318): loop over `i in 0..N`, `client_owned[i].load(Acquire)`;
  first `false` wins.
- write chunk bytes (plain writes; `send` or `send_raw`, length ≤ CHUNK_SIZE).
- `ChunkWriter::drop` (~L453):
  1. `client_len[i].store(len, Relaxed)`
  2. `client_owned[i].store(true, Relaxed)`
  3. `seq = cur_seq.fetch_add(1, Relaxed)`
  4. `client_seq[i].store(seq, Release)`
  5. if blocking: spin `client_owned[i].load(Relaxed)` until false.

Receivers (any number, sharing one `RecvPipe`; each holds one ticket):

- `request_ticket` (~L603): `seq.fetch_add(1, Relaxed)`.
- `try_recv` (~L619): for `i in 0..N`:
  1. `client_seq[i].load(Acquire)`; skip if ≠ ticket.
  2. `debug_assert!(client_owned[i].load(Relaxed))`.
  3. `client_len[i].load(Relaxed)`, read `len` chunk bytes (plain reads),
     run the callback.
  4. callback `Ok`: `client_owned[i].store(false, Release)`, new ticket.
     callback `Err`: keep the ticket, nothing stored.

Earlier empirical results (Miri weak-memory emulation, every subset of
orderings weakened, see branch `mempipe-fix-stranded-buffer-backup`): exactly
four orderings are required, one Release/Acquire pair per direction:
`client_seq` store Release / load Acquire, and `client_owned = false` store
Release / `alloc_buffer`'s load Acquire. Weakening `client_seq` breaks the
`debug_assert` and yields stale lengths. **Use this as a sanity check**: once
the encoding is parameterized by orderings, the proofs must fail (or
counterexamples exist) for each weakened variant.

## ORC11 sources

- Technical appendix: <https://plv.mpi-sws.org/rustbelt/rbrlx/appendix.pdf>.
  Read pages as images (`Read` with `pages`), `pdftotext` mangles the rules.
  Page 8: Fig. 6 view helpers. Page 9: Fig. 7 machine semantics. Page 10:
  Fig. 8 DRF precondition. Page 11: Fig. 9 DRF postcondition. Page 12:
  Figs. 10-11 combined step and threadpool. §2 (pp. 13-23): correspondence to
  RC11 (declarative semantics, "operational graph semantics", OGS → ORC11);
  needed for stage 2.
- Coq development: `git clone https://gitlab.mpi-sws.org/iris/gpfsl.git`
  (read at commit `6cb903691a1553a3cbe4c3fede7caa41330bcfbb`). Files in
  `gpfsl/orc11/`: `thread.v` (L80-356: read/write steps, fences, drf_pre,
  drf_post, `machine_step`), `tview.v` (L36-54 `threadView`; L158-208
  `read_tview`, `read_helper`, `write_tview`, `write_Rw`, `write_helper`),
  `memory.v` (L15 `baseMessage`, L641 `message`, L755 `memory_addins`, L963
  `memory_write`), `view.v` (L9 `timeInfo`), `mem_order.v`, `event.v`.
  The thread pool / language instantiation is under `gpfsl/lang/`.

## ORC11 rules, as extracted (fragment mempipe needs)

Types: `Time = ℕ+`. `TimeInfo = {w : Time, aw nr ar : finite sets of ids}`.
`View = Loc ⇀ TimeInfo`, pointwise join; `⊑` pointwise (`w` by ≤, sets by ⊆).
`ThreadView = {rel, cur, acq : View}` with `rel ⊑ cur ⊑ acq` (the appendix
also has `frel` and per-location `rel`; the Coq has a single `rel` view, follow
the Coq). `Msg = {loc, to : Time, val, rel : Option View}`. Memory is a finite
map `(loc, time) ↦ {val, rel}`. Race detector global state `𝓝 : View`.
Orders: `na ⊑ rlx ⊑ acqrel ⊑ sc`.

Read of message `m = (l, t, v, R)` with order `o`, fresh read id `r`
(`read_helper`):

- require `cur(l).w ≤ t` and `R(l).w ≤ t`
- `V = [l ↦ {w = t, aw = ∅, nr = (o = na ? {r} : ∅), ar = (rlx ⊑ o ? {r} : ∅)}]`
- `cur' = acqrel ⊑ o ? cur ⊔ V ⊔ R : cur ⊔ V`
- `acq' = rlx ⊑ o ? acq ⊔ V ⊔ R : acq ⊔ V`; `rel` unchanged.
- message must be in memory (the Coq also requires the location allocated).

Write at fresh time `t` (no message at `(l, t)`), order `o`, with `Rr` (the
view of the message an update read, else ∅) (`write_helper`, `memory_write`):

- require `cur(l).w < t`
- `V = [l ↦ {w = t, aw = (rlx ⊑ o ? {t} : ∅), nr = ∅, ar = ∅}]`
- `cur' = cur ⊔ V`, `acq' = acq ⊔ V`, `rel` unchanged
- message view `Rw = rlx ⊑ o ? Some((acqrel ⊑ o ? cur ⊔ V : V) ⊔ rel ⊔ Rr) : None`
- the Coq `memory_write` also requires the new message's view closed in the
  new memory and some existing message at `l` with time ≤ t.

Update (RMW) reading `m1` at `t_r` and writing at `t_w = t_r + 1` (must be
free): the read step, then the write step from the post-read view with
`Rr = view of m1`.

DRF precondition (`drf_pre`, Fig. 8), for a thread with view `cur`:

- read, `na`: every message at `l` has time ≤ `cur(l).w`; `𝓝(l).aw ⊆ cur(l).aw`;
  and (all reads) `𝓝(l).w ≤ cur(l).w`.
- read, atomic: `𝓝(l).w ≤ cur(l).w`.
- write, `na`: every message at `l` has time ≤ `cur(l).w`; `𝓝(l).aw ⊆ cur(l).aw`;
  `𝓝(l).ar ⊆ cur(l).ar`; and (all writes) `𝓝(l).w ≤ cur(l).w`,
  `𝓝(l).nr ⊆ cur(l).nr`.
- write, atomic: `𝓝(l).w ≤ cur(l).w`, `𝓝(l).nr ⊆ cur(l).nr`.
- update: both the read and the write preconditions.

DRF postcondition (`drf_post`, Fig. 9): na read adds `r` to `𝓝(l).nr`
(`r` fresh); atomic read adds `r` to `𝓝(l).ar`; na write sets `𝓝(l).w := t`;
atomic write adds `t` to `𝓝(l).aw`; update adds the read id to `ar` and `t_w`
to `aw`.

Combined step (Fig. 10): a memory event is taken only if **for every** way the
machine could take it, `RaceFree` holds; otherwise the program is racy (UB).
Our theorem: in every reachable state, the next event of every thread
satisfies `drf_pre` (it doesn't depend on which message a read picks).
Thread pool (Fig. 11): pick a thread, take a combined step; `fork` gives the
child `ForkView(V) = (∅, ∅, V.cur, V.cur)`.

## Planned fragment and deviations (document all in the Lean README)

- Only read / write / update events; no alloc, dealloc, fences, SC, syscalls
  (mempipe uses none). Start from an initialized memory: one message per
  location at time 1, all threads' views include it (standing in for the
  allocation and initialization before the threads are forked).
- Views as total functions `Loc → TimeInfo` with `w = 0` for "no entry"
  (real messages have time ≥ 1); isomorphic to the partial maps.
- Fresh read ids: any id not already present (the Coq picks a canonical fresh
  one); only uniqueness matters.
- Values `ℕ`; an update is `f : ℕ → ℕ` (fetch_add is `(· + 1)`).
- The chunk of buffer `i` is one non-atomic location holding the payload
  (coarser than bytes: conservative for races).
- Programs are per-thread state machines, not ORC11's expression language.
  Make reads receptive by construction: an instruction is
  `read l o (k : ℕ → S)`, `write l v o k`, `update l f or ow (k : ℕ → S)`,
  `choose (k : Bool → S)` (callback Ok/Err, blocking or not), `halt`, plus a
  `fault` state for the `debug_assert`. A relation-style program could refuse
  values and silently drop behaviors.

## Planned Lean layout

- `ORC11/Basic.lean`: orders, `TimeInfo`, `View` (lattice), `TView`, messages,
  memory, events.
- `ORC11/Machine.lean`: read/write/update steps, `DrfPre`, `DrfPost`, each with
  a comment citing the Coq definition and line.
- `ORC11/Program.lean`: instructions, programs, configurations (per-thread
  local state + thread view, memory, `𝓝`), step, reachability, `Racy`.
- `Mempipe/Program.lean`: sender and receivers for parameters `N`, `R`, `M`
  (messages to send), plus ghost logs of what was sent and received.
- `Mempipe/Invariant.lean`, `Mempipe/Safety.lean`, `Mempipe/Progress.lean`.
- Later: `ORC11/RC11.lean` (axiomatic RC11) and the correspondence; a bounded
  explorer for the herd cross-check; `#print axioms` audit script as in
  `../rearm-barrier/scripts/check_axioms.sh`.

## Pitfalls already hit (don't repeat)

- Test/harness bookkeeping must not add synchronization (e.g. a SeqCst counter
  between receivers masks the stale-`owned` bug). Same for ghost state: it
  must not constrain executions.
- A receiver that stops while holding a ticket strands a buffer; progress
  statements must account for receivers that are mid-callback or retrying.

## Next steps

1. `lake update && lake exe cache get` in `mempipe/lean` on corey.
2. Write `ORC11/Basic.lean` and `ORC11/Machine.lean` from the rules above,
   checking each against Figs. 6-9 and the Coq files.
3. Thread pool semantics, then the mempipe encoding, then invariants.
