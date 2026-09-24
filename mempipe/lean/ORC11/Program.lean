import ORC11.Machine
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

/-!
# ORC11: programs and the thread pool

The Coq instantiates ORC11 with the λ-calculus of `gpfsl/lang/lang.v`. We
replace it with per-thread state machines, each state yielding one
instruction. Reads are receptive by construction: the continuation of a read
or update is a function of the value read, so a program can never refuse a
value (which would silently drop behaviors).

The combined step (`lang.v` L780 `impure_step`, appendix Fig. 10) takes a
memory event only if `drf_pre` holds for it. Our `DrfPre` for a read or update
does not depend on the value read, so "for every event the thread could take"
reduces to "for the event of the current instruction". We call a
configuration *racy* when some thread's next instruction fails `drf_pre`,
whether or not the machine could take the event; this is stronger than the
Coq's stuckness, so proving the absence of races here implies it there.

The thread pool (appendix Fig. 11) is fixed: there is no `fork`. Every thread
starts from `forkView` (`lang.v` L767) of the view the forking thread has
after allocating and initializing all locations with non-atomic writes. We
model that as a single message at time 1 per location (value `none` for
locations left uninitialized, the Coq's `AVal`), a race detector that has seen
those writes, and thread views containing them.
-/

namespace ORC11

variable {Loc Val : Type} [DecidableEq Loc]

/-- One instruction of a thread whose local states are `S`. -/
inductive Instr (Loc Val S : Type) where
  /-- Read `l` with order `o`, continue with the value read. -/
  | read (l : Loc) (o : MemOrder) (k : Option Val → S)
  /-- Write `v` to `l` with order `o`. -/
  | write (l : Loc) (o : MemOrder) (v : Val) (k : S)
  /-- Atomically replace the value `v` of `l` by `f v` (read with `or`, write
  with `ow`), continue with `v`. -/
  | update (l : Loc) (or ow : MemOrder) (f : Val → Val) (k : Val → S)
  /-- A silent, nondeterministic choice. -/
  | choose (k : Bool → S)
  /-- The thread has finished. -/
  | halt
  /-- The thread hit undefined behavior or a failed assertion. -/
  | fault

/-- The `drf_pre` condition of the next instruction; `True` for instructions
without a memory event. -/
def Instr.DrfPreOk {S : Type} (𝓝 : View Loc) (𝓥 : TView Loc) (M : Memory Loc Val) :
    Instr Loc Val S → Prop
  | .read l o _ => DrfPreRead l 𝓝 𝓥 M o
  | .write l o _ _ => DrfPreWrite l 𝓝 𝓥 M o
  | .update l or ow _ _ => DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow
  | .choose _ => True
  | .halt => True
  | .fault => True

/-- A thread step: the combined step of `lang.v` L774 `base_step` for a
thread running `prog`, from local state `s`, thread view `𝓥`, memory `M` and
race detector state `𝓝`. -/
inductive TStep {S : Type} (prog : S → Instr Loc Val S) :
    S → TView Loc → Memory Loc Val → View Loc →
      S → TView Loc → Memory Loc Val → View Loc → Prop
  | read {s 𝓥 M 𝓝 l o k tr 𝓥' 𝓝'} {m : Msg Loc Val}
      (INSTR : prog s = .read l o k)
      (DRFPre : DrfPre 𝓝 𝓥 M (.read l m.val o))
      (PStep : MachineStep 𝓥 M (.read l m.val o) (some tr) [] 𝓥' M)
      (DRFPost : DrfPost 𝓝 (.read l m.val o) (some tr) [] 𝓝') :
      TStep prog s 𝓥 M 𝓝 (k m.val) 𝓥' M 𝓝'
  | write {s 𝓥 M 𝓝 l o v k 𝓥' M' 𝓝'} {m : Msg Loc Val}
      (INSTR : prog s = .write l o v k)
      (DRFPre : DrfPre 𝓝 𝓥 M (.write l v o))
      (PStep : MachineStep 𝓥 M (.write l v o) none [(l, m)] 𝓥' M')
      (DRFPost : DrfPost 𝓝 (.write l v o) none [(l, m)] 𝓝') :
      TStep prog s 𝓥 M 𝓝 k 𝓥' M' 𝓝'
  | update {s 𝓥 M 𝓝 l or ow f k v tr 𝓥' M' 𝓝'} {m : Msg Loc Val}
      (INSTR : prog s = .update l or ow f k)
      (DRFPre : DrfPre 𝓝 𝓥 M (.update l v (f v) or ow))
      (PStep : MachineStep 𝓥 M (.update l v (f v) or ow) (some tr) [(l, m)] 𝓥' M')
      (DRFPost : DrfPost 𝓝 (.update l v (f v) or ow) (some tr) [(l, m)] 𝓝') :
      TStep prog s 𝓥 M 𝓝 (k v) 𝓥' M' 𝓝'
  | choose {s 𝓥 M 𝓝 k} (b : Bool)
      (INSTR : prog s = .choose k) :
      TStep prog s 𝓥 M 𝓝 (k b) 𝓥 M 𝓝

/-- A configuration of a fixed pool of threads `ι`, thread `i` having local
states `S i`: per-thread local state and view, the memory, and the race
detector state (`lang.v` `state`, without the SC view, which only SC fences
use). -/
structure Config (ι : Type) (S : ι → Type) (Loc Val : Type) where
  th : (i : ι) → S i × TView Loc
  mem : Memory Loc Val
  na : View Loc

section Pool

variable {ι : Type} [DecidableEq ι] {S : ι → Type}
  (prog : (i : ι) → S i → Instr Loc Val (S i))

/-- Appendix Fig. 11: some thread takes a step. -/
inductive Step : Config ι S Loc Val → Config ι S Loc Val → Prop
  | mk (c : Config ι S Loc Val) (i : ι) {s' : S i} {𝓥' M' 𝓝'}
      (h : TStep (prog i) (c.th i).1 (c.th i).2 c.mem c.na s' 𝓥' M' 𝓝') :
      Step c ⟨Function.update c.th i (s', 𝓥'), M', 𝓝'⟩

/-- The view of every thread after the initialization: every location was
written non-atomically at time 1. -/
def initTime : TimeInfo := ⟨1, ∅, ∅, ∅⟩

/-- `forkView` of the initializing thread's view. -/
def initTView : TView Loc where
  rel := ⊥
  cur := fun _ => initTime
  acq := fun _ => initTime

/-- The initial configuration: local states `s0`, initial values `v0`. -/
def initConfig (s0 : (i : ι) → S i) (v0 : Loc → Option Val) : Config ι S Loc Val where
  th i := (s0 i, initTView)
  mem l := [⟨1, v0 l, none⟩]
  na _ := initTime

/-- Configurations reachable from the initial one. -/
def Reachable (s0 : (i : ι) → S i) (v0 : Loc → Option Val)
    (c : Config ι S Loc Val) : Prop :=
  Relation.ReflTransGen (Step prog) (initConfig s0 v0) c

/-- Some thread's next instruction would race. -/
def Racy (c : Config ι S Loc Val) : Prop :=
  ∃ i, ¬ (prog i (c.th i).1).DrfPreOk c.na (c.th i).2 c.mem

/-- Some thread is at a fault. -/
def Faulty (c : Config ι S Loc Val) : Prop :=
  ∃ i, prog i (c.th i).1 = .fault

end Pool

end ORC11
