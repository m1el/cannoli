import ORC11.Basic

/-!
# ORC11: the memory machine and the race detector

Ports of `gpfsl/orc11/tview.v` (`read_helper`, `write_helper`),
`memory.v` (`memory_write`) and `thread.v` (`read_step`, `write_step`,
`machine_step`, `drf_pre`, `drf_post`), restricted to reads, writes and
updates (no fences, allocation, deallocation or system calls).
-/

namespace ORC11

variable {Loc Val : Type} [DecidableEq Loc]

/-! ## Events (`event.v`) -/

/-- `event.v` L65 `event`, restricted to memory accesses. Read values are
memory values (`none` is `AVal`); written values are proper values. -/
inductive Event (Loc Val : Type) where
  | read (l : Loc) (v : Option Val) (o : MemOrder)
  | write (l : Loc) (v : Val) (o : MemOrder)
  | update (l : Loc) (vr vw : Val) (or ow : MemOrder)

/-! ## Thread-view updates (`tview.v`) -/

/-- The view `V` of `tview.v` L179 `read_helper`: the read message's time and
the read id `tr`, recorded as an atomic or non-atomic read. -/
def readView (o : MemOrder) (l : Loc) (t tr : ℕ) : View Loc :=
  View.single l (if MemOrder.rlx ≤ o then ⟨t, ∅, ∅, {tr}⟩ else ⟨t, ∅, {tr}, ∅⟩)

/-- `tview.v` L158 `read_tview`. -/
def readTView (𝓥 : TView Loc) (o : MemOrder) (R V : View Loc) : TView Loc where
  rel := 𝓥.rel
  cur := if MemOrder.acqrel ≤ o then 𝓥.cur ⊔ V ⊔ R else 𝓥.cur ⊔ V
  acq := if MemOrder.rlx ≤ o then 𝓥.acq ⊔ V ⊔ R else 𝓥.acq ⊔ V

/-- `tview.v` L175 `read_helper`: reading the message at time `t` of `l`,
whose view is `R` (`∅` for non-atomic messages), with read id `tr`. -/
structure ReadHelper (𝓥 : TView Loc) (o : MemOrder) (l : Loc) (t tr : ℕ)
    (R : View Loc) (𝓥' : TView Loc) : Prop where
  pln : (𝓥.cur l).w ≤ t
  pln2 : (R l).w ≤ t
  eq : 𝓥' = readTView 𝓥 o R (readView o l t tr)

/-- The view `V` of `tview.v` L187 section `write`. -/
def writeView (o : MemOrder) (l : Loc) (t : ℕ) : View Loc :=
  View.single l (if MemOrder.rlx ≤ o then ⟨t, {t}, ∅, ∅⟩ else ⟨t, ∅, ∅, ∅⟩)

/-- `tview.v` L194 `write_tview`. -/
def writeTView (𝓥 : TView Loc) (o : MemOrder) (l : Loc) (t : ℕ) : TView Loc where
  rel := 𝓥.rel
  cur := 𝓥.cur ⊔ writeView o l t
  acq := 𝓥.acq ⊔ writeView o l t

/-- `tview.v` L201 `write_Rw`: the view of the written message. `Rr` is the
view of the message read by an update, `⊥` for plain writes. -/
def writeRw (𝓥 : TView Loc) (o : MemOrder) (l : Loc) (t : ℕ) (Rr : View Loc) :
    Option (View Loc) :=
  if MemOrder.rlx ≤ o then
    some ((if MemOrder.acqrel ≤ o then 𝓥.cur ⊔ writeView o l t
      else writeView o l t) ⊔ 𝓥.rel ⊔ Rr)
  else none

/-- `tview.v` L204 `write_helper`. -/
structure WriteHelper (𝓥 : TView Loc) (o : MemOrder) (l : Loc) (t : ℕ)
    (Rr : View Loc) (Rw : Option (View Loc)) (𝓥' : TView Loc) : Prop where
  rlx : (𝓥.cur l).w < t
  eqRw : Rw = writeRw 𝓥 o l t Rr
  eq : 𝓥' = writeTView 𝓥 o l t

/-! ## Memory writes (`memory.v`) -/

/-- Add message `m` to the cell of `l`. -/
def Memory.add (M : Memory Loc Val) (l : Loc) (m : Msg Loc Val) : Memory Loc Val :=
  Function.update M l (m :: M l)

/-- `memory.v` L963 `memory_write`, with `memory_addins` (L755) and
`cell_addins` (L107): the time is free, the message is well formed, its view
is closed in the new memory, and some message of the cell is not later.
`ISVAL` holds by construction (`m.val = some _`); `ALLOC` holds since every
location is allocated. -/
structure MemoryWrite (M : Memory Loc Val) (l : Loc) (m : Msg Loc Val)
    (M' : Memory Loc Val) : Prop where
  fresh : ∀ m' ∈ M l, m'.time ≠ m.time
  eq : M' = M.add l m
  wf : m.Wf l
  closed : View.ClosedOpt m.view M'
  isval : m.val.isSome
  lall : ∃ m' ∈ M l, m'.time ≤ m.time

/-! ## Thread steps (`thread.v`) -/

/-- `thread.v` L80 `read_step`: read message `m` of `l`. `ALLOC` holds since
every location is allocated. -/
structure ReadStep (𝓥 : TView Loc) (M : Memory Loc Val) (tr : ℕ) (l : Loc)
    (m : Msg Loc Val) (o : MemOrder) (𝓥' : TView Loc) : Prop where
  read : ReadHelper 𝓥 o l m.time tr (m.view.getD ⊥) 𝓥'
  mem : m ∈ M l

/-- `thread.v` L87 `write_step`. The Coq's `V` argument is our `Rr`. -/
structure WriteStep (𝓥 : TView Loc) (M : Memory Loc Val) (l : Loc)
    (m : Msg Loc Val) (o : MemOrder) (Rr : View Loc) (𝓥' : TView Loc)
    (M' : Memory Loc Val) : Prop where
  write : MemoryWrite M l m M'
  wview : WriteHelper 𝓥 o l m.time Rr m.view 𝓥'

/-- `thread.v` L308 `machine_step`, read, write and update cases
(`PStepR`, `PStepW`, `PStepU`). The `Option ℕ` is the read id, the list the
written messages (with their locations). -/
inductive MachineStep (𝓥 : TView Loc) (M : Memory Loc Val) :
    Event Loc Val → Option ℕ → List (Loc × Msg Loc Val) → TView Loc →
      Memory Loc Val → Prop
  | read (l : Loc) (m : Msg Loc Val) (o : MemOrder) (𝓥' : TView Loc) (tr : ℕ)
      (READ : ReadStep 𝓥 M tr l m o 𝓥') :
      MachineStep 𝓥 M (.read l m.val o) (some tr) [] 𝓥' M
  | write (l : Loc) (m : Msg Loc Val) (o : MemOrder) (𝓥' : TView Loc)
      (M' : Memory Loc Val) (v : Val)
      (ISVAL : m.val = some v)
      (WRITE : WriteStep 𝓥 M l m o ⊥ 𝓥' M') :
      MachineStep 𝓥 M (.write l v o) none [(l, m)] 𝓥' M'
  | update (l : Loc) (m1 m2 : Msg Loc Val) (or ow : MemOrder)
      (𝓥2 𝓥3 : TView Loc) (M3 : Memory Loc Val) (tr : ℕ) (v1 v2 : Val)
      (ISV1 : m1.val = some v1) (ISV2 : m2.val = some v2)
      (ADJ : m2.time = m1.time + 1)
      (READ : ReadStep 𝓥 M tr l m1 or 𝓥2)
      (WRITE : WriteStep 𝓥2 M l m2 ow (m1.view.getD ⊥) 𝓥3 M3) :
      MachineStep 𝓥 M (.update l v1 v2 or ow) (some tr) [(l, m2)] 𝓥3 M3

/-! ## The race detector (`thread.v`) -/

/-- `thread.v` L147 `add_aread_id`. -/
def addARead (𝓝 : View Loc) (l : Loc) (r : ℕ) : View Loc :=
  𝓝.alter l fun p => { p with ar := insert r p.ar }

/-- `thread.v` L151 `add_nread_id`. -/
def addNRead (𝓝 : View Loc) (l : Loc) (r : ℕ) : View Loc :=
  𝓝.alter l fun p => { p with nr := insert r p.nr }

/-- `thread.v` L155 `add_awrite_id`. -/
def addAWrite (𝓝 : View Loc) (l : Loc) (w : ℕ) : View Loc :=
  𝓝.alter l fun p => { p with aw := insert w p.aw }

/-- `thread.v` L159 `set_write_time`. -/
def setWriteTime (𝓝 : View Loc) (l : Loc) (t : ℕ) : View Loc :=
  𝓝.alter l fun p => { p with w := t }

/-- `thread.v` L216 `drf_pre_write`. -/
structure DrfPreWrite (l : Loc) (𝓝 : View Loc) (𝓥 : TView Loc)
    (M : Memory Loc Val) (o : MemOrder) : Prop where
  /-- All writes must have seen all non-atomic reads. -/
  readNA : (𝓝 l).nr ⊆ (𝓥.cur l).nr
  /-- All writes must have seen all non-atomic writes. -/
  allW : (𝓝 l).w ≤ (𝓥.cur l).w
  /-- Non-atomic writes must have seen the mo-latest write and all atomic
  reads and writes. -/
  writeNA : ¬ MemOrder.rlx ≤ o →
    (∀ m ∈ M l, m.time ≤ (𝓥.cur l).w) ∧ (𝓝 l).aw ⊆ (𝓥.cur l).aw ∧
      (𝓝 l).ar ⊆ (𝓥.cur l).ar

/-- `thread.v` L227 `drf_pre_read`. -/
structure DrfPreRead (l : Loc) (𝓝 : View Loc) (𝓥 : TView Loc)
    (M : Memory Loc Val) (o : MemOrder) : Prop where
  /-- All reads must have seen all non-atomic writes. -/
  writeNA : (𝓝 l).w ≤ (𝓥.cur l).w
  /-- Non-atomic reads must have seen the mo-latest write and all atomic
  writes. -/
  allW : ¬ MemOrder.rlx ≤ o →
    (∀ m ∈ M l, m.time ≤ (𝓥.cur l).w) ∧ (𝓝 l).aw ⊆ (𝓥.cur l).aw

/-- `thread.v` L243 `drf_pre`, memory-access cases. -/
def DrfPre (𝓝 : View Loc) (𝓥 : TView Loc) (M : Memory Loc Val) :
    Event Loc Val → Prop
  | .write l _ o => DrfPreWrite l 𝓝 𝓥 M o
  | .read l _ o => DrfPreRead l 𝓝 𝓥 M o
  | .update l _ _ or ow => DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow

/-- `thread.v` L265 `drf_post_read`. The Coq picks the canonical fresh id
`fresh (𝓝 !!ar l)`; we allow any fresh id. -/
def DrfPostRead (l : Loc) (o : MemOrder) (tr : ℕ) (𝓝 𝓝' : View Loc) : Prop :=
  if MemOrder.rlx ≤ o then 𝓝' = addARead 𝓝 l tr ∧ tr ∉ (𝓝 l).ar
  else 𝓝' = addNRead 𝓝 l tr ∧ tr ∉ (𝓝 l).nr

/-- `thread.v` L272 `drf_post_write`. -/
def DrfPostWrite (l : Loc) (t : ℕ) (o : MemOrder) (𝓝 𝓝' : View Loc) : Prop :=
  if MemOrder.rlx ≤ o then 𝓝' = addAWrite 𝓝 l t else 𝓝' = setWriteTime 𝓝 l t

/-- `thread.v` L279 `drf_post_update`. -/
def DrfPostUpdate (l : Loc) (tr tw : ℕ) (𝓝 𝓝' : View Loc) : Prop :=
  𝓝' = addAWrite (addARead 𝓝 l tr) l tw ∧ tr ∉ (𝓝 l).ar

/-- `thread.v` L284 `drf_post`, memory-access cases. -/
inductive DrfPost (𝓝 : View Loc) :
    Event Loc Val → Option ℕ → List (Loc × Msg Loc Val) → View Loc → Prop
  | write (l : Loc) (m : Msg Loc Val) (v : Val) (o : MemOrder) (𝓝' : View Loc)
      (DRF : DrfPostWrite l m.time o 𝓝 𝓝') :
      DrfPost 𝓝 (.write l v o) none [(l, m)] 𝓝'
  | read (l : Loc) (tr : ℕ) (o : MemOrder) (v : Option Val) (𝓝' : View Loc)
      (DRF : DrfPostRead l o tr 𝓝 𝓝') :
      DrfPost 𝓝 (.read l v o) (some tr) [] 𝓝'
  | update (l : Loc) (m : Msg Loc Val) (or ow : MemOrder) (tr : ℕ) (vr vw : Val)
      (𝓝' : View Loc) (DRF : DrfPostUpdate l tr m.time 𝓝 𝓝') :
      DrfPost 𝓝 (.update l vr vw or ow) (some tr) [(l, m)] 𝓝'

end ORC11
