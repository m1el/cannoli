import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max

/-!
# ORC11: basic definitions

A Lean port of the data structures of ORC11 (Dang, Jourdan, Kaiser, Dreyer,
"RustBelt Meets Relaxed Memory", POPL 2020), following the Coq development
`gpfsl` at commit `6cb903691a1553a3cbe4c3fede7caa41330bcfbb`, directory
`gpfsl/orc11/`. Every definition cites the Coq definition it ports.

Deviations from the Coq (see also `README.md`):

* Times and read ids are `ℕ`; the Coq uses `positive`. Real messages have time
  `≥ 1`, and time `0` stands for "no entry".
* Views are total functions `Loc → TimeInfo`; the Coq uses finite partial maps
  `gmap loc timeInfo`. An absent entry is `⊥ = ⟨0, ∅, ∅, ∅⟩`.
* Memory is a total function from locations to cells (lists of messages); the
  Coq uses `gmap (loc * time) baseMessage`. There is no allocation or
  deallocation: every location starts out allocated (see `Program.lean`).
* The thread-view invariants `rel ⊑ cur ⊑ acq` are a separate predicate
  (`TView.Wf`) instead of proof fields of the record.
-/

namespace ORC11

/-! ## Memory orders (`mem_order.v`) -/

/-- `mem_order.v` L5 `memOrder`. -/
inductive MemOrder where
  | na
  | rlx
  | acqrel
  | sc
  deriving DecidableEq, Repr

namespace MemOrder

/-- Rank realising the total order of `mem_order.v` L7 `memOrder_le`:
`NonAtomic ⊑ Relaxed ⊑ AcqRel ⊑ SeqCst`. -/
def rank : MemOrder → ℕ
  | na => 0
  | rlx => 1
  | acqrel => 2
  | sc => 3

instance : LE MemOrder := ⟨fun a b => a.rank ≤ b.rank⟩

instance (a b : MemOrder) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.rank ≤ b.rank))

@[simp] theorem rlx_le_na : ¬ (rlx ≤ na) := by decide
@[simp] theorem rlx_le_rlx : rlx ≤ rlx := by decide
@[simp] theorem rlx_le_acqrel : rlx ≤ acqrel := by decide
@[simp] theorem rlx_le_sc : rlx ≤ sc := by decide
@[simp] theorem acqrel_le_na : ¬ (acqrel ≤ na) := by decide
@[simp] theorem acqrel_le_rlx : ¬ (acqrel ≤ rlx) := by decide
@[simp] theorem acqrel_le_acqrel : acqrel ≤ acqrel := by decide
@[simp] theorem acqrel_le_sc : acqrel ≤ sc := by decide

end MemOrder

/-! ## Time information and views (`view.v`) -/

/-- `view.v` L9 `timeInfo`: the timestamp of the latest write seen (`w`), and
the ids of atomic writes (`aw`), non-atomic reads (`nr`) and atomic reads
(`ar`) seen, used by the race detector. -/
@[ext]
structure TimeInfo where
  w : ℕ
  aw : Finset ℕ
  nr : Finset ℕ
  ar : Finset ℕ
  deriving DecidableEq

namespace TimeInfo

/-- `view.v` L39 `timeInfo_sqsubseteq` and L45 `timeInfo_Lat`: componentwise
order and join (`max` on times, union on id sets). -/
instance : SemilatticeSup TimeInfo where
  le a b := a.w ≤ b.w ∧ a.aw ⊆ b.aw ∧ a.nr ⊆ b.nr ∧ a.ar ⊆ b.ar
  le_refl _ := ⟨le_rfl, subset_rfl, subset_rfl, subset_rfl⟩
  le_trans _ _ _ h1 h2 :=
    ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
      h1.2.2.2.trans h2.2.2.2⟩
  le_antisymm _ _ h1 h2 := by
    ext1
    · exact le_antisymm h1.1 h2.1
    · exact Finset.Subset.antisymm h1.2.1 h2.2.1
    · exact Finset.Subset.antisymm h1.2.2.1 h2.2.2.1
    · exact Finset.Subset.antisymm h1.2.2.2 h2.2.2.2
  sup a b := ⟨max a.w b.w, a.aw ∪ b.aw, a.nr ∪ b.nr, a.ar ∪ b.ar⟩
  le_sup_left _ _ :=
    ⟨le_max_left _ _, Finset.subset_union_left, Finset.subset_union_left,
      Finset.subset_union_left⟩
  le_sup_right _ _ :=
    ⟨le_max_right _ _, Finset.subset_union_right, Finset.subset_union_right,
      Finset.subset_union_right⟩
  sup_le _ _ _ h1 h2 :=
    ⟨max_le h1.1 h2.1, Finset.union_subset h1.2.1 h2.2.1,
      Finset.union_subset h1.2.2.1 h2.2.2.1, Finset.union_subset h1.2.2.2 h2.2.2.2⟩

/-- The absent entry. -/
instance : OrderBot TimeInfo where
  bot := ⟨0, ∅, ∅, ∅⟩
  bot_le a := ⟨Nat.zero_le _, Finset.empty_subset _, Finset.empty_subset _,
    Finset.empty_subset _⟩

theorem le_def {a b : TimeInfo} :
    a ≤ b ↔ a.w ≤ b.w ∧ a.aw ⊆ b.aw ∧ a.nr ⊆ b.nr ∧ a.ar ⊆ b.ar := Iff.rfl

@[simp] theorem sup_w (a b : TimeInfo) : (a ⊔ b).w = max a.w b.w := rfl
@[simp] theorem sup_aw (a b : TimeInfo) : (a ⊔ b).aw = a.aw ∪ b.aw := rfl
@[simp] theorem sup_nr (a b : TimeInfo) : (a ⊔ b).nr = a.nr ∪ b.nr := rfl
@[simp] theorem sup_ar (a b : TimeInfo) : (a ⊔ b).ar = a.ar ∪ b.ar := rfl
@[simp] theorem bot_w : (⊥ : TimeInfo).w = 0 := rfl
@[simp] theorem bot_aw : (⊥ : TimeInfo).aw = ∅ := rfl
@[simp] theorem bot_nr : (⊥ : TimeInfo).nr = ∅ := rfl
@[simp] theorem bot_ar : (⊥ : TimeInfo).ar = ∅ := rfl

theorem w_mono {a b : TimeInfo} (h : a ≤ b) : a.w ≤ b.w := h.1
theorem aw_mono {a b : TimeInfo} (h : a ≤ b) : a.aw ⊆ b.aw := h.2.1
theorem nr_mono {a b : TimeInfo} (h : a ≤ b) : a.nr ⊆ b.nr := h.2.2.1
theorem ar_mono {a b : TimeInfo} (h : a ≤ b) : a.ar ⊆ b.ar := h.2.2.2

end TimeInfo

/-- `view.v` L78 `view`: a view maps each location to the time information a
thread (or message, or the race detector) has about it. Total, with `⊥` for
absent entries; the order and join are pointwise (`gmap_Lat`). -/
abbrev View (Loc : Type) := Loc → TimeInfo

namespace View

variable {Loc : Type} [DecidableEq Loc]

/-- The singleton view `{[l := x]}`. -/
def single (l : Loc) (x : TimeInfo) : View Loc :=
  fun l' => if l' = l then x else ⊥

@[simp] theorem single_self (l : Loc) (x : TimeInfo) : single l x l = x := by
  simp [single]

@[simp] theorem single_ne {l l' : Loc} (x : TimeInfo) (h : l' ≠ l) :
    single l x l' = ⊥ := by
  simp [single, h]

/-- Alter the entry at `l` (`partial_alter` on a present entry). -/
def alter (V : View Loc) (l : Loc) (f : TimeInfo → TimeInfo) : View Loc :=
  Function.update V l (f (V l))

@[simp] theorem alter_self (V : View Loc) (l : Loc) (f : TimeInfo → TimeInfo) :
    alter V l f l = f (V l) := by
  simp [alter]

@[simp] theorem alter_ne (V : View Loc) {l l' : Loc} (f : TimeInfo → TimeInfo)
    (h : l' ≠ l) : alter V l f l' = V l' := by
  simp [alter, h]

end View

/-! ## Thread views (`tview.v`) -/

/-- `tview.v` L36 `threadView`: the release view `rel` (the latest release or
SC fence), the current view `cur`, and the acquire view `acq`. -/
@[ext]
structure TView (Loc : Type) where
  rel : View Loc
  cur : View Loc
  acq : View Loc

/-- The proof fields `rel_cur_dec` and `cur_acq_dec` of `threadView`. -/
def TView.Wf {Loc : Type} (𝓥 : TView Loc) : Prop :=
  𝓥.rel ≤ 𝓥.cur ∧ 𝓥.cur ≤ 𝓥.acq

/-! ## Messages and memory (`memory.v`) -/

/-- A message in a location's cell: `memory.v` L641 `message` without the
location (cells are per location), with `mbase` (L15 `baseMessage`) inlined.
The value is `none` for the Coq `AVal` (allocated, uninitialized) and `some v`
for `VVal v`; there is no `DVal` since we have no deallocation. `view` is
`mrel`: `none` for non-atomic writes, the message view for atomic ones. -/
structure Msg (Loc Val : Type) where
  time : ℕ
  val : Option Val
  view : Option (View Loc)

/-- Memory: the cell (list of messages) of every location. -/
abbrev Memory (Loc Val : Type) := Loc → List (Msg Loc Val)

/-- `memory.v` L456 `closed_view`: every time in the view is bounded by a
message at its location. -/
def View.Closed {Loc Val : Type} (V : View Loc) (M : Memory Loc Val) : Prop :=
  ∀ l, (V l).w = 0 ∨ ∃ m ∈ M l, (V l).w ≤ m.time

/-- `memory.v` L476 `closed_view_opt`. -/
def View.ClosedOpt {Loc Val : Type} (V : Option (View Loc))
    (M : Memory Loc Val) : Prop :=
  ∀ W, V = some W → W.Closed M

/-- `memory.v` L674 `message_wf`: an atomic message's view records its own
time at its own location. -/
def Msg.Wf {Loc Val : Type} (l : Loc) (m : Msg Loc Val) : Prop :=
  ∀ V, m.view = some V → (V l).w = m.time

/-- `m` is the latest message of cell `C`. -/
def IsLatest {Loc Val : Type} (C : List (Msg Loc Val)) (m : Msg Loc Val) : Prop :=
  m ∈ C ∧ ∀ m' ∈ C, m'.time ≤ m.time

end ORC11
