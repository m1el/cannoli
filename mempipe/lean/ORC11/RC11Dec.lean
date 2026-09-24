import ORC11.RC11
import ORC11.Closure

/-!
# Deciding RC11 consistency and races

For locations enumerated by a list, `Exec.Consistent` and `Exec.Racy` of
`RC11.lean` are decidable: every relation stays within the finitely many
events, and the closures (`eco`, `hb`, the `rf; [U]` chains of release
sequences) are computed by the proved Floyd–Warshall of `Closure.lean`. The
decisions are `Decidable` values of the propositions themselves, so running
them (as `tools/Litmus.lean` does to compare with herd7's `rc11.cat`) tests
the definitions of `RC11.lean` and nothing else.
-/

namespace ORC11.RC11

open Closure

variable {Loc Val : Type} [DecidableEq Loc] [DecidableEq Val]

namespace Label

instance (x : Label Loc Val) : Decidable x.IsRead := by cases x <;> unfold IsRead <;> infer_instance
instance (x : Label Loc Val) : Decidable x.IsWrite := by
  cases x <;> unfold IsWrite <;> infer_instance
instance (x : Label Loc Val) : Decidable x.IsUpdate := by
  cases x <;> unfold IsUpdate <;> infer_instance
instance (x : Label Loc Val) : Decidable x.IsNA := by cases x <;> unfold IsNA <;> infer_instance
instance (x : Label Loc Val) : Decidable x.AtomicW := by
  cases x <;> unfold AtomicW <;> infer_instance
instance (x : Label Loc Val) : Decidable x.RelW := by cases x <;> unfold RelW <;> infer_instance
instance (x : Label Loc Val) : Decidable x.AcqR := by cases x <;> unfold AcqR <;> infer_instance

end Label

/-- A case split on an option, with a decidable instance. -/
def optCase (o : Option ℕ) (p : Prop) (q : ℕ → Prop) : Prop :=
  match o with
  | none => p
  | some a => q a

instance (o : Option ℕ) (p : Prop) (q : ℕ → Prop) [Decidable p] [∀ a, Decidable (q a)] :
    Decidable (optCase o p q) := by
  cases o <;> unfold optCase <;> infer_instance

variable {ι : Type} [DecidableEq ι] {S : ι → Type}
  {prog : (i : ι) → S i → Instr Loc Val (S i)} {s0 : (i : ι) → S i} {v0 : Loc → Option Val}
  (G : Exec prog s0 v0)

namespace Exec

instance (a : Ev Loc) : Decidable (G.Mem a) := by cases a <;> unfold Mem <;> infer_instance
instance (a : Ev Loc) : Decidable (G.IsWrite a) := by
  cases a <;> unfold IsWrite <;> infer_instance
instance (a : Ev Loc) : Decidable (G.IsRead a) := by cases a <;> unfold IsRead <;> infer_instance
instance (a : Ev Loc) : Decidable (G.IsNA a) := by cases a <;> unfold IsNA <;> infer_instance
instance (a : Ev Loc) : Decidable (G.RelW a) := by cases a <;> unfold RelW <;> infer_instance
instance (a : Ev Loc) : Decidable (G.AcqR a) := by cases a <;> unfold AcqR <;> infer_instance
instance (a b : Ev Loc) : Decidable (G.sb a b) := by
  cases a <;> cases b <;> unfold sb <;> infer_instance
instance (a b : Ev Loc) : Decidable (G.mo a b) := by unfold mo; infer_instance

/-- The source of a read. -/
def rfSrcE (e : ℕ) : Ev Loc :=
  match G.rf e with
  | none => .init (G.lab e).loc
  | some a => .ev a

/-- Reads-from, as a decidable relation. -/
def rfD : Ev Loc → Ev Loc → Prop
  | w, .ev e => e < G.n ∧ (G.lab e).IsRead ∧ w = G.rfSrcE e
  | _, .init _ => False

instance (a b : Ev Loc) : Decidable (G.rfD a b) := by cases b <;> unfold rfD <;> infer_instance

theorem rfE_iff (a b : Ev Loc) : G.rfE a b ↔ G.rfD a b := by
  cases b with
  | init l => exact Iff.rfl
  | ev e => cases h : G.rf e <;> simp [rfE, rfD, rfSrcE, h]

instance (a b : Ev Loc) : Decidable (G.rfE a b) := decidable_of_iff _ (G.rfE_iff a b).symm

/-- The update events. -/
def UpdE : Ev Loc → Prop
  | .init _ => False
  | .ev e => (G.lab e).IsUpdate

instance (a : Ev Loc) : Decidable (G.UpdE a) := by cases a <;> unfold UpdE <;> infer_instance

/-- The atomic writes. -/
def AtomicE : Ev Loc → Prop
  | .init _ => False
  | .ev e => (G.lab e).AtomicW

instance (a : Ev Loc) : Decidable (G.AtomicE a) := by
  cases a <;> unfold AtomicE <;> infer_instance

/-! ## The events, as a list -/

variable (locs : List Loc)

/-- All events, given a list of all locations. -/
def univ : List (Ev Loc) := locs.map .init ++ (List.range G.n).map .ev

variable {locs} (hlocs : ∀ l, l ∈ locs)
include hlocs

theorem mem_univ {a : Ev Loc} : a ∈ G.univ locs ↔ G.Mem a := by
  cases a with
  | init l => simpa [univ, Mem] using hlocs l
  | ev e => simp [univ, Mem]

theorem Mem.of_write {a : Ev Loc} (h : G.IsWrite a) : a ∈ G.univ locs := by
  rw [G.mem_univ hlocs]; cases a
  · trivial
  · exact h.1

variable {G} (hwf : G.WF)
include hwf

theorem univ_rfE {a b : Ev Loc} (h : G.rfE a b) : a ∈ G.univ locs ∧ b ∈ G.univ locs := by
  obtain ⟨e, rfl, he, -⟩ := rfE_tgt h
  exact ⟨Mem.of_write G hlocs (rfE_src hwf h).1, (G.mem_univ hlocs).2 he⟩

omit hwf in
theorem univ_sb {a b : Ev Loc} (h : G.sb a b) : a ∈ G.univ locs ∧ b ∈ G.univ locs := by
  obtain ⟨e, rfl, he, hlt⟩ := sb_tgt h
  refine ⟨(G.mem_univ hlocs).2 ?_, (G.mem_univ hlocs).2 he⟩
  cases a with
  | init => trivial
  | ev x => exact (hlt x rfl).trans he

omit hwf in
theorem univ_mo {a b : Ev Loc} (h : G.mo a b) : a ∈ G.univ locs ∧ b ∈ G.univ locs :=
  ⟨Mem.of_write G hlocs h.1, Mem.of_write G hlocs h.2.1⟩

omit hwf hlocs in
theorem mo_trans' {a b c : Ev Loc} (h1 : G.mo a b) (h2 : G.mo b c) : G.mo a c :=
  ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

/-! ## Bounded relations -/

variable (G locs)
omit hwf hlocs

/-- `rb`, with the write bounded. -/
def rbU (a b : Ev Loc) : Prop := ∃ w ∈ G.univ locs, G.rfE w a ∧ G.mo w b

/-- The steps of `eco`. -/
def ecoStep (a b : Ev Loc) : Prop := G.rfE a b ∨ G.mo a b ∨ G.rbU locs a b

/-- The steps of the chains of release sequences. -/
def rsStep (a b : Ev Loc) : Prop := G.rfE a b ∧ G.UpdE b

instance (a b : Ev Loc) : Decidable (G.rsStep a b) := by unfold rsStep; infer_instance

/-- The `rf; [U]` chains of release sequences, as a finite set of pairs. -/
def rsSet : Finset (Ev Loc × Ev Loc) := fw (G.rsStep) (G.univ locs) (G.univ locs)

variable (R : Finset (Ev Loc × Ev Loc))

/-- `rs`, with the head bounded and the chains `R`. -/
def rsU (a b : Ev Loc) : Prop :=
  G.IsWrite a ∧ ∃ c ∈ G.univ locs, (c = a ∨ (G.sb a c ∧ G.loc a = G.loc c)) ∧ G.IsWrite c ∧
    G.AtomicE c ∧ (c = b ∨ (c, b) ∈ R)

/-- `sw`, with the write bounded. -/
def swU (a b : Ev Loc) : Prop :=
  G.RelW a ∧ ∃ w ∈ G.univ locs, G.rsU locs R a w ∧ G.rfE w b ∧ G.AcqR b

/-- The steps of `hb`. -/
def hbStep (a b : Ev Loc) : Prop := G.sb a b ∨ G.swU locs R a b

instance (a b : Ev Loc) : Decidable (G.ecoStep locs a b) := by
  unfold ecoStep rbU; infer_instance
instance (a b : Ev Loc) : Decidable (G.rsU locs R a b) := by unfold rsU; infer_instance
instance (a b : Ev Loc) : Decidable (G.hbStep locs R a b) := by
  unfold hbStep swU; infer_instance

/-- `eco` and `hb`, as finite sets of pairs. -/
def ecoSet : Finset (Ev Loc × Ev Loc) := fw (G.ecoStep locs) (G.univ locs) (G.univ locs)
def hbSet : Finset (Ev Loc × Ev Loc) :=
  fw (G.hbStep locs (G.rsSet locs)) (G.univ locs) (G.univ locs)

variable {G locs}
include hwf hlocs

theorem rb_iff {a b : Ev Loc} : G.rb a b ↔ G.rbU locs a b :=
  ⟨fun ⟨w, h1, h2⟩ => ⟨w, (univ_rfE hlocs hwf h1).1, h1, h2⟩, fun ⟨w, _, h1, h2⟩ => ⟨w, h1, h2⟩⟩

theorem eco_iff {a b : Ev Loc} : G.eco a b ↔ (a, b) ∈ G.ecoSet locs := by
  have : (fun a b => G.rfE a b ∨ G.mo a b ∨ G.rb a b) = G.ecoStep locs := by
    funext a b; simp only [ecoStep, rb_iff hlocs hwf]
  unfold eco ecoSet; rw [this]
  refine transGen_iff_fw fun a b h => ?_
  rcases h with h | h | ⟨w, -, h1, h2⟩
  · exact univ_rfE hlocs hwf h
  · exact univ_mo hlocs h
  · exact ⟨(univ_rfE hlocs hwf h1).2, (univ_mo hlocs h2).2⟩

theorem rs_iff {a b : Ev Loc} : G.rs a b ↔ G.rsU locs (G.rsSet locs) a b := by
  have hchain : ∀ c, Relation.ReflTransGen
      (fun x y => G.rfE x y ∧ ∃ e, y = .ev e ∧ (G.lab e).IsUpdate) c b ↔
      c = b ∨ (c, b) ∈ G.rsSet locs := by
    intro c
    have : (fun x y => G.rfE x y ∧ ∃ e, y = .ev e ∧ (G.lab e).IsUpdate) = G.rsStep := by
      funext x y
      simp only [rsStep]
      congr 1
      cases y <;> simp [UpdE]
    rw [this]
    exact reflTransGen_iff_fw fun x y h => univ_rfE hlocs hwf h.1
  have hat : ∀ c : Ev Loc, (match c with
      | .init _ => False
      | .ev e => (G.lab e).AtomicW) ↔ G.AtomicE c := fun c => by cases c <;> rfl
  unfold rs rsU
  constructor
  · rintro ⟨hw, c, hc, hcw, hca, hch⟩
    exact ⟨hw, c, Mem.of_write G hlocs hcw, hc, hcw, (hat c).1 hca, (hchain c).1 hch⟩
  · rintro ⟨hw, c, -, hc, hcw, hca, hch⟩
    exact ⟨hw, c, hc, hcw, (hat c).2 hca, (hchain c).2 hch⟩

theorem sw_iff {a b : Ev Loc} : G.sw a b ↔ G.swU locs (G.rsSet locs) a b := by
  unfold sw swU
  constructor
  · rintro ⟨hr, w, h1, h2, h3⟩
    exact ⟨hr, w, (univ_rfE hlocs hwf h2).1, (rs_iff hlocs hwf).1 h1, h2, h3⟩
  · rintro ⟨hr, w, -, h1, h2, h3⟩
    exact ⟨hr, w, (rs_iff hlocs hwf).2 h1, h2, h3⟩

theorem hb_iff {a b : Ev Loc} : G.hb a b ↔ (a, b) ∈ G.hbSet locs := by
  have : (fun a b => G.sb a b ∨ G.sw a b) = G.hbStep locs (G.rsSet locs) := by
    funext a b; simp only [hbStep, sw_iff hlocs hwf]
  unfold hb hbSet; rw [this]
  refine transGen_iff_fw fun a b h => ?_
  rcases h with h | ⟨ha, w, -, -, h2, hb⟩
  · exact univ_sb hlocs h
  · refine ⟨(G.mem_univ hlocs).2 ?_, (univ_rfE hlocs hwf h2).2⟩
    cases a
    · exact absurd ha id
    · exact ha.1

/-! ## Consistency and races -/

omit hwf hlocs

/-- Well-formedness, with its case split made decidable. -/
theorem wf_iff : G.WF ↔
    (∀ e < G.n, (G.lab e).IsRead →
      optCase (G.rf e) ((G.lab e).rval = some (v0 (G.lab e).loc))
        (fun w => w < e ∧ (G.lab w).IsWrite ∧ (G.lab w).loc = (G.lab e).loc ∧
          (G.lab e).rval = some (G.lab w).wval)) ∧
    (∀ e < G.n, (G.lab e).IsWrite → 2 ≤ G.ts e) ∧
    (∀ a < G.n, ∀ b < G.n, ((G.lab a).IsWrite ∧ (G.lab b).IsWrite ∧
      (G.lab a).loc = (G.lab b).loc ∧ G.ts a = G.ts b) → a = b) ∧
    (∀ e < G.n, (G.lab e).IsWrite → ∀ t < G.ts e + 1, 2 ≤ t →
      ∃ a ∈ List.range G.n, (G.lab a).IsWrite ∧ (G.lab a).loc = (G.lab e).loc ∧ G.ts a = t) := by
  have h : ∀ e, (match G.rf e with
      | none => (G.lab e).rval = some (v0 (G.lab e).loc)
      | some w => w < e ∧ (G.lab w).IsWrite ∧ (G.lab w).loc = (G.lab e).loc ∧
          (G.lab e).rval = some (G.lab w).wval) ↔
      optCase (G.rf e) ((G.lab e).rval = some (v0 (G.lab e).loc))
        (fun w => w < e ∧ (G.lab w).IsWrite ∧ (G.lab w).loc = (G.lab e).loc ∧
          (G.lab e).rval = some (G.lab w).wval) := fun e => by
    cases G.rf e <;> rfl
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun e he hr => (h e).1 (h1 e he hr), h2,
      fun a ha b hb ⟨x1, x2, x3, x4⟩ => h3 a ha b hb x1 x2 x3 x4,
      fun e he hw t ht h2t => by
        obtain ⟨a, ha, h⟩ := h4 e he hw t h2t (by omega)
        exact ⟨a, List.mem_range.2 ha, h⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun e he hr => (h e).2 (h1 e he hr), h2,
      fun a ha b hb x1 x2 x3 x4 => h3 a ha b hb ⟨x1, x2, x3, x4⟩,
      fun e he hw t h2t ht => by
        obtain ⟨a, ha, h⟩ := h4 e he hw t (by omega) h2t
        exact ⟨a, List.mem_range.1 ha, h⟩⟩

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 1000000 in
instance : Decidable G.WF := decidable_of_iff _ G.wf_iff.symm


theorem hbSet_univ {a b : Ev Loc} (h : (a, b) ∈ G.hbSet locs) :
    a ∈ G.univ locs ∧ b ∈ G.univ locs := fw_univ _ h

theorem consistent_iff (hlocs : ∀ l, l ∈ locs) (hwf : G.WF) :
    G.Consistent ↔
    (∀ a ∈ G.univ locs, (a, a) ∉ G.hbSet locs) ∧
    (∀ a ∈ G.univ locs, ∀ b ∈ G.univ locs, (a, b) ∈ G.hbSet locs → (b, a) ∉ G.ecoSet locs) ∧
    (∀ e ∈ List.range G.n, (G.lab e).IsUpdate → ∀ w ∈ G.univ locs, G.rfE w (.ev e) →
      G.mo w (.ev e) ∧ ∀ x ∈ G.univ locs, ¬ (G.mo w x ∧ G.mo x (.ev e))) := by
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨fun a _ h => h1 a ((hb_iff hlocs hwf).2 h),
      fun a _ b _ h h' => h2 a b ((hb_iff hlocs hwf).2 h) ((eco_iff hlocs hwf).2 h'),
      fun e he hu w _ hrf => ?_⟩
    obtain ⟨hmo, hx⟩ := h3 e (List.mem_range.1 he) hu w hrf
    exact ⟨hmo, fun x _ => hx x⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hwf, fun a h => ?_, fun a b h h' => ?_, fun e he hu w hrf => ?_⟩
    · have h := (hb_iff hlocs hwf).1 h
      exact h1 a (hbSet_univ h).1 h
    · have h := (hb_iff hlocs hwf).1 h
      exact h2 a (hbSet_univ h).1 b (hbSet_univ h).2 h ((eco_iff hlocs hwf).1 h')
    · obtain ⟨hmo, hx⟩ := h3 e (List.mem_range.2 he) hu w (univ_rfE hlocs hwf hrf).1 hrf
      exact ⟨hmo, fun x h => hx x (univ_mo hlocs h.1).2 h⟩

/-- Deciding RC11 consistency. -/
def decConsistent (hlocs : ∀ l, l ∈ locs) : Decidable G.Consistent :=
  if hwf : G.WF then
    -- each closure is computed once
    let R := G.rsSet locs
    let H := fw (G.hbStep locs R) (G.univ locs) (G.univ locs)
    let E := G.ecoSet locs
    have h : G.Consistent ↔
        (∀ a ∈ G.univ locs, (a, a) ∉ H) ∧
        (∀ a ∈ G.univ locs, ∀ b ∈ G.univ locs, (a, b) ∈ H → (b, a) ∉ E) ∧
        (∀ e ∈ List.range G.n, (G.lab e).IsUpdate → ∀ w ∈ G.univ locs, G.rfE w (.ev e) →
          G.mo w (.ev e) ∧ ∀ x ∈ G.univ locs, ¬ (G.mo w x ∧ G.mo x (.ev e))) :=
      consistent_iff hlocs hwf
    decidable_of_iff _ h.symm
  else isFalse fun h => hwf h.wf

instance (a b : Ev Loc) : Decidable (G.Conflict a b) := by unfold Conflict; infer_instance

theorem racy_iff (hlocs : ∀ l, l ∈ locs) (hwf : G.WF) : G.Racy ↔
    ∃ a ∈ G.univ locs, ∃ b ∈ G.univ locs, G.Conflict a b ∧ (a, b) ∉ G.hbSet locs ∧
      (b, a) ∉ G.hbSet locs ∧ (G.IsNA a ∨ G.IsNA b) := by
  simp only [Racy, Race, hb_iff hlocs hwf]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, (G.mem_univ hlocs).2 h.1.1, b, (G.mem_univ hlocs).2 h.1.2.1, h⟩
  · rintro ⟨a, -, b, -, h⟩
    exact ⟨a, b, h⟩

/-- Deciding races of a well-formed graph. -/
def decRacy (hlocs : ∀ l, l ∈ locs) (hwf : G.WF) : Decidable G.Racy :=
  let H := fw (G.hbStep locs (G.rsSet locs)) (G.univ locs) (G.univ locs)
  have h : G.Racy ↔ ∃ a ∈ G.univ locs, ∃ b ∈ G.univ locs, G.Conflict a b ∧ (a, b) ∉ H ∧
      (b, a) ∉ H ∧ (G.IsNA a ∨ G.IsNA b) := racy_iff hlocs hwf
  decidable_of_iff _ h.symm

end Exec

end ORC11.RC11
