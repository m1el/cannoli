import ORC11.RC11
import ORC11.Steps

/-!
# RC11 executions are ORC11 runs (for location-disciplined programs)

Replaying an RC11-consistent execution graph event by event, in its numbering
(which extends `sb ∪ rf`), gives an ORC11 run: either the run reaches a
configuration where some thread's next access fails ORC11's race check, or the
graph is race-free and the run ends with exactly the graph's final local
states (`replay`). Together with the ORC11 safety theorems this carries them
to all RC11-consistent executions.

This is the argument of the ORC11 appendix §2 (Lemmas 3–8, Theorem 1), done
directly on ORC11 with an upper-bound invariant instead of an exact
reconstruction of the machine state. The simulation (`Sim`) keeps:

* each thread's local state: the result of running its items so far;
* each thread's current view is bounded: every time in it is at most the rank
  of a write the thread has *seen* (it happens before one of the thread's
  events, or is read by an event that does), and every non-atomic read id in
  it is of a read that happens before one of the thread's events;
* every message is the initialization or a replayed write, with its rank, its
  value, and a view bounded by what its release sequence heads have seen;
* the race detector has recorded every replayed non-atomic access.

The programs must be **location-disciplined**: each location is accessed
only atomically (relaxed or acquire/release) or only non-atomically. Without
this the correspondence fails: the Coq ORC11 lets an acquire load of a
*relaxed* store make that store count as seen by a later non-atomic access of
the same location, which RC11 considers a race.
-/

namespace ORC11

namespace RC11

variable {Loc Val : Type} [DecidableEq Loc] [DecidableEq Val]
  {ι : Type} [DecidableEq ι] {S : ι → Type}
  {prog : (i : ι) → S i → Instr Loc Val (S i)} {s0 : (i : ι) → S i}
  {v0 : Loc → Option Val}

/-! ## Location discipline -/

/-- The orders a label may use at a location of kind `atomic`. -/
def Label.Disc (A : Loc → Prop) : Label Loc Val → Prop
  | .R l o _ | .W l o _ => (A l → o = .rlx ∨ o = .acqrel) ∧ (¬ A l → o = .na)
  | .U l or ow _ _ => A l ∧ (or = .rlx ∨ or = .acqrel) ∧ (ow = .rlx ∨ ow = .acqrel)

/-- The orders an instruction may use at a location of kind `atomic`. -/
def _root_.ORC11.Instr.Disc {T : Type} (A : Loc → Prop) : Instr Loc Val T → Prop
  | .read l o _ | .write l o _ _ => (A l → o = .rlx ∨ o = .acqrel) ∧ (¬ A l → o = .na)
  | .update l or ow _ _ => A l ∧ (or = .rlx ∨ or = .acqrel) ∧ (ow = .rlx ∨ ow = .acqrel)
  | _ => True

/-- Each location `l` is accessed only atomically (if `A l`), with relaxed or
acquire/release orders, or only non-atomically. -/
def Disciplined (prog : (i : ι) → S i → Instr Loc Val (S i)) (A : Loc → Prop) : Prop :=
  ∀ i (s : S i), (prog i s).Disc A

/-! ## Runs of items -/

section Runs

variable {T : Type} {p : T → Instr Loc Val T} {lab : ℕ → Label Loc Val}

theorem runItems_append (s : T) (xs ys : List Item) :
    runItems p lab s (xs ++ ys) = (runItems p lab s xs).bind fun s' => runItems p lab s' ys := by
  induction xs generalizing s with
  | nil => simp [runItems]
  | cons x xs ih =>
    simp only [List.cons_append, runItems]
    cases stepItem p lab s x with
    | none => rfl
    | some s' => exact ih s'

theorem runItems_cons_of {s s' : T} {x : Item} {xs : List Item}
    (h : runItems p lab s (x :: xs) = some s') :
    ∃ s1, stepItem p lab s x = some s1 ∧ runItems p lab s1 xs = some s' := by
  simp only [runItems] at h
  cases h1 : stepItem p lab s x with
  | none => rw [h1] at h; cases h
  | some s1 => rw [h1] at h; exact ⟨s1, rfl, h⟩

theorem runItems_snoc {s s1 s2 : T} {xs : List Item} {x : Item}
    (h1 : runItems p lab s xs = some s1) (h2 : stepItem p lab s1 x = some s2) :
    runItems p lab s (xs ++ [x]) = some s2 := by
  rw [runItems_append, h1]; simp [runItems, h2]

/-- A label that some state of the program accepts respects the discipline. -/
theorem stepItem_disc {A : Loc → Prop} (hd : ∀ s, (p s).Disc A)
    {s s' : T} {e : ℕ} (h : stepItem p lab s (.inl e) = some s') : (lab e).Disc A := by
  have hds := hd s
  simp only [stepItem] at h
  cases hp : p s with
  | read l o k =>
    rw [hp] at hds h; simp only [Instr.Disc] at hds
    cases hl : lab e with
    | R l' o' v =>
      rw [hl] at h; simp only at h
      split_ifs at h with hh
      obtain ⟨rfl, rfl⟩ := hh; simpa [Label.Disc] using hds
    | W => rw [hl] at h; cases h
    | U => rw [hl] at h; cases h
  | write l o v k =>
    rw [hp] at hds h; simp only [Instr.Disc] at hds
    cases hl : lab e with
    | W l' o' v' =>
      rw [hl] at h; simp only at h
      split_ifs at h with hh
      obtain ⟨rfl, rfl, -⟩ := hh; simpa [Label.Disc] using hds
    | R => rw [hl] at h; cases h
    | U => rw [hl] at h; cases h
  | update l or ow f k =>
    rw [hp] at hds h; simp only [Instr.Disc] at hds
    cases hl : lab e with
    | U l' or' ow' vr vw =>
      rw [hl] at h; simp only at h
      split_ifs at h with hh
      obtain ⟨rfl, rfl, rfl, -⟩ := hh; simpa [Label.Disc] using hds
    | R => rw [hl] at h; cases h
    | W => rw [hl] at h; cases h
  | choose k => rw [hp] at h; cases lab e <;> cases h
  | halt => rw [hp] at h; cases lab e <;> cases h
  | fault => rw [hp] at h; cases lab e <;> cases h

theorem runItems_disc {A : Loc → Prop} (hd : ∀ s, (p s).Disc A) :
    ∀ {s s' : T} {xs : List Item}, runItems p lab s xs = some s' → ∀ e, Sum.inl e ∈ xs →
      (lab e).Disc A
  | s, s', [], _, e, he => by cases he
  | s, s', x :: xs, h, e, he => by
    obtain ⟨s1, h1, h2⟩ := runItems_cons_of h
    rcases List.mem_cons.1 he with rfl | he
    · exact stepItem_disc hd h1
    · exact runItems_disc hd h2 e he

/-- Splitting a list of items at its first event. -/
theorem split_first_event : ∀ {xs : List Item} {e : ℕ} {ys : List ℕ},
    xs.filterMap Sum.getLeft? = e :: ys →
    ∃ cs rest, xs = cs ++ Sum.inl e :: rest ∧ (∀ x ∈ cs, ∃ b, x = Sum.inr b) ∧
      rest.filterMap Sum.getLeft? = ys
  | [], _, _, h => by simp at h
  | .inl a :: xs, e, ys, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨[], xs, rfl, by simp, h⟩
  | .inr b :: xs, e, ys, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr] at h
    obtain ⟨cs, rest, rfl, hcs, hrest⟩ := split_first_event h
    exact ⟨.inr b :: cs, rest, rfl, by
      intro x hx; rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, rfl⟩
      · exact hcs x hx, hrest⟩

theorem all_choices_of_filterMap_nil : ∀ {xs : List Item}, xs.filterMap Sum.getLeft? = [] →
    ∀ x ∈ xs, ∃ b, x = Sum.inr b
  | [], _, x, hx => by cases hx
  | .inl a :: xs, h, _, _ => by simp at h
  | .inr b :: xs, h, x, hx => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, rfl⟩
    · exact all_choices_of_filterMap_nil h x hx

end Runs

variable (G : Exec prog s0 v0)

namespace Exec

/-! ## What threads and messages have seen -/

/-- Thread `π`, having replayed the events below `k`, has seen write `w`. -/
def Seen (π : ι) (k : ℕ) (w : Ev Loc) : Prop :=
  G.IsWrite w ∧ ((∃ l, w = .init l) ∨ ∃ e < k, G.tid e = π ∧
    (G.hbS w (.ev e) ∨ ∃ r, G.rfE w r ∧ G.hbS r (.ev e)))

/-- Non-atomic reads that happen before one of `π`'s events below `k`. -/
def SeenNR (π : ι) (k : ℕ) (r : ℕ) : Prop :=
  r < G.n ∧ (G.lab r).IsRead ∧ (G.lab r).IsNA ∧
    ∃ e < k, G.tid e = π ∧ G.hbS (.ev r) (.ev e)

/-- `h` is a release write heading a release sequence containing `e`. -/
def RelHead (h e : ℕ) : Prop := G.RelW (.ev h) ∧ G.rs (.ev h) (.ev e)

/-- What the message of write `e` may carry: its own time, and what release
sequence heads of `e` have seen. -/
def MsgSeen (e : ℕ) (x : Ev Loc) : Prop :=
  G.IsWrite x ∧ ((∃ l, x = .init l) ∨ x = .ev e ∨ ∃ h, G.RelHead h e ∧
    (G.hbS x (.ev h) ∨ ∃ r, G.rfE x r ∧ G.hbS r (.ev h)))

def MsgNR (e r : ℕ) : Prop :=
  r < G.n ∧ (G.lab r).IsRead ∧ (G.lab r).IsNA ∧ ∃ h, G.RelHead h e ∧ G.hbS (.ev r) (.ev h)

/-- View `V` is bounded by writes satisfying `P` (for times) and reads
satisfying `Q` (for non-atomic read ids). -/
def Bounded (V : View Loc) (P : Ev Loc → Prop) (Q : ℕ → Prop) : Prop :=
  (∀ l, ∃ x, P x ∧ G.loc x = l ∧ (V l).w ≤ G.tsE x) ∧ (∀ l r, r ∈ (V l).nr → Q r)

variable {G}

theorem Bounded.sup {V W : View Loc} {P : Ev Loc → Prop} {Q : ℕ → Prop}
    (hV : G.Bounded V P Q) (hW : G.Bounded W P Q) : G.Bounded (V ⊔ W) P Q := by
  refine ⟨fun l => ?_, fun l r hr => ?_⟩
  · obtain ⟨x, hx, hxl, hxt⟩ := hV.1 l
    obtain ⟨y, hy, hyl, hyt⟩ := hW.1 l
    simp only [View.sup_apply', TimeInfo.sup_w]
    rcases le_total (G.tsE x) (G.tsE y) with h | h
    · exact ⟨y, hy, hyl, max_le (hxt.trans h) hyt⟩
    · exact ⟨x, hx, hxl, max_le hxt (hyt.trans h)⟩
  · simp only [View.sup_apply', TimeInfo.sup_nr, Finset.mem_union] at hr
    rcases hr with hr | hr
    · exact hV.2 l r hr
    · exact hW.2 l r hr

theorem Bounded.mono {V : View Loc} {P P' : Ev Loc → Prop} {Q Q' : ℕ → Prop}
    (h : G.Bounded V P Q) (hP : ∀ x, P x → P' x) (hQ : ∀ r, Q r → Q' r) :
    G.Bounded V P' Q' :=
  ⟨fun l => let ⟨x, hx, hxl, hxt⟩ := h.1 l; ⟨x, hP x hx, hxl, hxt⟩,
    fun l r hr => hQ r (h.2 l r hr)⟩

theorem Bounded.bot {P : Ev Loc → Prop} {Q : ℕ → Prop} (hP : ∀ l, P (.init l)) :
    G.Bounded (⊥ : View Loc) P Q :=
  ⟨fun l => ⟨.init l, hP l, rfl, by simp⟩, fun l r hr => by simp at hr⟩

/-- A single entry at `l` with time `t` and no read ids. -/
theorem Bounded.single {l : Loc} {x0 : TimeInfo} {P : Ev Loc → Prop} {Q : ℕ → Prop}
    (hP : ∀ l, P (.init l)) {y : Ev Loc} (hy : P y) (hyl : G.loc y = l)
    (hyt : x0.w ≤ G.tsE y) (hnr : ∀ r ∈ x0.nr, Q r) :
    G.Bounded (View.single l x0) P Q := by
  refine ⟨fun l' => ?_, fun l' r hr => ?_⟩
  · by_cases h : l' = l
    · subst h; exact ⟨y, hy, hyl, by simpa using hyt⟩
    · exact ⟨.init l', hP l', rfl, by simp [h]⟩
  · by_cases h : l' = l
    · subst h; exact hnr r (by simpa using hr)
    · simp [h] at hr

end Exec

variable {G}

theorem Exec.seen_init (π : ι) (k : ℕ) (l : Loc) : G.Seen π k (.init l) :=
  ⟨trivial, Or.inl ⟨l, rfl⟩⟩

theorem Exec.msgSeen_init (e : ℕ) (l : Loc) : G.MsgSeen e (.init l) :=
  ⟨trivial, Or.inl ⟨l, rfl⟩⟩

theorem Exec.seen_mono {π : ι} {k k' : ℕ} (hk : k ≤ k') {w : Ev Loc} (h : G.Seen π k w) :
    G.Seen π k' w := by
  obtain ⟨hw, h | ⟨e, he, ht, h⟩⟩ := h
  · exact ⟨hw, Or.inl h⟩
  · exact ⟨hw, Or.inr ⟨e, by omega, ht, h⟩⟩

theorem Exec.seenNR_mono {π : ι} {k k' : ℕ} (hk : k ≤ k') {r : ℕ} (h : G.SeenNR π k r) :
    G.SeenNR π k' r :=
  let ⟨h1, h2, h3, e, he, ht, h⟩ := h; ⟨h1, h2, h3, e, by omega, ht, h⟩

/-! ## The simulation -/

/-- The initialization message of `l`. -/
def initMsg (v0 : Loc → Option Val) (l : Loc) : Msg Loc Val := ⟨1, v0 l, none⟩

/-- Events numbered below `k`, and initializations. -/
def InPre (k : ℕ) : Ev Loc → Prop
  | .init _ => True
  | .ev e => e < k

/-- No race among the events below `k`. -/
def Exec.RaceFree (k : ℕ) : Prop := ∀ a b, G.Race a b → InPre k a → InPre k b → False

variable (G)

/-- The ORC11 configuration `c` corresponds to the events below `k`, thread
`π` having run the items `pre π`. -/
structure Sim (k : ℕ) (pre : (i : ι) → List Item) (c : Config ι S Loc Val) : Prop where
  prefix_ : ∀ π, pre π <+: G.items π
  state : ∀ π, runItems (prog π) G.lab (s0 π) (pre π) = some (c.th π).1
  evs : ∀ π, (pre π).filterMap Sum.getLeft? = (List.range k).filter (fun e => G.tid e = π)
  cur : ∀ π, G.Bounded (c.th π).2.cur (G.Seen π k) (G.SeenNR π k)
  rel : ∀ π, (c.th π).2.rel = ⊥
  memOld : ∀ l, ∀ m ∈ c.mem l, m = initMsg v0 l ∨ ∃ e < k, (G.lab e).IsWrite ∧
    (G.lab e).loc = l ∧ m.time = G.ts e ∧ m.val = (G.lab e).wval ∧
    G.Bounded (m.view.getD ⊥) (G.MsgSeen e) (G.MsgNR e)
  memInit : ∀ l, initMsg v0 l ∈ c.mem l
  memNew : ∀ e < k, (G.lab e).IsWrite → ∃ m ∈ c.mem (G.lab e).loc, m.time = G.ts e
  naW : ∀ e < k, (G.lab e).IsWrite → (G.lab e).IsNA → G.ts e ≤ (c.na (G.lab e).loc).w
  naR : ∀ e < k, (G.lab e).IsRead → (G.lab e).IsNA → e ∈ (c.na (G.lab e).loc).nr
  ids : ∀ l r, r ∈ (c.na l).nr ∨ r ∈ (c.na l).ar → r < k

variable {G}

theorem Sim.mem_pre {k : ℕ} {pre : (i : ι) → List Item} {c : Config ι S Loc Val}
    (h : Sim G k pre c) {π : ι} {e : ℕ} : Sum.inl e ∈ pre π ↔ e < k ∧ G.tid e = π := by
  have := h.evs π
  constructor
  · intro he
    have : e ∈ (pre π).filterMap Sum.getLeft? := List.mem_filterMap.2 ⟨_, he, rfl⟩
    rw [h.evs π] at this; simpa using this
  · intro he
    have : e ∈ (List.range k).filter (fun e => G.tid e = π) := by simpa using he
    rw [← h.evs π] at this
    obtain ⟨x, hx, hxe⟩ := List.mem_filterMap.1 this
    cases x with
    | inl a => simp at hxe; subst hxe; exact hx
    | inr b => simp at hxe

theorem initTView_cur_bounded (π : ι) :
    G.Bounded (initTView (Loc := Loc)).cur (G.Seen π 0) (G.SeenNR π 0) :=
  ⟨fun l => ⟨.init l, G.seen_init π 0 l, rfl, by simp [initTView, initTime, Exec.tsE]⟩,
    fun l r hr => by simp [initTView, initTime] at hr⟩

/-- The initial configuration corresponds to no events. -/
theorem sim_init : Sim G 0 (fun _ => []) (initConfig s0 v0) where
  prefix_ π := List.nil_prefix
  state π := rfl
  evs π := by simp
  cur π := initTView_cur_bounded π
  rel π := rfl
  memOld l m hm := by
    simp only [initConfig, List.mem_singleton] at hm; exact Or.inl hm
  memInit l := by simp [initConfig, initMsg]
  memNew e he := absurd he (Nat.not_lt_zero _)
  naW e he := absurd he (Nat.not_lt_zero _)
  naR e he := absurd he (Nat.not_lt_zero _)
  ids l r hr := by simp [initConfig, initTime] at hr

theorem raceFree_zero : G.RaceFree 0 := by
  intro a b hr ha hb
  obtain ⟨⟨-, -, hne, hloc, -⟩, -⟩ := hr
  cases a with
  | ev e => exact absurd ha (Nat.not_lt_zero _)
  | init l =>
    cases b with
    | ev e => exact absurd hb (Nat.not_lt_zero _)
    | init l' => exact hne (by simp [Exec.loc] at hloc; rw [hloc])

/-! ## Discipline of the graph's labels -/

variable (G) in
/-- The labels of the graph respect the discipline. -/
def Exec.LabDisc (A : Loc → Prop) : Prop := ∀ e < G.n, (G.lab e).Disc A

theorem Exec.labDisc {A : Loc → Prop} (hd : Disciplined prog A) : G.LabDisc A := fun e he => by
  have hmem : e ∈ (G.items (G.tid e)).filterMap Sum.getLeft? := by
    rw [G.itemsEv]; simp [he]
  obtain ⟨x, hx, hxe⟩ := List.mem_filterMap.1 hmem
  cases x with
  | inr b => simp at hxe
  | inl a =>
    have hae : a = e := by simpa using hxe
    rw [hae] at hx
    exact runItems_disc (hd (G.tid e)) (G.run (G.tid e)) e hx

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.disc_na {A : Loc → Prop} {lab : Label Loc Val} (h : lab.Disc A)
    (hA : ¬ A lab.loc) : lab.IsNA ∧ ¬ lab.IsUpdate := by
  cases lab <;> simp_all [Label.Disc, Label.IsNA, Label.IsUpdate, Label.loc]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.disc_atomic {A : Loc → Prop} {lab : Label Loc Val} (h : lab.Disc A)
    (hA : A lab.loc) : ¬ lab.IsNA := by
  cases lab with
  | R l o v =>
    simp only [Label.Disc, Label.loc] at h hA
    rcases h.1 hA with h | h <;> simp [Label.IsNA, h]
  | W l o v =>
    simp only [Label.Disc, Label.loc] at h hA
    rcases h.1 hA with h | h <;> simp [Label.IsNA, h]
  | U => simp [Label.IsNA]

/-! ## Detecting races -/

section Races

variable {A : Loc → Prop}

theorem Exec.race_symm {a b : Ev Loc} (h : G.Race a b) : G.Race b a := by
  obtain ⟨⟨ha, hb, hne, hloc, hw⟩, h1, h2, hna⟩ := h
  exact ⟨⟨hb, ha, Ne.symm hne, hloc.symm, hw.symm⟩, h2, h1, hna.symm⟩

/-- In a race-free prefix, conflicting accesses with a non-atomic one are
ordered by `hb`. -/
theorem Exec.hb_related {k : ℕ} (hrf : G.RaceFree k) {x y : ℕ} (hx : x < k) (hy : y < k)
    (hkn : k ≤ G.n) (hne : x ≠ y) (hloc : (G.lab x).loc = (G.lab y).loc)
    (hw : (G.lab x).IsWrite ∨ (G.lab y).IsWrite) (hna : (G.lab x).IsNA ∨ (G.lab y).IsNA) :
    G.hb (.ev x) (.ev y) ∨ G.hb (.ev y) (.ev x) := by
  by_contra h
  push Not at h
  refine hrf (.ev x) (.ev y) ⟨⟨by show x < G.n; omega, by show y < G.n; omega,
    by simpa using hne, hloc, ?_⟩, h.1, h.2, hna⟩ hx hy
  rcases hw with hw | hw
  · exact Or.inl ⟨by omega, hw⟩
  · exact Or.inr ⟨by omega, hw⟩

/-- Events at a non-atomic location are non-atomic reads or writes. -/
theorem Exec.na_at (hA : G.LabDisc A) {e : ℕ} (he : e < G.n) {l : Loc}
    (hl : (G.lab e).loc = l) (hnA : ¬ A l) : (G.lab e).IsNA ∧ ¬ (G.lab e).IsUpdate :=
  Label.disc_na (hA e he) (hl ▸ hnA)

variable (hc : G.Consistent) (hA : G.LabDisc A)
include hc hA

/-- A thread cannot have seen a non-atomic write that does not happen before
its next event, if the events so far are race-free. -/
theorem Exec.hidden_write {k : ℕ} (hrf : G.RaceFree k) (hk : k < G.n) {x : ℕ} (hx : x < k)
    (hxw : (G.lab x).IsWrite) {l : Loc} (hxl : (G.lab x).loc = l) (hnA : ¬ A l)
    (hnhb : ¬ G.hb (.ev x) (.ev k)) {w' : Ev Loc} (hseen : G.Seen (G.tid k) k w')
    (hwl : G.loc w' = l) (hle : G.ts x ≤ G.tsE w') : False := by
  have hwf := hc.wf
  have hxn : x < G.n := by omega
  have hts2 := hwf.tsW x hxn hxw
  obtain ⟨hw', hsn⟩ := hseen
  rcases hsn with ⟨l0, rfl⟩ | ⟨e, he, hte, hsee⟩
  · simp [Exec.tsE] at hle; omega
  have hek : G.hb (.ev e) (.ev k) := hb_of_tid he hk hte
  -- a read `y` of location `l` below `k`, that `x` is not `hb`-before, is a race
  have read_ok : ∀ y, G.rfE (.ev x) (.ev y) ∨ True → (G.lab y).IsRead →
      (G.lab y).loc = l → y < k → x < y → G.hbS (.ev y) (.ev e) → False := by
    intro y _ hyr hyl hyk hxy hye
    have hyn := (Exec.na_at hA (by omega) hyl hnA).1
    rcases G.hb_related hrf hx hyk (by omega) (by omega)
      (by rw [hxl, hyl]) (Or.inl hxw) (Or.inr hyn) with h | h
    · exact hnhb (hb_trans (hb_hbS h hye) hek)
    · exact absurd (hb_lt hwf h) (by omega)
  cases w' with
  | init l0 => simp [Exec.tsE] at hle; omega
  | ev a =>
    have hawr : (G.lab a).IsWrite := hw'.2
    have hal : (G.lab a).loc = l := hwl
    by_cases hax : a = x
    · subst hax
      rcases hsee with h | ⟨r, hr, h⟩
      · exact hnhb (hbS_hb h hek)
      · obtain ⟨y, rfl, hyn, hyr⟩ := rfE_tgt hr
        have hxy := (rfE_src hwf hr).2.2 a rfl
        have hyl : (G.lab y).loc = l := by rw [← (rfE_src hwf hr).2.1]; exact hal
        exact read_ok y (Or.inr trivial) hyr hyl (by have := hbS_lt hwf h; omega) hxy h
    · -- `a` is a later write of `l` in `mo`, hence `hb`-after `x`
      have hlt : G.ts x < G.ts a := by
        rcases Nat.lt_or_ge (G.ts x) (G.ts a) with h | h
        · exact h
        · exact absurd (hwf.tsInj x hxn a hw'.1 hxw hawr (by rw [hxl, hal])
            (le_antisymm (by simpa [Exec.tsE] using hle) h)) (Ne.symm hax)
      have hak : a < k := by
        rcases hsee with h | ⟨r, hr, h⟩
        · have := hbS_lt hwf h; omega
        · obtain ⟨y, rfl, -, -⟩ := rfE_tgt hr
          have := (rfE_src hwf hr).2.2 a rfl
          have := hbS_lt hwf h; omega
      have hana := (Exec.na_at hA hw'.1 hal hnA).1
      have hxa : G.hb (.ev x) (.ev a) := by
        rcases G.hb_related hrf hx hak (by omega) (Ne.symm hax) (by rw [hxl, hal])
          (Or.inl hxw) (Or.inl (Exec.na_at hA hxn hxl hnA).1) with h | h
        · exact h
        · exact absurd ⟨⟨hxn, hxw⟩, hw', by show (G.lab x).loc = (G.lab a).loc; rw [hxl, hal],
            hlt⟩ (coh_hb_mo hc h)
      rcases hsee with h | ⟨r, hr, h⟩
      · exact hnhb (hb_trans hxa (hbS_hb h hek))
      · obtain ⟨y, rfl, hyn, hyr⟩ := rfE_tgt hr
        have hay := (rfE_src hwf hr).2.2 a rfl
        have hyl : (G.lab y).loc = l := by rw [← (rfE_src hwf hr).2.1]; exact hal
        have := hb_lt hwf hxa
        exact read_ok y (Or.inr trivial) hyr hyl (by have := hbS_lt hwf h; omega)
          (by omega) h

/-- ORC11's race check for an event with this label. -/
def LabDrf (lab : Label Loc Val) (𝓝 : View Loc) (𝓥 : TView Loc) (M : Memory Loc Val) : Prop :=
  match lab with
  | .R l o _ => DrfPreRead l 𝓝 𝓥 M o
  | .W l o _ => DrfPreWrite l 𝓝 𝓥 M o
  | .U l or ow _ _ => DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow

/-- If event `k` passes ORC11's race check, adding it creates no race. -/
theorem Exec.raceFree_succ {k : ℕ} {pre : (i : ι) → List Item} {c : Config ι S Loc Val}
    (hrf : G.RaceFree k) (hk : k < G.n) (hs : Sim G k pre c)
    (hok : LabDrf (G.lab k) c.na (c.th (G.tid k)).2 c.mem) : G.RaceFree (k + 1) := by
  have hwf := hc.wf
  have last : ∀ x, InPre k x → G.Race x (.ev k) → False := by
    intro x hx hr
    obtain ⟨⟨-, -, hne, hloc, hw⟩, hnhb1, -, hna⟩ := hr
    cases x with
    | init l => exact hnhb1 (hb_init hk)
    | ev a =>
      have hak : a < k := hx
      have han : a < G.n := by omega
      have hloc' : (G.lab a).loc = (G.lab k).loc := hloc
      by_cases hAl : A (G.lab k).loc
      · rcases hna with h | h
        · exact Label.disc_atomic (hA a han) (hloc' ▸ hAl) h
        · exact Label.disc_atomic (hA k hk) hAl h
      · obtain ⟨hkna, hku⟩ := Exec.na_at hA hk rfl hAl
        obtain ⟨hana, hau⟩ := Exec.na_at hA han hloc' hAl
        -- a write of `a` that `k`'s thread must not have seen
        have hidden : (G.lab a).IsWrite → G.ts a ≤ ((c.th (G.tid k)).2.cur (G.lab k).loc).w →
            False := by
          intro haw hle
          obtain ⟨w', hw', hwl, hwt⟩ := (hs.cur (G.tid k)).1 (G.lab k).loc
          exact Exec.hidden_write hc hA hrf hk hak haw hloc' hAl hnhb1 hw' hwl (hle.trans hwt)
        have hmsg : (G.lab a).IsWrite → ∃ m ∈ c.mem (G.lab k).loc, m.time = G.ts a := by
          intro haw; rw [← hloc']; exact hs.memNew a hak haw
        unfold LabDrf at hok
        cases hlk : G.lab k with
        | U => rw [hlk] at hku; exact hku trivial
        | R l o v =>
          rw [hlk] at hok hkna
          simp only [Label.IsNA] at hkna; subst hkna
          have haw : (G.lab a).IsWrite := by
            rcases hw with h | h
            · exact h.2
            · have := h.2; rw [hlk] at this; exact absurd this id
          obtain ⟨m, hm, hmt⟩ := hmsg haw
          have hl : (G.lab k).loc = l := by rw [hlk]; rfl
          rw [hl] at hm hidden
          exact hidden haw (hmt ▸ (hok.allW (by decide)).1 m hm)
        | W l o v =>
          rw [hlk] at hok hkna
          simp only [Label.IsNA] at hkna; subst hkna
          have hl : (G.lab k).loc = l := by rw [hlk]; rfl
          by_cases haw : (G.lab a).IsWrite
          · obtain ⟨m, hm, hmt⟩ := hmsg haw
            rw [hl] at hm hidden
            exact hidden haw (hmt ▸ (hok.writeNA (by decide)).1 m hm)
          · -- `a` is a non-atomic read, which the race detector recorded
            have har : (G.lab a).IsRead := by
              revert haw hau; cases G.lab a <;> simp [Label.IsWrite, Label.IsRead, Label.IsUpdate]
            have hin := hs.naR a hak har hana
            rw [hloc', hl] at hin
            obtain ⟨-, -, -, e, he, hte, hae⟩ := (hs.cur (G.tid k)).2 l a (hok.readNA hin)
            exact hnhb1 (hbS_hb hae (hb_of_tid he hk hte))
  intro a b hr ha hb
  by_cases ha' : InPre k a <;> by_cases hb' : InPre k b
  · exact hrf a b hr ha' hb'
  · have : b = .ev k := by
      cases b with
      | init l => exact absurd trivial hb'
      | ev e => have : e < k + 1 := hb; have : ¬ e < k := hb'; congr 1; omega
    subst this; exact last a ha' hr
  · have : a = .ev k := by
      cases a with
      | init l => exact absurd trivial ha'
      | ev e => have : e < k + 1 := ha; have : ¬ e < k := ha'; congr 1; omega
    subst this; exact last b hb' (G.race_symm hr)
  · have h1 : a = .ev k := by
      cases a with
      | init l => exact absurd trivial ha'
      | ev e => have : e < k + 1 := ha; have : ¬ e < k := ha'; congr 1; omega
    have h2 : b = .ev k := by
      cases b with
      | init l => exact absurd trivial hb'
      | ev e => have : e < k + 1 := hb; have : ¬ e < k := hb'; congr 1; omega
    exact hr.1.2.2.1 (h1.trans h2.symm)

end Races

end RC11

end ORC11
