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

theorem stepItem_read_inv {s s' : T} {e : ℕ} {l : Loc} {o : MemOrder} {v : Option Val}
    (h : stepItem p lab s (.inl e) = some s') (hl : lab e = .R l o v) :
    ∃ k, p s = .read l o k ∧ s' = k v := by
  simp only [stepItem, hl] at h
  cases hp : p s <;> rw [hp] at h <;> simp only at h
  · split_ifs at h with hh
    obtain ⟨rfl, rfl⟩ := hh; cases h; exact ⟨_, rfl, rfl⟩
  all_goals cases h

theorem stepItem_write_inv {s s' : T} {e : ℕ} {l : Loc} {o : MemOrder} {v : Val}
    (h : stepItem p lab s (.inl e) = some s') (hl : lab e = .W l o v) :
    p s = .write l o v s' := by
  simp only [stepItem, hl] at h
  cases hp : p s <;> rw [hp] at h <;> simp only at h
  case write =>
    split_ifs at h with hh
    obtain ⟨rfl, rfl, rfl⟩ := hh; cases h; rfl
  all_goals cases h

theorem stepItem_update_inv {s s' : T} {e : ℕ} {l : Loc} {or ow : MemOrder} {vr vw : Val}
    (h : stepItem p lab s (.inl e) = some s') (hl : lab e = .U l or ow vr vw) :
    ∃ f k, p s = .update l or ow f k ∧ vw = f vr ∧ s' = k vr := by
  simp only [stepItem, hl] at h
  cases hp : p s <;> rw [hp] at h <;> simp only at h
  case update =>
    split_ifs at h with hh
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hh; cases h; exact ⟨_, _, rfl, rfl, rfl⟩
  all_goals cases h

theorem stepItem_choose_inv {s s' : T} {b : Bool}
    (h : stepItem p lab s (.inr b) = some s') : ∃ k, p s = .choose k ∧ s' = k b := by
  simp only [stepItem] at h
  cases hp : p s <;> rw [hp] at h <;> simp only at h
  case choose => cases h; exact ⟨_, rfl, rfl⟩
  all_goals cases h

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

/-! ## Replaying one event: helpers -/

section Helpers

variable (G) in
/-- The source of read `k`. -/
def Exec.src (k : ℕ) : Ev Loc :=
  match G.rf k with
  | none => .init (G.lab k).loc
  | some w => .ev w

theorem Exec.rfE_src_self {k : ℕ} (hk : k < G.n) (hr : (G.lab k).IsRead) :
    G.rfE (G.src k) (.ev k) := by
  refine ⟨hk, hr, ?_⟩
  unfold Exec.src; cases G.rf k <;> rfl

theorem Exec.hb_of_seen_pred {k : ℕ} (hk : k < G.n) {e : ℕ} (he : e < k)
    (hte : G.tid e = G.tid k) {x : Ev Loc} (h : G.hbS x (.ev e)) : G.hb x (.ev k) :=
  hbS_hb h (hb_of_tid he hk hte)

/-- What `k`'s thread has seen, it has seen strictly before `k`. -/
theorem Exec.seen_before {k : ℕ} (hk : k < G.n) {w : Ev Loc} (hw : G.Seen (G.tid k) k w)
    (hni : ∀ l, w ≠ .init l) : G.hb w (.ev k) ∨ ∃ r, G.rfE w r ∧ G.hb r (.ev k) := by
  obtain ⟨-, ⟨l, rfl⟩ | ⟨e, he, hte, h | ⟨r, hr, h⟩⟩⟩ := hw
  · exact absurd rfl (hni l)
  · exact Or.inl (G.hb_of_seen_pred hk he hte h)
  · exact Or.inr ⟨r, hr, G.hb_of_seen_pred hk he hte h⟩

theorem Exec.seen_lt {k : ℕ} (hwf : G.WF) {a : ℕ} (hw : G.Seen (G.tid k) k (.ev a)) :
    a < k := by
  obtain ⟨-, ⟨l, h⟩ | ⟨e, he, -, h | ⟨r, hr, h⟩⟩⟩ := hw
  · cases h
  · have := hbS_lt hwf h; omega
  · obtain ⟨y, rfl, -, -⟩ := rfE_tgt hr
    have := (rfE_src hwf hr).2.2 a rfl
    have := hbS_lt hwf h; omega

variable (hc : G.Consistent)
include hc

/-- A read reads a write at least as late as anything its thread has seen at
that location. -/
theorem Exec.seen_le_src {k : ℕ} (hk : k < G.n) (hr : (G.lab k).IsRead) {w : Ev Loc}
    (hw : G.Seen (G.tid k) k w) (hwl : G.loc w = (G.lab k).loc) :
    G.tsE w ≤ G.tsE (G.src k) := by
  have hwf := hc.wf
  have hrf := G.rfE_src_self hk hr
  by_cases hi : ∃ l, w = .init l
  · obtain ⟨l, rfl⟩ := hi
    unfold Exec.src; cases hs : G.rf k with
    | none => simp [Exec.tsE]
    | some a =>
      have := (hwf.rfSrc k hk hr); rw [hs] at this
      have := hwf.tsW a (by omega) this.2.1
      simp [Exec.tsE]; omega
  · push Not at hi
    have := coh_read hc hrf (G.seen_before hk hw hi)
    by_contra hlt
    exact this ⟨(rfE_src hwf hrf).1, hw.1,
      by rw [hwl, (rfE_src hwf hrf).2.1], by omega⟩

/-- A write goes after everything its thread has seen at that location. -/
theorem Exec.seen_lt_write {k : ℕ} (hk : k < G.n) (hkw : (G.lab k).IsWrite) {w : Ev Loc}
    (hw : G.Seen (G.tid k) k w) (hwl : G.loc w = (G.lab k).loc) :
    G.tsE w < G.ts k := by
  have hwf := hc.wf
  have h2 := hwf.tsW k hk hkw
  cases w with
  | init l => simp [Exec.tsE]; omega
  | ev a =>
    have hak := G.seen_lt hwf hw
    have := coh_write hc (G.seen_before hk hw (fun l h => by cases h))
    rcases Nat.lt_or_ge (G.ts a) (G.ts k) with h | h
    · exact h
    · exfalso
      rcases Nat.lt_or_eq_of_le h with h | h
      · exact this ⟨⟨hk, hkw⟩, hw.1, by rw [hwl]; rfl, h⟩
      · exact absurd (hwf.tsInj a hw.1.1 k hk hw.1.2 hkw hwl h.symm) (by omega)

/-- The message a read `k` reads, in a simulated configuration. -/
theorem Exec.msg_of_src {k : ℕ} {pre : (i : ι) → List Item} {c : Config ι S Loc Val}
    (hs : Sim G k pre c) (hk : k < G.n) (hr : (G.lab k).IsRead) :
    ∃ m ∈ c.mem (G.lab k).loc, m.time = G.tsE (G.src k) ∧
      (G.lab k).rval = some m.val ∧
      (G.src k = .init (G.lab k).loc → m.view = none) ∧
      (∀ w, G.src k = .ev w → G.Bounded (m.view.getD ⊥) (G.MsgSeen w) (G.MsgNR w)) := by
  have hwf := hc.wf
  have hsrc := hwf.rfSrc k hk hr
  unfold Exec.src
  cases hrf : G.rf k with
  | none =>
    rw [hrf] at hsrc
    exact ⟨initMsg v0 _, hs.memInit _, rfl, hsrc, (fun _ => rfl), (fun w h => by cases h)⟩
  | some w =>
    rw [hrf] at hsrc
    obtain ⟨hwk, hww, hwl, hval⟩ := hsrc
    obtain ⟨m, hm, hmt⟩ := hs.memNew w hwk hww
    rw [hwl] at hm
    rcases hs.memOld _ m hm with hinit | ⟨e', he', he'w, he'l, hmt', hmv, hmb⟩
    · subst hinit
      have := hwf.tsW w (by omega) hww
      simp [initMsg] at hmt; omega
    · have : e' = w := hwf.tsInj e' (by omega) w (by omega) he'w hww (by rw [he'l, hwl])
        (by rw [← hmt', hmt])
      subst this
      exact ⟨m, hm, hmt, by rw [hval, hmv], (fun h => by cases h),
        (fun w' h => by cases h; exact hmb)⟩

/-- What an acquire read of `k`'s source gives: things `k`'s thread has now
seen. -/
theorem Exec.acq_bounded {k : ℕ} (hk : k < G.n) (hr : (G.lab k).IsRead)
    (hacq : (G.lab k).AcqR) {m : Msg Loc Val}
    (hinit : G.src k = .init (G.lab k).loc → m.view = none)
    (hb : ∀ w, G.src k = .ev w → G.Bounded (m.view.getD ⊥) (G.MsgSeen w) (G.MsgNR w)) :
    G.Bounded (m.view.getD ⊥) (G.Seen (G.tid k) (k + 1)) (G.SeenNR (G.tid k) (k + 1)) := by
  have hwf := hc.wf
  have hrf := G.rfE_src_self hk hr
  cases hsrc : G.src k with
  | init l =>
    have hl : l = (G.lab k).loc := by unfold Exec.src at hsrc; split at hsrc <;> cases hsrc; rfl
    subst hl
    rw [hinit hsrc]; exact Bounded.bot (fun l => G.seen_init _ _ l)
  | ev w =>
    rw [hsrc] at hrf
    -- a release sequence head of `w` synchronizes with `k`
    have hsw : ∀ h, G.RelHead h w → G.hb (.ev h) (.ev k) :=
      fun h ⟨hrel, hrs⟩ => hb_of_sw ⟨hrel, .ev w, hrs, hrf, hk, hacq⟩
    refine (hb w hsrc).mono (fun x hx => ?_) (fun r hr' => ?_)
    · obtain ⟨hxw, h | h | ⟨h, hrh, hh | ⟨r, hr', hh⟩⟩⟩ := hx
      · exact ⟨hxw, Or.inl h⟩
      · subst h; exact ⟨hxw, Or.inr ⟨k, by omega, rfl, Or.inr ⟨.ev k, hrf, .refl⟩⟩⟩
      · exact ⟨hxw, Or.inr ⟨k, by omega, rfl, Or.inl (.single (hbS_hb hh (hsw h hrh)))⟩⟩
      · exact ⟨hxw, Or.inr ⟨k, by omega, rfl, Or.inr ⟨r, hr', .single (hbS_hb hh (hsw h hrh))⟩⟩⟩
    · obtain ⟨h1, h2, h3, h, hrh, hh⟩ := hr'
      exact ⟨h1, h2, h3, k, by omega, rfl, .single (hbS_hb hh (hsw h hrh))⟩

end Helpers

/-- Advancing the simulation by event `k`, given the new thread view,
memory and race detector state of the step. -/
theorem Sim.succ {k : ℕ} {pre : (i : ι) → List Item} {c : Config ι S Loc Val}
    (hs : Sim G k pre c) {s' : S (G.tid k)} {𝓥' : TView Loc} {M' : Memory Loc Val}
    {𝓝' : View Loc}
    (hnext : pre (G.tid k) ++ [Sum.inl k] <+: G.items (G.tid k))
    (hstep : stepItem (prog (G.tid k)) G.lab (c.th (G.tid k)).1 (.inl k) = some s')
    (hcur : G.Bounded 𝓥'.cur (G.Seen (G.tid k) (k + 1)) (G.SeenNR (G.tid k) (k + 1)))
    (hrel : 𝓥'.rel = ⊥)
    (hmemOld : ∀ l, ∀ m ∈ M' l, m = initMsg v0 l ∨ ∃ e < k + 1, (G.lab e).IsWrite ∧
      (G.lab e).loc = l ∧ m.time = G.ts e ∧ m.val = (G.lab e).wval ∧
      G.Bounded (m.view.getD ⊥) (G.MsgSeen e) (G.MsgNR e))
    (hmemInit : ∀ l, initMsg v0 l ∈ M' l)
    (hmemNew : ∀ e < k + 1, (G.lab e).IsWrite → ∃ m ∈ M' (G.lab e).loc, m.time = G.ts e)
    (hnaW : ∀ e < k + 1, (G.lab e).IsWrite → (G.lab e).IsNA → G.ts e ≤ (𝓝' (G.lab e).loc).w)
    (hnaR : ∀ e < k + 1, (G.lab e).IsRead → (G.lab e).IsNA → e ∈ (𝓝' (G.lab e).loc).nr)
    (hids : ∀ l r, r ∈ (𝓝' l).nr ∨ r ∈ (𝓝' l).ar → r < k + 1) :
    Sim G (k + 1) (Function.update pre (G.tid k) (pre (G.tid k) ++ [.inl k]))
      ⟨Function.update c.th (G.tid k) (s', 𝓥'), M', 𝓝'⟩ where
  prefix_ π := by
    by_cases h : π = G.tid k
    · subst h; simpa using hnext
    · simpa [Function.update_of_ne h] using hs.prefix_ π
  state π := by
    by_cases h : π = G.tid k
    · subst h; simpa using runItems_snoc (hs.state (G.tid k)) hstep
    · simpa [Function.update_of_ne h] using hs.state π
  evs π := by
    by_cases h : π = G.tid k
    · subst h
      simp only [Function.update_self, List.filterMap_append, hs.evs, List.range_succ,
        List.filter_append]
      simp
    · simp only [Function.update_of_ne h, hs.evs, List.range_succ, List.filter_append]
      simp [Ne.symm h]
  cur π := by
    by_cases h : π = G.tid k
    · subst h; simpa using hcur
    · simpa [Function.update_of_ne h] using (hs.cur π).mono (fun x hx => G.seen_mono
        (Nat.le_succ k) hx) (fun r hr => G.seenNR_mono (Nat.le_succ k) hr)
  rel π := by
    by_cases h : π = G.tid k
    · subst h; simpa using hrel
    · simpa [Function.update_of_ne h] using hs.rel π
  memOld := hmemOld
  memInit := hmemInit
  memNew := hmemNew
  naW := hnaW
  naR := hnaR
  ids := hids

/-! ## Replaying one event -/

theorem MemOrder.eq_na_of {o : MemOrder} (h : ¬ MemOrder.rlx ≤ o) : o = .na := by
  cases o <;> first | rfl | exact absurd (by decide) h

theorem addRead_w (𝓝 : View Loc) (l l' : Loc) (r : ℕ) (b : Prop) [Decidable b] :
    ((if b then addARead 𝓝 l r else addNRead 𝓝 l r) l').w = (𝓝 l').w := by
  by_cases hl : l' = l <;> split_ifs <;> simp [hl]

theorem addRead_nr (𝓝 : View Loc) (l l' : Loc) (r : ℕ) (b : Prop) [Decidable b] :
    (𝓝 l').nr ⊆ ((if b then addARead 𝓝 l r else addNRead 𝓝 l r) l').nr := by
  by_cases hl : l' = l <;> split_ifs <;> simp [hl, Finset.subset_insert]

theorem addRead_ids (𝓝 : View Loc) (l l' : Loc) (r x : ℕ) (b : Prop) [Decidable b]
    (h : x ∈ ((if b then addARead 𝓝 l r else addNRead 𝓝 l r) l').nr ∨
      x ∈ ((if b then addARead 𝓝 l r else addNRead 𝓝 l r) l').ar) :
    x = r ∨ x ∈ (𝓝 l').nr ∨ x ∈ (𝓝 l').ar := by
  by_cases hl : l' = l
  · subst hl; split_ifs at h <;> simp at h <;> tauto
  · split_ifs at h <;> simp [hl] at h <;> tauto

/-- What a thread has seen, after its release write or update `k`, the
message of `k` may carry. -/
theorem Exec.seen_to_msg {k : ℕ} (hk : k < G.n) (hrh : G.RelHead k k) {x : Ev Loc}
    (hx : G.Seen (G.tid k) (k + 1) x) : G.MsgSeen k x := by
  obtain ⟨hxw, h | ⟨e, he, hte, hh⟩⟩ := hx
  · exact ⟨hxw, Or.inl h⟩
  have hek : G.hbS (.ev e) (.ev k) := by
    rcases Nat.lt_or_ge e k with h | h
    · exact .single (hb_of_tid h hk hte)
    · have : e = k := by omega
      subst this; exact .refl
  rcases hh with hh | ⟨r, hr, hh⟩
  · exact ⟨hxw, Or.inr (Or.inr ⟨k, hrh, Or.inl (hbS_trans hh hek)⟩)⟩
  · exact ⟨hxw, Or.inr (Or.inr ⟨k, hrh, Or.inr ⟨r, hr, hbS_trans hh hek⟩⟩)⟩

theorem Exec.seenNR_to_msg {k : ℕ} (hk : k < G.n) (hrh : G.RelHead k k) {r : ℕ}
    (hx : G.SeenNR (G.tid k) (k + 1) r) : G.MsgNR k r := by
  obtain ⟨h1, h2, h3, e, he, hte, hh⟩ := hx
  have hek : G.hbS (.ev e) (.ev k) := by
    rcases Nat.lt_or_ge e k with h | h
    · exact .single (hb_of_tid h hk hte)
    · have : e = k := by omega
      subst this; exact .refl
  exact ⟨h1, h2, h3, k, hrh, hbS_trans hh hek⟩

/-- The thread's view after a write stays bounded. -/
theorem Exec.cur_write_bounded {k : ℕ} (hk : k < G.n) (hkw : (G.lab k).IsWrite)
    {V : View Loc} (hV : G.Bounded V (G.Seen (G.tid k) (k + 1)) (G.SeenNR (G.tid k) (k + 1)))
    (o : MemOrder) : G.Bounded (V ⊔ writeView o (G.lab k).loc (G.ts k))
      (G.Seen (G.tid k) (k + 1)) (G.SeenNR (G.tid k) (k + 1)) :=
  hV.sup (Bounded.single (fun l => G.seen_init _ _ l)
    ⟨(show G.IsWrite (.ev k) from ⟨hk, hkw⟩), Or.inr ⟨k, by omega, rfl, Or.inl .refl⟩⟩ rfl
    (by split_ifs <;> simp [Exec.tsE])
    (fun r hr => by split_ifs at hr <;> simp at hr))

theorem Exec.writeView_msg_bounded {k : ℕ} (hk : k < G.n) (hkw : (G.lab k).IsWrite)
    (o : MemOrder) : G.Bounded (writeView o (G.lab k).loc (G.ts k)) (G.MsgSeen k) (G.MsgNR k) :=
  Bounded.single (fun l => G.msgSeen_init _ l)
    ⟨(show G.IsWrite (.ev k) from ⟨hk, hkw⟩), Or.inr (Or.inl rfl)⟩ rfl
    (by split_ifs <;> simp [Exec.tsE]) (fun r hr => by split_ifs at hr <;> simp at hr)

section Events

variable (hc : G.Consistent)
include hc

/-- Replaying a read. -/
theorem Exec.sim_read {k : ℕ} {pre : (i : ι) → List Item} {c : Config ι S Loc Val}
    (hr : Reachable prog s0 v0 c) (hs : Sim G k pre c) (hk : k < G.n)
    (hnext : pre (G.tid k) ++ [Sum.inl k] <+: G.items (G.tid k))
    {s' : S (G.tid k)}
    (hstep : stepItem (prog (G.tid k)) G.lab (c.th (G.tid k)).1 (.inl k) = some s')
    {l : Loc} {o : MemOrder} {v : Option Val} (hlab : G.lab k = .R l o v)
    (hok : DrfPreRead l c.na (c.th (G.tid k)).2 c.mem o) :
    ∃ c', Step prog c c' ∧
      Sim G (k + 1) (Function.update pre (G.tid k) (pre (G.tid k) ++ [.inl k])) c' := by
  have hwf := hc.wf
  obtain ⟨kk, hp, rfl⟩ := stepItem_read_inv hstep hlab
  have hread : (G.lab k).IsRead := by rw [hlab]; trivial
  have hl : (G.lab k).loc = l := by rw [hlab]; rfl
  obtain ⟨m, hm, hmt, hmv, hminit, hmb⟩ := G.msg_of_src hc hs hk hread
  rw [hl] at hm
  have hv : m.val = v := by rw [hlab] at hmv; simp [Label.rval] at hmv; exact hmv.symm
  have hrf := G.rfE_src_self hk hread
  have hsl : G.loc (G.src k) = l := by rw [(rfE_src hwf hrf).2.1, hl]
  have hle : ((c.th (G.tid k)).2.cur l).w ≤ m.time := by
    obtain ⟨w', hw', hwl, hwt⟩ := (hs.cur (G.tid k)).1 l
    rw [hmt]; exact hwt.trans (G.seen_le_src hc hk hread hw' (by rw [hwl, hl]))
  have htr : k ∉ (c.na l).ar ∧ k ∉ (c.na l).nr :=
    ⟨fun h => absurd (hs.ids l k (Or.inr h)) (lt_irrefl k),
      fun h => absurd (hs.ids l k (Or.inl h)) (lt_irrefl k)⟩
  have hts := TStep.read_at hr.wfInv.memWf hp hok hm hle htr
  rw [hv] at hts
  refine ⟨_, .mk c (G.tid k) hts, hs.succ hnext hstep ?_ (by simpa [readTView] using hs.rel _)
    ?_ hs.memInit ?_ ?_ ?_ ?_⟩
  · -- the thread's new view
    have hsrcSeen : G.Seen (G.tid k) (k + 1) (G.src k) :=
      ⟨(rfE_src hwf hrf).1, Or.inr ⟨k, by omega, rfl, Or.inr ⟨.ev k, hrf, .refl⟩⟩⟩
    have hold := (hs.cur (G.tid k)).mono (fun x hx => G.seen_mono (Nat.le_succ k) hx)
      (fun r hr => G.seenNR_mono (Nat.le_succ k) hr)
    have hVr : G.Bounded (readView o l m.time k) (G.Seen (G.tid k) (k + 1))
        (G.SeenNR (G.tid k) (k + 1)) := by
      refine Bounded.single (fun l => G.seen_init _ _ l) hsrcSeen hsl
        (by split_ifs <;> simp [hmt]) ?_
      intro r hr'
      split_ifs at hr' with ho
      · simp at hr'
      · simp at hr'; rw [hr']
        refine ⟨hk, hread, ?_, k, by omega, rfl, .refl⟩
        rw [hlab]; exact MemOrder.eq_na_of ho
    unfold readTView; dsimp only
    split_ifs with ha
    · have hacq : (G.lab k).AcqR := by rw [hlab]; exact ha
      exact (hold.sup hVr).sup (G.acq_bounded hc hk hread hacq hminit hmb)
    · exact hold.sup hVr
  · intro l' m' hm'
    rcases hs.memOld l' m' hm' with h | ⟨e, he, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, by omega, h⟩
  · intro e he hew
    rcases Nat.lt_or_ge e k with h | h
    · exact hs.memNew e h hew
    · have : e = k := by omega
      subst this; rw [hlab] at hew; exact absurd hew id
  · intro e he hew hena
    rcases Nat.lt_or_ge e k with h | h
    · rw [addRead_w]; exact hs.naW e h hew hena
    · have : e = k := by omega
      subst this; rw [hlab] at hew; exact absurd hew id
  · intro e he her hena
    rcases Nat.lt_or_ge e k with h | h
    · exact addRead_nr _ _ _ _ _ (hs.naR e h her hena)
    · have : e = k := by omega
      subst this
      rw [hl]
      have ho : o = .na := by rw [hlab] at hena; exact hena
      subst ho
      simp
  · intro l' r hr'
    rcases addRead_ids _ _ _ _ _ _ hr' with h | h
    · omega
    · have := hs.ids l' r h; omega

/-- A write's message is new in memory: its rank is free. -/
theorem Exec.fresh_rank {k : ℕ} {pre : (i : ι) → List Item} {c : Config ι S Loc Val}
    (hs : Sim G k pre c) (hk : k < G.n) (hkw : (G.lab k).IsWrite) :
    ∀ m ∈ c.mem (G.lab k).loc, m.time ≠ G.ts k := by
  have hwf := hc.wf
  intro m hm hmt
  rcases hs.memOld _ m hm with h | ⟨e, he, hew, hel, hmt', -⟩
  · subst h; have := hwf.tsW k hk hkw; simp [initMsg] at hmt; omega
  · have := hwf.tsInj e (by omega) k hk hew hkw hel (by rw [← hmt', hmt])
    omega

/-- Replaying a write. -/
theorem Exec.sim_write {k : ℕ} {pre : (i : ι) → List Item} {c : Config ι S Loc Val}
    (hr : Reachable prog s0 v0 c) (hs : Sim G k pre c) (hrf1 : G.RaceFree (k + 1))
    (hk : k < G.n) (hnext : pre (G.tid k) ++ [Sum.inl k] <+: G.items (G.tid k))
    {s' : S (G.tid k)}
    (hstep : stepItem (prog (G.tid k)) G.lab (c.th (G.tid k)).1 (.inl k) = some s')
    {l : Loc} {o : MemOrder} {v : Val} (hlab : G.lab k = .W l o v)
    (hok : DrfPreWrite l c.na (c.th (G.tid k)).2 c.mem o) :
    ∃ c', Step prog c c' ∧
      Sim G (k + 1) (Function.update pre (G.tid k) (pre (G.tid k) ++ [.inl k])) c' := by
  have hwf := hc.wf
  have hp := stepItem_write_inv hstep hlab
  have hkw : (G.lab k).IsWrite := by rw [hlab]; trivial
  have hl : (G.lab k).loc = l := by rw [hlab]; rfl
  have hfresh := G.fresh_rank hc hs hk hkw
  rw [hl] at hfresh
  have hlt : ((c.th (G.tid k)).2.cur l).w < G.ts k := by
    obtain ⟨w', hw', hwl, hwt⟩ := (hs.cur (G.tid k)).1 l
    exact hwt.trans_lt (G.seen_lt_write hc hk hkw hw' (by rw [hwl, hl]))
  have hlall : ∃ m ∈ c.mem l, m.time ≤ G.ts k :=
    ⟨initMsg v0 l, hs.memInit l, by simp [initMsg]; have := hwf.tsW k hk hkw; omega⟩
  have hts := TStep.write_at (hr.wfInv.threadWf (G.tid k)) hp hok hfresh hlt hlall
  have hold := (hs.cur (G.tid k)).mono (fun x hx => G.seen_mono (Nat.le_succ k) hx)
    (fun r hr => G.seenNR_mono (Nat.le_succ k) hr)
  refine ⟨_, .mk c (G.tid k) hts, hs.succ hnext hstep ?_ (by simpa [writeTView] using hs.rel _)
    ?_ (fun l' => Memory.mem_add_of_mem (hs.memInit l')) ?_ ?_ ?_ ?_⟩
  · have := G.cur_write_bounded hk hkw hold o; rw [hl] at this; exact this
  · intro l' m' hm'
    rcases Memory.mem_add.1 hm' with ⟨rfl, rfl⟩ | hm'
    · refine Or.inr ⟨k, by omega, hkw, hl, rfl, by rw [hlab]; rfl, ?_⟩
      unfold writeRw
      split_ifs with h1 h2
      · -- a release write carries the writer's view
        have hrh : G.RelHead k k := ⟨⟨hk, by rw [hlab]; exact h2⟩,
          rs_refl hk hkw (by rw [hlab]; exact h1)⟩
        simp only [Option.getD_some]
        refine (((hold.mono (fun x hx => G.seen_to_msg hk hrh hx)
          (fun r hr => G.seenNR_to_msg hk hrh hr)).sup ?_).sup ?_).sup
          (Bounded.bot (fun l => G.msgSeen_init _ l))
        · have := G.writeView_msg_bounded hk hkw o; rw [hl] at this; exact this
        · rw [hs.rel]; exact Bounded.bot (fun l => G.msgSeen_init _ l)
      · simp only [Option.getD_some]
        refine ((?_ : G.Bounded _ _ _).sup ?_).sup (Bounded.bot (fun l => G.msgSeen_init _ l))
        · have := G.writeView_msg_bounded hk hkw o; rw [hl] at this; exact this
        · rw [hs.rel]; exact Bounded.bot (fun l => G.msgSeen_init _ l)
      · exact Bounded.bot (fun l => G.msgSeen_init _ l)
    · rcases hs.memOld l' m' hm' with h | ⟨e, he, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, by omega, h⟩
  · intro e he hew
    rcases Nat.lt_or_ge e k with h | h
    · obtain ⟨m, hm, hmt⟩ := hs.memNew e h hew
      exact ⟨m, Memory.mem_add_of_mem hm, hmt⟩
    · have : e = k := by omega
      subst this; rw [hl]; exact ⟨_, Memory.mem_add.2 (Or.inl ⟨rfl, rfl⟩), rfl⟩
  · intro e he hew hena
    split_ifs with ho
    · -- an atomic write leaves the non-atomic write time alone
      rcases Nat.lt_or_ge e k with h | h
      · have := hs.naW e h hew hena
        by_cases hel : (G.lab e).loc = l
        · rw [hel] at this ⊢; simpa using this
        · simpa [hel] using this
      · have : e = k := by omega
        subst this; rw [hlab] at hena; simp [Label.IsNA] at hena; subst hena
        exact absurd ho (by decide)
    · by_cases hel : (G.lab e).loc = l
      · rw [hel]; simp only [setWriteTime_self]
        rcases Nat.lt_or_ge e k with h | h
        · -- an earlier non-atomic write of `l` happens before `k`
          rcases G.hb_related hrf1 (by omega : e < k + 1) (by omega : k < k + 1) (by omega)
            (by omega) (by rw [hel, hl]) (Or.inl hew) (Or.inl hena) with h1 | h1
          · have := coh_hb_mo hc h1
            by_contra hlt'
            exact this ⟨(show G.IsWrite (.ev k) from ⟨hk, hkw⟩),
              (show G.IsWrite (.ev e) from ⟨by omega, hew⟩),
              (show (G.lab k).loc = (G.lab e).loc by rw [hel, hl]),
              (show G.ts k < G.ts e by omega)⟩
          · exact absurd (hb_lt hwf h1) (by omega)
        · have : e = k := by omega
          subst this; exact le_rfl
      · simp only [setWriteTime_ne _ _ hel]
        rcases Nat.lt_or_ge e k with h | h
        · exact hs.naW e h hew hena
        · have : e = k := by omega
          subst this; exact absurd hl hel
  · intro e he her hena
    rcases Nat.lt_or_ge e k with h | h
    · have := hs.naR e h her hena
      split_ifs <;> by_cases hel : (G.lab e).loc = l <;> simp_all
    · have : e = k := by omega
      subst this; rw [hlab] at her; exact absurd her id
  · intro l' r hr'
    have : r ∈ (c.na l').nr ∨ r ∈ (c.na l').ar := by
      split_ifs at hr' <;> by_cases hl' : l' = l <;> simp_all
    have := hs.ids l' r this; omega

end Events

end RC11

end ORC11
