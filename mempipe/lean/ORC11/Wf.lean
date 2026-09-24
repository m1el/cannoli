import ORC11.Lemmas

/-!
# ORC11: well-formedness and latest steps

* `WfInv`: the well-formedness invariant of ORC11 runs. Thread views satisfy
  `rel ⊑ cur ⊑ acq` and are closed in memory, messages are well formed
  (`memory.v` L674 `message_wf`) with closed views (L476 `closed_view_opt`),
  and no cell is empty. This is the part of the Coq's `Wf` for thread states
  and memories (`tview.v` `closed_tview`, `memory.v` `memory_wf`) that our
  restricted machine needs.
* `TStepL`/`StepL`: steps in which reads read the latest message and writes go
  after every existing message of their location. They are special cases of
  `TStep`/`Step`, and a well-formed thread can always take one.
-/

namespace ORC11

variable {Loc Val : Type} [DecidableEq Loc]

/-! ## Closedness -/

section Closed

omit [DecidableEq Loc]

/-- `memory.v` `closed_view_mono`-style: closedness survives memory growth. -/
theorem View.Closed.mono {V : View Loc} {M M' : Memory Loc Val} (h : V.Closed M)
    (hM : ∀ l, ∀ m ∈ M l, m ∈ M' l) : V.Closed M' := fun l =>
  (h l).imp_right fun ⟨m, hm, ht⟩ => ⟨m, hM l m hm, ht⟩

theorem View.ClosedOpt.mono {V : Option (View Loc)} {M M' : Memory Loc Val}
    (h : View.ClosedOpt V M) (hM : ∀ l, ∀ m ∈ M l, m ∈ M' l) : View.ClosedOpt V M' :=
  fun W hW => (h W hW).mono hM

theorem View.closed_bot (M : Memory Loc Val) : (⊥ : View Loc).Closed M :=
  fun _ => Or.inl rfl

theorem View.Closed.sup {V W : View Loc} {M : Memory Loc Val} (hV : V.Closed M)
    (hW : W.Closed M) : (V ⊔ W).Closed M := by
  intro l
  show max (V l).w (W l).w = 0 ∨ ∃ m ∈ M l, max (V l).w (W l).w ≤ m.time
  rcases le_total (V l).w (W l).w with h | h
  · rw [max_eq_right h]; exact hW l
  · rw [max_eq_left h]; exact hV l

theorem View.ClosedOpt.getD {V : Option (View Loc)} {M : Memory Loc Val}
    (h : View.ClosedOpt V M) : (V.getD ⊥).Closed M := by
  cases V with
  | none => exact View.closed_bot M
  | some W => exact h W rfl

/-- The view of a well-formed message records at most its own time. -/
theorem Msg.Wf.getD_le {l : Loc} {m : Msg Loc Val} (h : m.Wf l) :
    ((m.view.getD ⊥) l).w ≤ m.time := by
  cases hv : m.view with
  | none => exact Nat.zero_le _
  | some V => exact (h V hv).le

end Closed

theorem readView_closed {o : MemOrder} {l : Loc} {t tr : ℕ} {M : Memory Loc Val}
    (h : ∃ m ∈ M l, t ≤ m.time) : (readView o l t tr).Closed M := by
  intro l'
  by_cases hl : l' = l
  · subst hl; rw [readView_w]; exact Or.inr h
  · rw [readView_ne o t tr hl]; exact Or.inl rfl

theorem writeView_closed {o : MemOrder} {l : Loc} {t : ℕ} {M : Memory Loc Val}
    (h : ∃ m ∈ M l, t ≤ m.time) : (writeView o l t).Closed M := by
  intro l'
  by_cases hl : l' = l
  · subst hl; rw [writeView_w]; exact Or.inr h
  · rw [writeView_ne o t hl]; exact Or.inl rfl

/-! ## Thread-view updates -/

section TViews

omit [DecidableEq Loc] in
theorem acqrel_le_rlx {o : MemOrder} (h : MemOrder.acqrel ≤ o) : MemOrder.rlx ≤ o := by
  revert h; cases o <;> decide

theorem readTView_wf {𝓥 : TView Loc} {o : MemOrder} {R V : View Loc} (h : 𝓥.Wf) :
    (readTView 𝓥 o R V).Wf := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.trans (readTView_cur_le _ _ _ _), ?_⟩
  show (if MemOrder.acqrel ≤ o then 𝓥.cur ⊔ V ⊔ R else 𝓥.cur ⊔ V) ≤
    (if MemOrder.rlx ≤ o then 𝓥.acq ⊔ V ⊔ R else 𝓥.acq ⊔ V)
  by_cases ha : MemOrder.acqrel ≤ o
  · simp only [ha, acqrel_le_rlx ha, ↓reduceIte]
    exact sup_le_sup_right (sup_le_sup_right h2 _) _
  · simp only [ha, ↓reduceIte]; split
    · exact (sup_le_sup_right h2 _).trans le_sup_left
    · exact sup_le_sup_right h2 _

omit [DecidableEq Loc] in
theorem readTView_cur_le_sup (𝓥 : TView Loc) (o : MemOrder) (R V : View Loc) :
    (readTView 𝓥 o R V).cur ≤ 𝓥.cur ⊔ V ⊔ R := by
  show (if MemOrder.acqrel ≤ o then 𝓥.cur ⊔ V ⊔ R else 𝓥.cur ⊔ V) ≤ _
  split
  · exact le_rfl
  · exact le_sup_left

omit [DecidableEq Loc] in
theorem readTView_cur_closed {𝓥 : TView Loc} {o : MemOrder} {R V : View Loc}
    {M : Memory Loc Val} (hcur : 𝓥.cur.Closed M) (hR : R.Closed M) (hV : V.Closed M) :
    (readTView 𝓥 o R V).cur.Closed M := by
  show (if MemOrder.acqrel ≤ o then 𝓥.cur ⊔ V ⊔ R else 𝓥.cur ⊔ V).Closed M
  split
  · exact (hcur.sup hV).sup hR
  · exact hcur.sup hV

omit [DecidableEq Loc] in
theorem readTView_acq_closed {𝓥 : TView Loc} {o : MemOrder} {R V : View Loc}
    {M : Memory Loc Val} (hacq : 𝓥.acq.Closed M) (hR : R.Closed M) (hV : V.Closed M) :
    (readTView 𝓥 o R V).acq.Closed M := by
  show (if MemOrder.rlx ≤ o then 𝓥.acq ⊔ V ⊔ R else 𝓥.acq ⊔ V).Closed M
  split
  · exact (hacq.sup hV).sup hR
  · exact hacq.sup hV

end TViews

theorem writeTView_wf {𝓥 : TView Loc} {o : MemOrder} {l : Loc} {t : ℕ} (h : 𝓥.Wf) :
    (writeTView 𝓥 o l t).Wf :=
  ⟨h.1.trans le_sup_left, sup_le_sup_right h.2 _⟩

theorem writeRw_closed {𝓥 : TView Loc} {o : MemOrder} {l : Loc} {t : ℕ} {Rr : View Loc}
    {M : Memory Loc Val} (hrel : 𝓥.rel.Closed M) (hcur : 𝓥.cur.Closed M)
    (hW : (writeView o l t).Closed M) (hRr : Rr.Closed M) :
    View.ClosedOpt (writeRw 𝓥 o l t Rr) M := by
  intro W hW'
  unfold writeRw at hW'
  split at hW'
  · simp only [Option.some.injEq] at hW'; subst hW'
    split
    · exact ((hcur.sup hW).sup hrel).sup hRr
    · exact (hW.sup hrel).sup hRr
  · cases hW'

/-- The written message is well formed if the writer's views and `Rr` do not
exceed the new time at `l`. -/
theorem writeRw_wf {𝓥 : TView Loc} {o : MemOrder} {l : Loc} {t : ℕ} {Rr : View Loc}
    (hrel : (𝓥.rel l).w ≤ t) (hcur : (𝓥.cur l).w ≤ t) (hRr : (Rr l).w ≤ t) :
    ∀ W, writeRw 𝓥 o l t Rr = some W → (W l).w = t := by
  intro W hW
  unfold writeRw at hW
  split at hW
  · simp only [Option.some.injEq] at hW; subst hW
    have := writeView_w o l t
    split <;> simp only [View.sup_apply', TimeInfo.sup_w] <;> omega
  · cases hW

/-! ## The invariant -/

/-- The thread-local part of `WfInv` (`tview.v` `closed_tview` plus `TView.Wf`). -/
structure ThreadWf (𝓥 : TView Loc) (M : Memory Loc Val) : Prop where
  wf : 𝓥.Wf
  rel : 𝓥.rel.Closed M
  cur : 𝓥.cur.Closed M
  acq : 𝓥.acq.Closed M

/-- The memory part of `WfInv` (`memory.v` `memory_wf` and `msg_closed`). -/
structure MemWf (M : Memory Loc Val) : Prop where
  msgWf : ∀ l, ∀ m ∈ M l, m.Wf l
  msgClosed : ∀ l, ∀ m ∈ M l, View.ClosedOpt m.view M
  nonempty : ∀ l, M l ≠ []

omit [DecidableEq Loc] in
theorem ThreadWf.mono {𝓥 : TView Loc} {M M' : Memory Loc Val} (h : ThreadWf 𝓥 M)
    (hM : ∀ l, ∀ m ∈ M l, m ∈ M' l) : ThreadWf 𝓥 M' :=
  ⟨h.wf, h.rel.mono hM, h.cur.mono hM, h.acq.mono hM⟩

theorem ReadStep.threadWf {𝓥 𝓥' : TView Loc} {M : Memory Loc Val} {tr : ℕ} {l : Loc}
    {m : Msg Loc Val} {o : MemOrder} (hT : ThreadWf 𝓥 M) (hM : MemWf M)
    (h : ReadStep 𝓥 M tr l m o 𝓥') : ThreadWf 𝓥' M := by
  rw [h.read.eq]
  have hV : (readView o l m.time tr).Closed M := readView_closed ⟨m, h.mem, le_rfl⟩
  have hR := (hM.msgClosed l m h.mem).getD
  exact ⟨readTView_wf hT.wf, hT.rel, readTView_cur_closed hT.cur hR hV,
    readTView_acq_closed hT.acq hR hV⟩

theorem WriteStep.threadWf {𝓥 𝓥' : TView Loc} {M M' : Memory Loc Val} {l : Loc}
    {m : Msg Loc Val} {o : MemOrder} {Rr : View Loc} (hT : ThreadWf 𝓥 M) (hM : MemWf M)
    (h : WriteStep 𝓥 M l m o Rr 𝓥' M') : ThreadWf 𝓥' M' ∧ MemWf M' := by
  obtain ⟨⟨_, hM', hwf, hcl, _, _⟩, ⟨_, _, h𝓥'⟩⟩ := h
  subst hM' h𝓥'
  have hsub : ∀ l', ∀ m' ∈ M l', m' ∈ M.add l m l' := fun _ _ => Memory.mem_add_of_mem
  have hT' := hT.mono hsub
  have hW : (writeView o l m.time).Closed (M.add l m) :=
    writeView_closed ⟨m, by simp, le_rfl⟩
  refine ⟨⟨writeTView_wf hT.wf, hT'.rel, hT'.cur.sup hW, hT'.acq.sup hW⟩, ?_, ?_, ?_⟩
  · intro l' m' hm'
    rcases Memory.mem_add.1 hm' with ⟨rfl, rfl⟩ | h
    · exact hwf
    · exact hM.msgWf _ _ h
  · intro l' m' hm'
    rcases Memory.mem_add.1 hm' with ⟨rfl, rfl⟩ | h
    · exact hcl
    · exact (hM.msgClosed _ _ h).mono hsub
  · intro l'
    by_cases hl : l' = l
    · subst hl; simp
    · rw [Memory.add_ne _ _ hl]; exact hM.nonempty l'

/-- Thread steps preserve well-formedness. -/
theorem TStep.wf {S : Type} {prog : S → Instr Loc Val S} {s s' : S} {𝓥 𝓥' : TView Loc}
    {M M' : Memory Loc Val} {𝓝 𝓝' : View Loc} (hT : ThreadWf 𝓥 M) (hM : MemWf M)
    (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') : ThreadWf 𝓥' M' ∧ MemWf M' := by
  rcases h.cases' with ⟨_, _, _, _, R, rfl⟩ | ⟨_, _, _, W⟩ |
    ⟨_, _, _, _, _, _, _, R, -, W⟩ | ⟨rfl, rfl⟩
  · exact ⟨R.threadWf hT hM, hM⟩
  · exact W.threadWf hT hM
  · exact W.threadWf (R.threadWf hT hM) hM
  · exact ⟨hT, hM⟩

section Pool

variable {ι : Type} [DecidableEq ι] {S : ι → Type}
  {prog : (i : ι) → S i → Instr Loc Val (S i)}

/-- The well-formedness invariant of ORC11 runs. -/
structure WfInv (c : Config ι S Loc Val) : Prop where
  /-- `rel ⊑ cur ⊑ acq`. -/
  tview : ∀ i, (c.th i).2.Wf
  rel : ∀ i, (c.th i).2.rel.Closed c.mem
  cur : ∀ i, (c.th i).2.cur.Closed c.mem
  acq : ∀ i, (c.th i).2.acq.Closed c.mem
  msgWf : ∀ l, ∀ m ∈ c.mem l, m.Wf l
  msgClosed : ∀ l, ∀ m ∈ c.mem l, View.ClosedOpt m.view c.mem
  nonempty : ∀ l, c.mem l ≠ []

omit [DecidableEq Loc] [DecidableEq ι] in
theorem WfInv.threadWf {c : Config ι S Loc Val} (h : WfInv c) (i : ι) :
    ThreadWf (c.th i).2 c.mem :=
  ⟨h.tview i, h.rel i, h.cur i, h.acq i⟩

omit [DecidableEq Loc] [DecidableEq ι] in
theorem WfInv.memWf {c : Config ι S Loc Val} (h : WfInv c) : MemWf c.mem :=
  ⟨h.msgWf, h.msgClosed, h.nonempty⟩

omit [DecidableEq Loc] [DecidableEq ι] in
theorem wfInv_init (s0 : (i : ι) → S i) (v0 : Loc → Option Val) :
    WfInv (initConfig s0 v0) where
  tview _ := ⟨bot_le, le_rfl⟩
  rel _ := View.closed_bot _
  cur _ l := Or.inr ⟨⟨1, v0 l, none⟩, List.mem_singleton_self _, le_rfl⟩
  acq _ l := Or.inr ⟨⟨1, v0 l, none⟩, List.mem_singleton_self _, le_rfl⟩
  msgWf l m hm := by
    simp only [initConfig, List.mem_singleton] at hm; subst hm; intro V hV; cases hV
  msgClosed l m hm := by
    simp only [initConfig, List.mem_singleton] at hm; subst hm; intro V hV; cases hV
  nonempty l := by simp [initConfig]

theorem wfInv_step {c c' : Config ι S Loc Val} (h : WfInv c) (hs : Step prog c c') :
    WfInv c' := by
  cases hs with
  | @mk i s' 𝓥' M' 𝓝' hst =>
    obtain ⟨hT', hM'⟩ := hst.wf (h.threadWf i) h.memWf
    have key : ∀ j, ThreadWf (Function.update c.th i (s', 𝓥') j).2 M' := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa using hT'
      · rw [Function.update_of_ne hj]; exact (h.threadWf j).mono hst.mem_sub
    exact ⟨fun j => (key j).wf, fun j => (key j).rel, fun j => (key j).cur,
      fun j => (key j).acq, hM'.msgWf, hM'.msgClosed, hM'.nonempty⟩

theorem Reachable.wfInv {s0 : (i : ι) → S i} {v0 : Loc → Option Val}
    {c : Config ι S Loc Val} (h : Reachable prog s0 v0 c) : WfInv c := by
  induction h with
  | refl => exact wfInv_init s0 v0
  | tail _ hs ih => exact wfInv_step ih hs

end Pool

/-! ## Latest steps -/

/-- A thread step (`TStep`) that reads the latest message of its location and
writes after every existing message of its location. -/
inductive TStepL {S : Type} (prog : S → Instr Loc Val S) :
    S → TView Loc → Memory Loc Val → View Loc →
      S → TView Loc → Memory Loc Val → View Loc → Prop
  | read {s 𝓥 M 𝓝 l o k tr 𝓥' 𝓝'} {m : Msg Loc Val}
      (INSTR : prog s = .read l o k)
      (DRFPre : DrfPre 𝓝 𝓥 M (.read l m.val o))
      (PStep : MachineStep 𝓥 M (.read l m.val o) (some tr) [] 𝓥' M)
      (DRFPost : DrfPost 𝓝 (.read l m.val o) (some tr) [] 𝓝')
      (LATEST : IsLatest (M l) m) :
      TStepL prog s 𝓥 M 𝓝 (k m.val) 𝓥' M 𝓝'
  | write {s 𝓥 M 𝓝 l o v k 𝓥' M' 𝓝'} {m : Msg Loc Val}
      (INSTR : prog s = .write l o v k)
      (DRFPre : DrfPre 𝓝 𝓥 M (.write l v o))
      (PStep : MachineStep 𝓥 M (.write l v o) none [(l, m)] 𝓥' M')
      (DRFPost : DrfPost 𝓝 (.write l v o) none [(l, m)] 𝓝')
      (LATEST : ∀ m' ∈ M l, m'.time < m.time) :
      TStepL prog s 𝓥 M 𝓝 k 𝓥' M' 𝓝'
  | update {s 𝓥 M 𝓝 l or ow f k v tr 𝓥' M' 𝓝'} {m : Msg Loc Val}
      (INSTR : prog s = .update l or ow f k)
      (DRFPre : DrfPre 𝓝 𝓥 M (.update l v (f v) or ow))
      (PStep : MachineStep 𝓥 M (.update l v (f v) or ow) (some tr) [(l, m)] 𝓥' M')
      (DRFPost : DrfPost 𝓝 (.update l v (f v) or ow) (some tr) [(l, m)] 𝓝')
      (LATEST : ∀ m' ∈ M l, m'.time < m.time) :
      TStepL prog s 𝓥 M 𝓝 (k v) 𝓥' M' 𝓝'
  | choose {s 𝓥 M 𝓝 k} (b : Bool)
      (INSTR : prog s = .choose k) :
      TStepL prog s 𝓥 M 𝓝 (k b) 𝓥 M 𝓝

theorem TStepL.toTStep {S : Type} {prog : S → Instr Loc Val S} {s s' : S}
    {𝓥 𝓥' : TView Loc} {M M' : Memory Loc Val} {𝓝 𝓝' : View Loc}
    (h : TStepL prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝' := by
  cases h with
  | read INSTR DRFPre PStep DRFPost => exact .read INSTR DRFPre PStep DRFPost
  | write INSTR DRFPre PStep DRFPost => exact .write INSTR DRFPre PStep DRFPost
  | update INSTR DRFPre PStep DRFPost => exact .update INSTR DRFPre PStep DRFPost
  | choose b INSTR => exact .choose b INSTR

section Pool

variable {ι : Type} [DecidableEq ι] {S : ι → Type}
  (prog : (i : ι) → S i → Instr Loc Val (S i))

/-- `Step` with latest thread steps. -/
inductive StepL : Config ι S Loc Val → Config ι S Loc Val → Prop
  | mk (c : Config ι S Loc Val) (i : ι) {s' : S i} {𝓥' M' 𝓝'}
      (h : TStepL (prog i) (c.th i).1 (c.th i).2 c.mem c.na s' 𝓥' M' 𝓝') :
      StepL c ⟨Function.update c.th i (s', 𝓥'), M', 𝓝'⟩

variable {prog}

theorem StepL.toStep {c c' : Config ι S Loc Val} (h : StepL prog c c') : Step prog c c' := by
  cases h with
  | mk i h => exact .mk c i h.toTStep

theorem StepL.reflTransGen_toStep {c c' : Config ι S Loc Val}
    (h : Relation.ReflTransGen (StepL prog) c c') : Relation.ReflTransGen (Step prog) c c' :=
  Relation.ReflTransGen.mono (r := StepL prog) (p := Step prog)
    (fun _ _ => StepL.toStep) _ _ h

end Pool

/-! ## Existence of latest steps -/

section Exists

omit [DecidableEq Loc]

/-- The largest time in a cell (`0` for an empty cell). -/
def maxTime : List (Msg Loc Val) → ℕ
  | [] => 0
  | m :: C => max m.time (maxTime C)

theorem le_maxTime {C : List (Msg Loc Val)} {m : Msg Loc Val} (h : m ∈ C) :
    m.time ≤ maxTime C := by
  induction C with
  | nil => cases h
  | cons a C ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem exists_maxTime {C : List (Msg Loc Val)} (h : C ≠ []) :
    ∃ m ∈ C, m.time = maxTime C := by
  induction C with
  | nil => exact absurd rfl h
  | cons a C ih =>
    by_cases hC : C = []
    · subst hC; exact ⟨a, List.mem_singleton_self _, by simp [maxTime]⟩
    · obtain ⟨m, hm, ht⟩ := ih hC
      rcases le_total a.time (maxTime C) with hle | hle
      · exact ⟨m, List.mem_cons_of_mem _ hm, by simp only [maxTime]; omega⟩
      · exact ⟨a, List.mem_cons_self, by simp only [maxTime]; omega⟩

/-- Every nonempty cell has a latest message. -/
theorem exists_isLatest {C : List (Msg Loc Val)} (h : C ≠ []) : ∃ m, IsLatest C m := by
  obtain ⟨m, hm, ht⟩ := exists_maxTime h
  exact ⟨m, hm, fun m' hm' => ht ▸ le_maxTime hm'⟩

theorem exists_fresh_id (s : Finset ℕ) : ∃ n, n ∉ s := by
  obtain ⟨n, hn⟩ := s.exists_nat_subset_range
  exact ⟨n, fun h => by simpa using hn h⟩

end Exists

section Exists

variable {S : Type} {prog : S → Instr Loc Val S} {s : S} {𝓥 : TView Loc}
  {M : Memory Loc Val} {𝓝 : View Loc}

omit [DecidableEq Loc] in
theorem cur_w_le_latest {l : Loc} {m : Msg Loc Val} (hcur : 𝓥.cur.Closed M)
    (hm : IsLatest (M l) m) : (𝓥.cur l).w ≤ m.time := by
  rcases hcur l with h0 | ⟨m', hm', hle⟩
  · omega
  · exact hle.trans (hm.2 m' hm')

/-- A thread at a read can read the latest message. -/
theorem TStepL.exists_read {l : Loc} {o : MemOrder} {k : Option Val → S}
    (hcur : 𝓥.cur.Closed M) (hwf : ∀ l, ∀ m ∈ M l, m.Wf l)
    (hp : prog s = .read l o k) (hdrf : DrfPreRead l 𝓝 𝓥 M o)
    {m : Msg Loc Val} (hm : IsLatest (M l) m) :
    ∃ 𝓥' 𝓝', TStepL prog s 𝓥 M 𝓝 (k m.val) 𝓥' M 𝓝' := by
  obtain ⟨tr, htr⟩ := exists_fresh_id ((𝓝 l).ar ∪ (𝓝 l).nr)
  refine ⟨readTView 𝓥 o (m.view.getD ⊥) (readView o l m.time tr),
    if MemOrder.rlx ≤ o then addARead 𝓝 l tr else addNRead 𝓝 l tr,
    .read hp hdrf (.read l m o _ tr
      ⟨⟨cur_w_le_latest hcur hm, (hwf l m hm.1).getD_le, rfl⟩, hm.1⟩)
      (.read l tr o _ _ ?_) hm⟩
  by_cases ho : MemOrder.rlx ≤ o
  · simp only [DrfPostRead, ho, ↓reduceIte, true_and]
    exact fun h => htr (Finset.mem_union_left _ h)
  · simp only [DrfPostRead, ho, ↓reduceIte, true_and]
    exact fun h => htr (Finset.mem_union_right _ h)

/-- A thread at a write can write after every existing message. -/
theorem TStepL.exists_write {l : Loc} {o : MemOrder} {v : Val} {k : S}
    (h𝓥 : 𝓥.Wf) (hrel : 𝓥.rel.Closed M) (hcur : 𝓥.cur.Closed M) (hne : ∀ l, M l ≠ [])
    (hp : prog s = .write l o v k) (hdrf : DrfPreWrite l 𝓝 𝓥 M o) :
    ∃ (m : Msg Loc Val) (𝓥' : TView Loc) (𝓝' : View Loc), m.val = some v ∧
      (∀ m' ∈ M l, m'.time < m.time) ∧ TStepL prog s 𝓥 M 𝓝 k 𝓥' (M.add l m) 𝓝' := by
  have hlt : ∀ m' ∈ M l, m'.time < maxTime (M l) + 1 :=
    fun m' h => Nat.lt_succ_of_le (le_maxTime h)
  have hcurlt : (𝓥.cur l).w < maxTime (M l) + 1 := by
    rcases hcur l with h0 | ⟨m', hm', hle⟩
    · omega
    · exact lt_of_le_of_lt hle (hlt m' hm')
  obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil _ (hne l)
  let t := maxTime (M l) + 1
  let m : Msg Loc Val := ⟨t, some v, writeRw 𝓥 o l t ⊥⟩
  have hsub : ∀ l', ∀ m' ∈ M l', m' ∈ M.add l m l' := fun _ _ => Memory.mem_add_of_mem
  have MW : MemoryWrite M l m (M.add l m) :=
    { fresh := fun m' h => (hlt m' h).ne
      eq := rfl
      wf := writeRw_wf ((TimeInfo.w_mono (h𝓥.1 l)).trans hcurlt.le) hcurlt.le (by simp)
      closed := writeRw_closed (hrel.mono hsub) (hcur.mono hsub)
        (writeView_closed ⟨m, by simp, le_rfl⟩) (View.closed_bot _)
      isval := rfl
      lall := ⟨m0, hm0, (hlt m0 hm0).le⟩ }
  refine ⟨m, writeTView 𝓥 o l t,
    if MemOrder.rlx ≤ o then addAWrite 𝓝 l t else setWriteTime 𝓝 l t, rfl, hlt,
    .write hp hdrf (.write l m o _ _ v rfl ⟨MW, ⟨hcurlt, rfl, rfl⟩⟩)
      (.write l m v o _ ?_) hlt⟩
  by_cases ho : MemOrder.rlx ≤ o <;> simp [DrfPostWrite, ho, m, t]

/-- A thread at an update can read the latest message and write right after
it. -/
theorem TStepL.exists_update {l : Loc} {or ow : MemOrder} {f : Val → Val}
    {k : Val → S} (h𝓥 : 𝓥.Wf) (hrel : 𝓥.rel.Closed M) (hcur : 𝓥.cur.Closed M)
    (hwf : ∀ l, ∀ m ∈ M l, m.Wf l) (hcl : ∀ l, ∀ m ∈ M l, View.ClosedOpt m.view M)
    (hp : prog s = .update l or ow f k)
    (hdrf : DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow)
    {m1 : Msg Loc Val} {v : Val} (hm1 : IsLatest (M l) m1) (hv : m1.val = some v) :
    ∃ (m2 : Msg Loc Val) (𝓥' : TView Loc) (𝓝' : View Loc), m2.time = m1.time + 1 ∧
      m2.val = some (f v) ∧ (∀ m' ∈ M l, m'.time < m2.time) ∧
      TStepL prog s 𝓥 M 𝓝 (k v) 𝓥' (M.add l m2) 𝓝' := by
  obtain ⟨tr, htr⟩ := exists_fresh_id (𝓝 l).ar
  have hmem := hm1.1
  have hcurl := cur_w_le_latest hcur hm1
  have hRl := (hwf l m1 hmem).getD_le
  have hRcl := (hcl l m1 hmem).getD
  let t := m1.time + 1
  let R := m1.view.getD ⊥
  let V : View Loc := readView or l m1.time tr
  let 𝓥2 := readTView 𝓥 or R V
  have h2cur : (𝓥2.cur l).w ≤ m1.time := by
    have h := TimeInfo.w_mono (readTView_cur_le_sup 𝓥 or (m1.view.getD ⊥)
      (readView or l m1.time tr) l)
    simp only [View.sup_apply', TimeInfo.sup_w, readView_w] at h
    exact h.trans (by omega)
  have h2rel : (𝓥2.rel l).w ≤ m1.time := (TimeInfo.w_mono (h𝓥.1 l)).trans hcurl
  have h2curcl : 𝓥2.cur.Closed M :=
    readTView_cur_closed hcur hRcl (readView_closed ⟨m1, hmem, le_rfl⟩)
  have hlt : ∀ m' ∈ M l, m'.time < t := fun m' h => Nat.lt_succ_of_le (hm1.2 m' h)
  let m2 : Msg Loc Val := ⟨t, some (f v), writeRw 𝓥2 ow l t R⟩
  have hsub : ∀ l', ∀ m' ∈ M l', m' ∈ M.add l m2 l' := fun _ _ => Memory.mem_add_of_mem
  have MW : MemoryWrite M l m2 (M.add l m2) :=
    { fresh := fun m' h => (hlt m' h).ne
      eq := rfl
      wf := writeRw_wf (Nat.le_succ_of_le h2rel) (Nat.le_succ_of_le h2cur)
        (Nat.le_succ_of_le hRl)
      closed := writeRw_closed (hrel.mono hsub) (h2curcl.mono hsub)
        (writeView_closed ⟨m2, by simp, le_rfl⟩) (hRcl.mono hsub)
      isval := rfl
      lall := ⟨m1, hmem, Nat.le_succ _⟩ }
  refine ⟨m2, writeTView 𝓥2 ow l t, addAWrite (addARead 𝓝 l tr) l t, rfl, rfl, hlt,
    .update hp hdrf
      (.update l m1 m2 or ow 𝓥2 _ _ tr v (f v) hv rfl rfl
        ⟨⟨hcurl, hRl, rfl⟩, hmem⟩ ⟨MW, ⟨Nat.lt_succ_of_le h2cur, rfl, rfl⟩⟩)
      (.update l m2 or ow tr v (f v) _ ⟨rfl, htr⟩) hlt⟩

/-- A thread at a choice can take either branch. -/
theorem TStepL.exists_choose {k : Bool → S} (hp : prog s = .choose k) (b : Bool) :
    TStepL prog s 𝓥 M 𝓝 (k b) 𝓥 M 𝓝 :=
  .choose b hp

end Exists

section Pool

variable {ι : Type} [DecidableEq ι] {S : ι → Type}
  {prog : (i : ι) → S i → Instr Loc Val (S i)}

/-- A latest step of thread `i` is a pool step. -/
theorem StepL.of_tstepL {c : Config ι S Loc Val} {i : ι} {s' : S i} {𝓥' : TView Loc}
    {M' : Memory Loc Val} {𝓝' : View Loc}
    (h : TStepL (prog i) (c.th i).1 (c.th i).2 c.mem c.na s' 𝓥' M' 𝓝') :
    StepL prog c ⟨Function.update c.th i (s', 𝓥'), M', 𝓝'⟩ :=
  .mk c i h

end Pool

end ORC11
