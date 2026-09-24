import ORC11.Program

/-!
# ORC11: lemmas

Inversion lemmas for thread steps, computation rules for the view updates,
and program-independent invariants of reachable configurations.
-/

namespace ORC11

variable {Loc Val : Type} [DecidableEq Loc]

/-! ## Views -/

@[simp] theorem View.sup_apply' (V W : View Loc) (l : Loc) : (V ⊔ W) l = V l ⊔ W l := rfl
@[simp] theorem View.bot_apply' (l : Loc) : (⊥ : View Loc) l = ⊥ := rfl

theorem View.le_apply {V W : View Loc} (h : V ≤ W) (l : Loc) : V l ≤ W l := h l

theorem readView_self (o : MemOrder) (l : Loc) (t tr : ℕ) :
    readView o l t tr l =
      (if MemOrder.rlx ≤ o then ⟨t, ∅, ∅, {tr}⟩ else ⟨t, ∅, {tr}, ∅⟩) := by
  simp [readView]

@[simp] theorem readView_ne (o : MemOrder) {l l' : Loc} (t tr : ℕ) (h : l' ≠ l) :
    readView o l t tr l' = ⊥ := by
  simp [readView, h]

theorem writeView_self (o : MemOrder) (l : Loc) (t : ℕ) :
    writeView o l t l = (if MemOrder.rlx ≤ o then ⟨t, {t}, ∅, ∅⟩ else ⟨t, ∅, ∅, ∅⟩) := by
  simp [writeView]

@[simp] theorem writeView_ne (o : MemOrder) {l l' : Loc} (t : ℕ) (h : l' ≠ l) :
    writeView o l t l' = ⊥ := by
  simp [writeView, h]

@[simp] theorem readView_w (o : MemOrder) (l : Loc) (t tr : ℕ) :
    (readView o l t tr l).w = t := by
  rw [readView_self]; split <;> rfl

@[simp] theorem readView_aw (o : MemOrder) (l : Loc) (t tr : ℕ) :
    (readView o l t tr l).aw = ∅ := by
  rw [readView_self]; split <;> rfl

@[simp] theorem readView_nr (o : MemOrder) (l : Loc) (t tr : ℕ) :
    (readView o l t tr l).nr = if MemOrder.rlx ≤ o then ∅ else {tr} := by
  rw [readView_self]; split <;> rfl

@[simp] theorem readView_ar (o : MemOrder) (l : Loc) (t tr : ℕ) :
    (readView o l t tr l).ar = if MemOrder.rlx ≤ o then {tr} else ∅ := by
  rw [readView_self]; split <;> rfl

@[simp] theorem writeView_w (o : MemOrder) (l : Loc) (t : ℕ) :
    (writeView o l t l).w = t := by
  rw [writeView_self]; split <;> rfl

@[simp] theorem writeView_aw (o : MemOrder) (l : Loc) (t : ℕ) :
    (writeView o l t l).aw = if MemOrder.rlx ≤ o then {t} else ∅ := by
  rw [writeView_self]; split <;> rfl

@[simp] theorem writeView_nr (o : MemOrder) (l : Loc) (t : ℕ) :
    (writeView o l t l).nr = ∅ := by
  rw [writeView_self]; split <;> rfl

@[simp] theorem writeView_ar (o : MemOrder) (l : Loc) (t : ℕ) :
    (writeView o l t l).ar = ∅ := by
  rw [writeView_self]; split <;> rfl

theorem readTView_cur_le (𝓥 : TView Loc) (o : MemOrder) (R V : View Loc) :
    𝓥.cur ≤ (readTView 𝓥 o R V).cur := by
  unfold readTView; split
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_left

theorem readTView_V_le (𝓥 : TView Loc) (o : MemOrder) (R V : View Loc) :
    V ≤ (readTView 𝓥 o R V).cur := by
  unfold readTView; split
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem readTView_R_le (𝓥 : TView Loc) {o : MemOrder} (R V : View Loc)
    (h : MemOrder.acqrel ≤ o) : R ≤ (readTView 𝓥 o R V).cur := by
  unfold readTView; rw [if_pos h]; exact le_sup_right

theorem writeTView_cur_le (𝓥 : TView Loc) (o : MemOrder) (l : Loc) (t : ℕ) :
    𝓥.cur ≤ (writeTView 𝓥 o l t).cur := le_sup_left

theorem writeTView_V_le (𝓥 : TView Loc) (o : MemOrder) (l : Loc) (t : ℕ) :
    writeView o l t ≤ (writeTView 𝓥 o l t).cur := le_sup_right

@[simp] theorem writeTView_cur_ne (𝓥 : TView Loc) (o : MemOrder) {l l' : Loc} (t : ℕ)
    (h : l' ≠ l) : (writeTView 𝓥 o l t).cur l' = 𝓥.cur l' := by
  simp [writeTView, h]

theorem writeTView_cur_w (𝓥 : TView Loc) (o : MemOrder) (l : Loc) {t : ℕ}
    (h : (𝓥.cur l).w < t) : ((writeTView 𝓥 o l t).cur l).w = t := by
  show max (𝓥.cur l).w (writeView o l t l).w = t
  rw [writeView_w]; omega

/-- The message view of an atomic release write contains the writer's current
view. -/
theorem writeRw_rel {𝓥 : TView Loc} {o : MemOrder} {l : Loc} {t : ℕ} {Rr : View Loc}
    (h : MemOrder.acqrel ≤ o) :
    𝓥.cur ≤ (writeRw 𝓥 o l t Rr).getD ⊥ := by
  have h' : MemOrder.rlx ≤ o := by revert h; cases o <;> decide
  simp only [writeRw, h', h, if_true, Option.getD_some]
  exact le_sup_left.trans (le_sup_left.trans le_sup_left)

/-! ## The race detector -/

@[simp] theorem addARead_self (𝓝 : View Loc) (l : Loc) (r : ℕ) :
    addARead 𝓝 l r l = { 𝓝 l with ar := insert r (𝓝 l).ar } := by
  simp [addARead]

@[simp] theorem addARead_ne (𝓝 : View Loc) {l l' : Loc} (r : ℕ) (h : l' ≠ l) :
    addARead 𝓝 l r l' = 𝓝 l' := by
  simp [addARead, h]

@[simp] theorem addNRead_self (𝓝 : View Loc) (l : Loc) (r : ℕ) :
    addNRead 𝓝 l r l = { 𝓝 l with nr := insert r (𝓝 l).nr } := by
  simp [addNRead]

@[simp] theorem addNRead_ne (𝓝 : View Loc) {l l' : Loc} (r : ℕ) (h : l' ≠ l) :
    addNRead 𝓝 l r l' = 𝓝 l' := by
  simp [addNRead, h]

@[simp] theorem addAWrite_self (𝓝 : View Loc) (l : Loc) (w : ℕ) :
    addAWrite 𝓝 l w l = { 𝓝 l with aw := insert w (𝓝 l).aw } := by
  simp [addAWrite]

@[simp] theorem addAWrite_ne (𝓝 : View Loc) {l l' : Loc} (w : ℕ) (h : l' ≠ l) :
    addAWrite 𝓝 l w l' = 𝓝 l' := by
  simp [addAWrite, h]

@[simp] theorem setWriteTime_self (𝓝 : View Loc) (l : Loc) (t : ℕ) :
    setWriteTime 𝓝 l t l = { 𝓝 l with w := t } := by
  simp [setWriteTime]

@[simp] theorem setWriteTime_ne (𝓝 : View Loc) {l l' : Loc} (t : ℕ) (h : l' ≠ l) :
    setWriteTime 𝓝 l t l' = 𝓝 l' := by
  simp [setWriteTime, h]

/-! ## Memory -/

@[simp] theorem Memory.add_self (M : Memory Loc Val) (l : Loc) (m : Msg Loc Val) :
    M.add l m l = m :: M l := by
  simp [Memory.add]

@[simp] theorem Memory.add_ne (M : Memory Loc Val) {l l' : Loc} (m : Msg Loc Val)
    (h : l' ≠ l) : M.add l m l' = M l' := by
  simp [Memory.add, h]

theorem Memory.mem_add {M : Memory Loc Val} {l l' : Loc} {m m' : Msg Loc Val} :
    m' ∈ M.add l m l' ↔ (l' = l ∧ m' = m) ∨ m' ∈ M l' := by
  by_cases h : l' = l
  · subst h; simp
  · simp [h]

theorem Memory.mem_add_of_mem {M : Memory Loc Val} {l l' : Loc} {m m' : Msg Loc Val}
    (h : m' ∈ M l') : m' ∈ M.add l m l' :=
  Memory.mem_add.2 (Or.inr h)

/-! ## Inversion of thread steps -/

section Inversion

variable {S : Type} {prog : S → Instr Loc Val S} {s s' : S} {𝓥 𝓥' : TView Loc}
  {M M' : Memory Loc Val} {𝓝 𝓝' : View Loc}

theorem MachineStep.read_inv {l : Loc} {v : Option Val} {o : MemOrder} {ot : Option ℕ}
    {ms : List (Loc × Msg Loc Val)} (h : MachineStep 𝓥 M (.read l v o) ot ms 𝓥' M') :
    ∃ m tr, v = m.val ∧ ot = some tr ∧ ms = [] ∧ M' = M ∧ ReadStep 𝓥 M tr l m o 𝓥' := by
  cases h with
  | read _ m _ _ tr READ => exact ⟨m, tr, rfl, rfl, rfl, rfl, READ⟩

theorem MachineStep.write_inv {l : Loc} {v : Val} {o : MemOrder} {ot : Option ℕ}
    {ms : List (Loc × Msg Loc Val)} (h : MachineStep 𝓥 M (.write l v o) ot ms 𝓥' M') :
    ∃ m, ot = none ∧ ms = [(l, m)] ∧ m.val = some v ∧ WriteStep 𝓥 M l m o ⊥ 𝓥' M' := by
  cases h with
  | write _ m _ _ _ _ ISVAL WRITE => exact ⟨m, rfl, rfl, ISVAL, WRITE⟩

theorem MachineStep.update_inv {l : Loc} {vr vw : Val} {or ow : MemOrder} {ot : Option ℕ}
    {ms : List (Loc × Msg Loc Val)}
    (h : MachineStep 𝓥 M (.update l vr vw or ow) ot ms 𝓥' M') :
    ∃ m1 m2 𝓥2 tr, ot = some tr ∧ ms = [(l, m2)] ∧ m1.val = some vr ∧ m2.val = some vw ∧
      m2.time = m1.time + 1 ∧ ReadStep 𝓥 M tr l m1 or 𝓥2 ∧
      WriteStep 𝓥2 M l m2 ow (m1.view.getD ⊥) 𝓥' M' := by
  cases h with
  | update _ m1 m2 _ _ 𝓥2 _ _ tr _ _ ISV1 ISV2 ADJ READ WRITE =>
    exact ⟨m1, m2, 𝓥2, tr, rfl, rfl, ISV1, ISV2, ADJ, READ, WRITE⟩

theorem DrfPost.read_inv {l : Loc} {v : Option Val} {o : MemOrder} {ot : Option ℕ}
    {ms : List (Loc × Msg Loc Val)} (h : DrfPost 𝓝 (.read l v o) ot ms 𝓝') :
    ∃ tr, ot = some tr ∧ DrfPostRead l o tr 𝓝 𝓝' := by
  cases h with
  | read _ tr _ _ _ DRF => exact ⟨tr, rfl, DRF⟩

theorem DrfPost.write_inv {l : Loc} {v : Val} {o : MemOrder} {ot : Option ℕ}
    {ms : List (Loc × Msg Loc Val)} (h : DrfPost 𝓝 (.write l v o) ot ms 𝓝') :
    ∃ m, ms = [(l, m)] ∧ DrfPostWrite l m.time o 𝓝 𝓝' := by
  cases h with
  | write _ m _ _ _ DRF => exact ⟨m, rfl, DRF⟩

theorem DrfPost.update_inv {l : Loc} {vr vw : Val} {or ow : MemOrder} {ot : Option ℕ}
    {ms : List (Loc × Msg Loc Val)} (h : DrfPost 𝓝 (.update l vr vw or ow) ot ms 𝓝') :
    ∃ m tr, ot = some tr ∧ ms = [(l, m)] ∧ DrfPostUpdate l tr m.time 𝓝 𝓝' := by
  cases h with
  | update _ m _ _ tr _ _ _ DRF => exact ⟨m, tr, rfl, rfl, DRF⟩

/-- A read step, spelled out. -/
theorem TStep.read_inv {l : Loc} {o : MemOrder} {k : Option Val → S}
    (hp : prog s = .read l o k) (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') :
    ∃ m ∈ M l, ∃ tr, (𝓥.cur l).w ≤ m.time ∧ ((m.view.getD ⊥) l).w ≤ m.time ∧
      DrfPreRead l 𝓝 𝓥 M o ∧ s' = k m.val ∧
      𝓥' = readTView 𝓥 o (m.view.getD ⊥) (readView o l m.time tr) ∧ M' = M ∧
      DrfPostRead l o tr 𝓝 𝓝' := by
  cases h with
  | read INSTR DRFPre PStep DRFPost =>
    rw [hp] at INSTR; cases INSTR
    obtain ⟨m', tr, hv, hot, -, hM, READ⟩ := PStep.read_inv
    obtain ⟨tr', hot', DRF⟩ := DRFPost.read_inv
    rw [hot] at hot'; cases hot'
    obtain ⟨⟨pln, pln2, eq⟩, mem⟩ := READ
    refine ⟨m', mem, tr, pln, pln2, DRFPre, by rw [hv], eq, hM, DRF⟩
  | write INSTR => rw [hp] at INSTR; cases INSTR
  | update INSTR => rw [hp] at INSTR; cases INSTR
  | choose _ INSTR => rw [hp] at INSTR; cases INSTR

/-- A write step, spelled out. -/
theorem TStep.write_inv {l : Loc} {o : MemOrder} {v : Val} {k : S}
    (hp : prog s = .write l o v k) (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') :
    ∃ t, (∀ m ∈ M l, m.time ≠ t) ∧ (𝓥.cur l).w < t ∧ DrfPreWrite l 𝓝 𝓥 M o ∧
      s' = k ∧ 𝓥' = writeTView 𝓥 o l t ∧
      M' = M.add l ⟨t, some v, writeRw 𝓥 o l t ⊥⟩ ∧
      View.ClosedOpt (writeRw 𝓥 o l t ⊥) M' ∧
      DrfPostWrite l t o 𝓝 𝓝' := by
  cases h with
  | read INSTR => rw [hp] at INSTR; cases INSTR
  | write INSTR DRFPre PStep DRFPost =>
    rw [hp] at INSTR; cases INSTR
    rename_i m
    obtain ⟨m', -, hms, hval, ⟨⟨fresh, eq, _, closed, _, _⟩, ⟨rlx, eqRw, eqV⟩⟩⟩ :=
      PStep.write_inv
    obtain ⟨m'', hms', DRF⟩ := DRFPost.write_inv
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hms hms'
    subst hms hms'
    refine ⟨m.time, fresh, rlx, DRFPre, rfl, eqV, ?_, ?_, DRF⟩
    · rw [eq]; congr 1; cases m; simp_all
    · rw [← eqRw]; exact closed
  | update INSTR => rw [hp] at INSTR; cases INSTR
  | choose _ INSTR => rw [hp] at INSTR; cases INSTR

/-- An update step, spelled out. -/
theorem TStep.update_inv {l : Loc} {or ow : MemOrder} {f : Val → Val} {k : Val → S}
    (hp : prog s = .update l or ow f k) (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') :
    ∃ m1 ∈ M l, ∃ v tr, m1.val = some v ∧ (𝓥.cur l).w ≤ m1.time ∧
      ((m1.view.getD ⊥) l).w ≤ m1.time ∧
      (∀ m ∈ M l, m.time ≠ m1.time + 1) ∧
      DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow ∧ s' = k v ∧
      𝓥' = writeTView (readTView 𝓥 or (m1.view.getD ⊥) (readView or l m1.time tr))
        ow l (m1.time + 1) ∧
      M' = M.add l ⟨m1.time + 1, some (f v),
         writeRw (readTView 𝓥 or (m1.view.getD ⊥) (readView or l m1.time tr))
           ow l (m1.time + 1) (m1.view.getD ⊥)⟩ ∧
      View.ClosedOpt (writeRw (readTView 𝓥 or (m1.view.getD ⊥) (readView or l m1.time tr))
           ow l (m1.time + 1) (m1.view.getD ⊥)) M' ∧
      DrfPostUpdate l tr (m1.time + 1) 𝓝 𝓝' := by
  cases h with
  | read INSTR => rw [hp] at INSTR; cases INSTR
  | write INSTR => rw [hp] at INSTR; cases INSTR
  | update INSTR DRFPre PStep DRFPost =>
    rw [hp] at INSTR; cases INSTR
    rename_i v tr m
    obtain ⟨m1, m2, 𝓥2, tr', hot, hms, ISV1, ISV2, ADJ, READ, WRITE⟩ := PStep.update_inv
    obtain ⟨m', tr'', hot', hms', DRF⟩ := DRFPost.update_inv
    cases hot; cases hot'
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hms hms'
    subst hms hms'
    obtain ⟨⟨fresh, eq, _, closed, _, _⟩, ⟨_, eqRw, eqV⟩⟩ := WRITE
    obtain ⟨⟨pln, pln2, eq2⟩, mem⟩ := READ
    subst eq2
    refine ⟨m1, mem, v, tr, ISV1, pln, pln2, ?_, DRFPre.1, DRFPre.2, rfl, ?_, ?_, ?_, ?_⟩
    · rw [← ADJ]; exact fresh
    · rw [eqV, ADJ]
    · rw [eq]; congr 1; cases m; simp_all
    · rw [← ADJ, ← eqRw]; exact closed
    · rw [← ADJ]; exact DRF
  | choose _ INSTR => rw [hp] at INSTR; cases INSTR

/-- A choice step, spelled out. -/
theorem TStep.choose_inv {k : Bool → S}
    (hp : prog s = .choose k) (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') :
    ∃ b, s' = k b ∧ 𝓥' = 𝓥 ∧ M' = M ∧ 𝓝' = 𝓝 := by
  cases h with
  | read INSTR => rw [hp] at INSTR; cases INSTR
  | write INSTR => rw [hp] at INSTR; cases INSTR
  | update INSTR => rw [hp] at INSTR; cases INSTR
  | choose b INSTR => rw [hp] at INSTR; cases INSTR; exact ⟨b, rfl, rfl, rfl, rfl⟩

theorem TStep.halt_inv (hp : prog s = .halt) (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') : False := by
  cases h <;> simp_all

theorem TStep.fault_inv (hp : prog s = .fault) (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') : False := by
  cases h <;> simp_all

/-- Every thread step, in one of four shapes. -/
theorem TStep.cases' (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') :
    (∃ l m tr o, ReadStep 𝓥 M tr l m o 𝓥' ∧ M' = M) ∨
    (∃ l m o, WriteStep 𝓥 M l m o ⊥ 𝓥' M') ∨
    (∃ l m1 m2 or ow 𝓥2 tr, ReadStep 𝓥 M tr l m1 or 𝓥2 ∧ m2.time = m1.time + 1 ∧
      WriteStep 𝓥2 M l m2 ow (m1.view.getD ⊥) 𝓥' M') ∨
    (𝓥' = 𝓥 ∧ M' = M) := by
  cases h with
  | read _ _ PStep _ =>
    obtain ⟨m, tr, -, -, -, hM, R⟩ := PStep.read_inv
    exact Or.inl ⟨_, m, tr, _, R, hM⟩
  | write _ _ PStep _ =>
    obtain ⟨m, -, -, -, W⟩ := PStep.write_inv
    exact Or.inr (Or.inl ⟨_, m, _, W⟩)
  | update _ _ PStep _ =>
    obtain ⟨m1, m2, 𝓥2, tr, -, -, -, -, ADJ, R, W⟩ := PStep.update_inv
    exact Or.inr (Or.inr (Or.inl ⟨_, m1, m2, _, _, 𝓥2, tr, R, ADJ, W⟩))
  | choose => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- Thread steps only grow the current view. -/
theorem TStep.cur_le (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') : 𝓥.cur ≤ 𝓥'.cur := by
  rcases h.cases' with ⟨_, _, _, _, R, -⟩ | ⟨_, _, _, W⟩ | ⟨_, _, _, _, _, _, _, R, -, W⟩ | ⟨h, -⟩
  · rw [R.read.eq]; exact readTView_cur_le _ _ _ _
  · rw [W.wview.eq]; exact writeTView_cur_le _ _ _ _
  · rw [W.wview.eq]
    exact (R.read.eq ▸ readTView_cur_le _ _ _ _).trans (writeTView_cur_le _ _ _ _)
  · rw [h]

/-- A step writes at most one message, at a fresh positive time. -/
theorem TStep.mem_cases (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') :
    M' = M ∨ ∃ l m, (∀ m' ∈ M l, m'.time ≠ m.time) ∧ 1 ≤ m.time ∧ M' = M.add l m := by
  rcases h.cases' with ⟨_, _, _, _, _, hM⟩ | ⟨l, m, _, W⟩ | ⟨l, _, m, _, _, _, _, _, ADJ, W⟩ | ⟨-, hM⟩
  · exact Or.inl hM
  · refine Or.inr ⟨l, m, W.write.fresh, ?_, W.write.eq⟩
    have := W.wview.rlx; omega
  · exact Or.inr ⟨l, m, W.write.fresh, by omega, W.write.eq⟩
  · exact Or.inl hM

/-- Memory only grows. -/
theorem TStep.mem_sub (h : TStep prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝') :
    ∀ l, ∀ m ∈ M l, m ∈ M' l := by
  rcases h.mem_cases with rfl | ⟨_, _, _, _, rfl⟩
  · exact fun _ _ h => h
  · exact fun _ _ h => Memory.mem_add_of_mem h

end Inversion

/-! ## Program-independent invariants -/

section Pool

variable {ι : Type} [DecidableEq ι] {S : ι → Type}
  {prog : (i : ι) → S i → Instr Loc Val (S i)}

/-- Invariants of every ORC11 run: messages have distinct, positive times per
location, and every thread has seen the initialization of every location. -/
structure GenInv (c : Config ι S Loc Val) : Prop where
  uniq : ∀ l, ∀ m ∈ c.mem l, ∀ m' ∈ c.mem l, m.time = m'.time → m = m'
  pos : ∀ l, ∀ m ∈ c.mem l, 1 ≤ m.time
  cur : ∀ i l, 1 ≤ ((c.th i).2.cur l).w

omit [DecidableEq ι] in
theorem genInv_init (s0 : (i : ι) → S i) (v0 : Loc → Option Val) :
    GenInv (initConfig s0 v0) where
  uniq l m hm m' hm' _ := by
    simp only [initConfig, List.mem_singleton] at hm hm'; rw [hm, hm']
  pos l m hm := by simp only [initConfig, List.mem_singleton] at hm; rw [hm]
  cur i l := by simp [initConfig, initTView, initTime]

theorem genInv_step {c c' : Config ι S Loc Val} (h : GenInv c) (hs : Step prog c c') :
    GenInv c' := by
  cases hs with
  | mk i hst =>
    refine ⟨?_, ?_, ?_⟩
    · rcases hst.mem_cases with hM | ⟨l0, m0, hfresh, _, hM⟩
      · simp only [hM]; exact h.uniq
      · simp only [hM]
        intro l m hm m' hm' ht
        rcases Memory.mem_add.1 hm with ⟨rfl, rfl⟩ | h1 <;>
          rcases Memory.mem_add.1 hm' with ⟨hl, rfl⟩ | h2
        · rfl
        · exact absurd ht.symm (hfresh m' h2)
        · subst hl; exact absurd ht (hfresh m h1)
        · exact h.uniq l m h1 m' h2 ht
    · rcases hst.mem_cases with hM | ⟨l0, m0, _, hpos, hM⟩
      · simp only [hM]; exact h.pos
      · simp only [hM]
        intro l m hm
        rcases Memory.mem_add.1 hm with ⟨rfl, rfl⟩ | h1
        · exact hpos
        · exact h.pos l m h1
    · intro j l
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]
        exact (h.cur j l).trans (hst.cur_le l).1
      · simp only [Function.update_of_ne hj]; exact h.cur j l

theorem Reachable.genInv {s0 : (i : ι) → S i} {v0 : Loc → Option Val}
    {c : Config ι S Loc Val} (h : Reachable prog s0 v0 c) : GenInv c := by
  induction h with
  | refl => exact genInv_init s0 v0
  | tail _ hs ih => exact genInv_step ih hs

end Pool

end ORC11
