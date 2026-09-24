import ORC11.Wf

/-!
# ORC11: an executable interpreter for latest steps

`stepL?` computes the latest step of a thread (the read reads the latest
message; the write goes at `maxTime + 1`; read ids are `sup + 1`), or `none` if
`drf_pre` fails. `run?` runs a schedule. Both are sound: whatever they compute
is a run of `StepL`, hence of `Step` (`run?_reachable`). Concrete schedules can
then be checked by evaluation in the kernel (`decide`), which gives explicit,
checked counterexample executions.
-/

namespace ORC11

variable {Loc Val : Type} [DecidableEq Loc]

/-! ## Decidability of the race detector's preconditions -/

instance (l : Loc) (𝓝 : View Loc) (𝓥 : TView Loc) (M : Memory Loc Val) (o : MemOrder) :
    Decidable (DrfPreRead l 𝓝 𝓥 M o) :=
  decidable_of_iff ((𝓝 l).w ≤ (𝓥.cur l).w ∧ (¬ MemOrder.rlx ≤ o →
      (∀ m ∈ M l, m.time ≤ (𝓥.cur l).w) ∧ (𝓝 l).aw ⊆ (𝓥.cur l).aw))
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.writeNA, h.allW⟩⟩

instance (l : Loc) (𝓝 : View Loc) (𝓥 : TView Loc) (M : Memory Loc Val) (o : MemOrder) :
    Decidable (DrfPreWrite l 𝓝 𝓥 M o) :=
  decidable_of_iff ((𝓝 l).nr ⊆ (𝓥.cur l).nr ∧ (𝓝 l).w ≤ (𝓥.cur l).w ∧
      (¬ MemOrder.rlx ≤ o → (∀ m ∈ M l, m.time ≤ (𝓥.cur l).w) ∧
        (𝓝 l).aw ⊆ (𝓥.cur l).aw ∧ (𝓝 l).ar ⊆ (𝓥.cur l).ar))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.readNA, h.allW, h.writeNA⟩⟩

instance {S : Type} (𝓝 : View Loc) (𝓥 : TView Loc) (M : Memory Loc Val) :
    (i : Instr Loc Val S) → Decidable (i.DrfPreOk 𝓝 𝓥 M)
  | .read l o _ => inferInstanceAs (Decidable (DrfPreRead l 𝓝 𝓥 M o))
  | .write l o _ _ => inferInstanceAs (Decidable (DrfPreWrite l 𝓝 𝓥 M o))
  | .update l or ow _ _ =>
    inferInstanceAs (Decidable (DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow))
  | .choose _ => isTrue trivial
  | .halt => isTrue trivial
  | .fault => isTrue trivial

/-! ## Latest messages and fresh ids -/

section Aux

omit [DecidableEq Loc]

/-- The latest message of a cell. -/
def latestMsg : List (Msg Loc Val) → Option (Msg Loc Val)
  | [] => none
  | m :: C => match latestMsg C with
    | none => some m
    | some m' => if m'.time ≤ m.time then some m else some m'

theorem latestMsg_cons_ne_none (b : Msg Loc Val) (C : List (Msg Loc Val)) :
    latestMsg (b :: C) ≠ none := by
  unfold latestMsg
  cases latestMsg C with
  | none => simp
  | some m' => simp only; split <;> simp

theorem latestMsg_isLatest : ∀ {C : List (Msg Loc Val)} {m : Msg Loc Val},
    latestMsg C = some m → IsLatest C m
  | [], _, h => by simp [latestMsg] at h
  | a :: C, m, h => by
    unfold latestMsg at h
    cases hC : latestMsg C with
    | none =>
      rw [hC] at h; cases h
      have : C = [] := by
        cases C with
        | nil => rfl
        | cons b C' => exact absurd hC (latestMsg_cons_ne_none b C')
      subst this
      exact ⟨List.mem_singleton_self _, fun m' hm' => by
        rw [List.mem_singleton] at hm'; rw [hm']⟩
    | some m' =>
      rw [hC] at h
      have ih := latestMsg_isLatest hC
      simp only at h
      split at h
      · cases h
        exact ⟨List.mem_cons_self, fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact le_rfl
          · exact (ih.2 x hx).trans (by omega)⟩
      · cases h
        exact ⟨List.mem_cons_of_mem _ ih.1, fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · omega
          · exact ih.2 x hx⟩

/-- A read id not in `s`. -/
def freshId (s : Finset ℕ) : ℕ := s.sup id + 1

theorem freshId_not_mem (s : Finset ℕ) : freshId s ∉ s := fun h => by
  have := Finset.le_sup (f := id) h
  change freshId s ≤ s.sup id at this
  unfold freshId at this; omega

end Aux

/-! ## One latest step -/

/-- The latest step of a thread at local state `s`; `b` resolves a choice. -/
def stepL? {S : Type} (prog : S → Instr Loc Val S) (s : S) (𝓥 : TView Loc)
    (M : Memory Loc Val) (𝓝 : View Loc) (b : Bool) :
    Option (S × TView Loc × Memory Loc Val × View Loc) :=
  match prog s with
  | .read l o k =>
    if DrfPreRead l 𝓝 𝓥 M o then
      match latestMsg (M l) with
      | none => none
      | some m =>
        let tr := freshId ((𝓝 l).ar ∪ (𝓝 l).nr)
        some (k m.val, readTView 𝓥 o (m.view.getD ⊥) (readView o l m.time tr), M,
          if MemOrder.rlx ≤ o then addARead 𝓝 l tr else addNRead 𝓝 l tr)
    else none
  | .write l o v k =>
    if DrfPreWrite l 𝓝 𝓥 M o then
      let t := maxTime (M l) + 1
      some (k, writeTView 𝓥 o l t, M.add l ⟨t, some v, writeRw 𝓥 o l t ⊥⟩,
        if MemOrder.rlx ≤ o then addAWrite 𝓝 l t else setWriteTime 𝓝 l t)
    else none
  | .update l or ow f k =>
    if DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow then
      match latestMsg (M l) with
      | none => none
      | some m1 =>
        match m1.val with
        | none => none
        | some v =>
          let tr := freshId (𝓝 l).ar
          let t := m1.time + 1
          let 𝓥2 := readTView 𝓥 or (m1.view.getD ⊥) (readView or l m1.time tr)
          some (k v, writeTView 𝓥2 ow l t,
            M.add l ⟨t, some (f v), writeRw 𝓥2 ow l t (m1.view.getD ⊥)⟩,
            addAWrite (addARead 𝓝 l tr) l t)
    else none
  | .choose k => some (k b, 𝓥, M, 𝓝)
  | .halt => none
  | .fault => none

theorem stepL?_sound {S : Type} {prog : S → Instr Loc Val S} {s s' : S}
    {𝓥 𝓥' : TView Loc} {M M' : Memory Loc Val} {𝓝 𝓝' : View Loc} {b : Bool}
    (hT : ThreadWf 𝓥 M) (hM : MemWf M)
    (h : stepL? prog s 𝓥 M 𝓝 b = some (s', 𝓥', M', 𝓝')) :
    TStepL prog s 𝓥 M 𝓝 s' 𝓥' M' 𝓝' := by
  unfold stepL? at h
  cases hp : prog s with
  | read l o k =>
    rw [hp] at h; simp only at h
    split at h
    · rename_i hdrf
      cases hm : latestMsg (M l) with
      | none => rw [hm] at h; cases h
      | some m =>
        rw [hm] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have hl := latestMsg_isLatest hm
        refine .read hp hdrf (.read l m o _ _
          ⟨⟨cur_w_le_latest hT.cur hl, (hM.msgWf l m hl.1).getD_le, rfl⟩, hl.1⟩)
          (.read l _ o _ _ ?_) hl
        have hfr := freshId_not_mem ((𝓝 l).ar ∪ (𝓝 l).nr)
        by_cases ho : MemOrder.rlx ≤ o
        · simp only [DrfPostRead, ho, ↓reduceIte, true_and]
          exact fun h => hfr (Finset.mem_union_left _ h)
        · simp only [DrfPostRead, ho, ↓reduceIte, true_and]
          exact fun h => hfr (Finset.mem_union_right _ h)
    · cases h
  | write l o v k =>
    rw [hp] at h; simp only at h
    split at h
    · rename_i hdrf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hlt : ∀ m' ∈ M l, m'.time < maxTime (M l) + 1 :=
        fun m' h => Nat.lt_succ_of_le (le_maxTime h)
      have hcurlt : (𝓥.cur l).w < maxTime (M l) + 1 := by
        rcases hT.cur l with h0 | ⟨m', hm', hle⟩
        · omega
        · exact lt_of_le_of_lt hle (hlt m' hm')
      obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil _ (hM.nonempty l)
      let t := maxTime (M l) + 1
      let m : Msg Loc Val := ⟨t, some v, writeRw 𝓥 o l t ⊥⟩
      have hsub : ∀ l', ∀ m' ∈ M l', m' ∈ M.add l m l' := fun _ _ => Memory.mem_add_of_mem
      have MW : MemoryWrite M l m (M.add l m) :=
        { fresh := fun m' h => (hlt m' h).ne
          eq := rfl
          wf := writeRw_wf ((TimeInfo.w_mono (hT.wf.1 l)).trans hcurlt.le) hcurlt.le
            (by simp)
          closed := writeRw_closed (hT.rel.mono hsub) (hT.cur.mono hsub)
            (writeView_closed ⟨m, by simp, le_rfl⟩) (View.closed_bot _)
          isval := rfl
          lall := ⟨m0, hm0, (hlt m0 hm0).le⟩ }
      refine .write hp hdrf (.write l m o _ _ v rfl ⟨MW, ⟨hcurlt, rfl, rfl⟩⟩)
        (.write l m v o _ ?_) hlt
      by_cases ho : MemOrder.rlx ≤ o <;> simp [DrfPostWrite, ho, m, t]
    · cases h
  | update l or ow f k =>
    rw [hp] at h; simp only at h
    split at h
    · rename_i hdrf
      cases hm : latestMsg (M l) with
      | none => rw [hm] at h; cases h
      | some m1 =>
        rw [hm] at h; simp only at h
        cases hv : m1.val with
        | none => rw [hv] at h; cases h
        | some v =>
          rw [hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have hm1 := latestMsg_isLatest hm
          have htr := freshId_not_mem (𝓝 l).ar
          have hmem := hm1.1
          have hcurl := cur_w_le_latest hT.cur hm1
          have hRl := (hM.msgWf l m1 hmem).getD_le
          have hRcl := (hM.msgClosed l m1 hmem).getD
          let tr := freshId (𝓝 l).ar
          let t := m1.time + 1
          let R := m1.view.getD ⊥
          let 𝓥2 := readTView 𝓥 or R (readView or l m1.time tr)
          have h2cur : (𝓥2.cur l).w ≤ m1.time := by
            have h := TimeInfo.w_mono (readTView_cur_le_sup 𝓥 or (m1.view.getD ⊥)
              (readView or l m1.time tr) l)
            simp only [View.sup_apply', TimeInfo.sup_w, readView_w] at h
            exact h.trans (by omega)
          have h2rel : (𝓥2.rel l).w ≤ m1.time := (TimeInfo.w_mono (hT.wf.1 l)).trans hcurl
          have h2curcl : 𝓥2.cur.Closed M :=
            readTView_cur_closed hT.cur hRcl (readView_closed ⟨m1, hmem, le_rfl⟩)
          have hlt : ∀ m' ∈ M l, m'.time < t := fun m' h => Nat.lt_succ_of_le (hm1.2 m' h)
          let m2 : Msg Loc Val := ⟨t, some (f v), writeRw 𝓥2 ow l t R⟩
          have hsub : ∀ l', ∀ m' ∈ M l', m' ∈ M.add l m2 l' :=
            fun _ _ => Memory.mem_add_of_mem
          have MW : MemoryWrite M l m2 (M.add l m2) :=
            { fresh := fun m' h => (hlt m' h).ne
              eq := rfl
              wf := writeRw_wf (Nat.le_succ_of_le h2rel) (Nat.le_succ_of_le h2cur)
                (Nat.le_succ_of_le hRl)
              closed := writeRw_closed (hT.rel.mono hsub) (h2curcl.mono hsub)
                (writeView_closed ⟨m2, by simp, le_rfl⟩) (hRcl.mono hsub)
              isval := rfl
              lall := ⟨m1, hmem, Nat.le_succ _⟩ }
          exact .update hp hdrf
            (.update l m1 m2 or ow 𝓥2 _ _ tr v (f v) hv rfl rfl
              ⟨⟨hcurl, hRl, rfl⟩, hmem⟩ ⟨MW, ⟨Nat.lt_succ_of_le h2cur, rfl, rfl⟩⟩)
            (.update l m2 or ow tr v (f v) _ ⟨rfl, htr⟩) hlt
    · cases h
  | choose k =>
    rw [hp] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .choose b hp
  | halt => rw [hp] at h; cases h
  | fault => rw [hp] at h; cases h

/-! ## Schedules -/

section Pool

variable {ι : Type} [DecidableEq ι] {S : ι → Type}
  (prog : (i : ι) → S i → Instr Loc Val (S i))

/-- The latest step of thread `i` in configuration `c`. -/
def stepThread? (c : Config ι S Loc Val) (i : ι) (b : Bool) : Option (Config ι S Loc Val) :=
  (stepL? (prog i) (c.th i).1 (c.th i).2 c.mem c.na b).map fun x =>
    ⟨Function.update c.th i (x.1, x.2.1), x.2.2.1, x.2.2.2⟩

/-- Run a schedule: a list of threads, each with the branch of its choice. -/
def run? : Config ι S Loc Val → List (ι × Bool) → Option (Config ι S Loc Val)
  | c, [] => some c
  | c, (i, b) :: l => (stepThread? prog c i b).bind fun c' => run? c' l

variable {prog}

theorem stepThread?_sound {c c' : Config ι S Loc Val} {i : ι} {b : Bool} (hw : WfInv c)
    (h : stepThread? prog c i b = some c') : StepL prog c c' := by
  unfold stepThread? at h
  cases hs : stepL? (prog i) (c.th i).1 (c.th i).2 c.mem c.na b with
  | none => rw [hs] at h; cases h
  | some x =>
    rw [hs] at h; simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨s', 𝓥', M', 𝓝'⟩ := x
    exact StepL.of_tstepL (stepL?_sound (hw.threadWf i) hw.memWf hs)

theorem run?_reachable {s0 : (i : ι) → S i} {v0 : Loc → Option Val} :
    ∀ {c c' : Config ι S Loc Val} {l : List (ι × Bool)}, Reachable prog s0 v0 c →
      run? prog c l = some c' → Reachable prog s0 v0 c'
  | c, c', [], hr, h => by simp only [run?, Option.some.injEq] at h; exact h ▸ hr
  | c, c', (i, b) :: l, hr, h => by
    simp only [run?] at h
    cases hs : stepThread? prog c i b with
    | none => rw [hs] at h; cases h
    | some c1 =>
      rw [hs] at h
      exact run?_reachable (hr.tail (stepThread?_sound hr.wfInv hs).toStep) h

/-- A schedule leading to a configuration in which thread `i`'s next access
races. -/
theorem racy_of_run {s0 : (i : ι) → S i} {v0 : Loc → Option Val} {l : List (ι × Bool)}
    {i : ι}
    (h : (run? prog (initConfig s0 v0) l).any
      (fun c => !decide ((prog i (c.th i).1).DrfPreOk c.na (c.th i).2 c.mem)) = true) :
    ∃ c, Reachable prog s0 v0 c ∧ Racy prog c := by
  cases hc : run? prog (initConfig s0 v0) l with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    simp only [Option.any_some, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at h
    exact ⟨c, run?_reachable .refl hc, i, h⟩

/-- A schedule leading to a configuration in which thread `i` is at a fault. -/
theorem faulty_of_run {s0 : (i : ι) → S i} {v0 : Loc → Option Val} {l : List (ι × Bool)}
    {i : ι} [∀ c : Config ι S Loc Val, Decidable (prog i (c.th i).1 = .fault)]
    (h : (run? prog (initConfig s0 v0) l).any
      (fun c => decide (prog i (c.th i).1 = .fault)) = true) :
    ∃ c, Reachable prog s0 v0 c ∧ Faulty prog c := by
  cases hc : run? prog (initConfig s0 v0) l with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    simp only [Option.any_some, decide_eq_true_eq] at h
    exact ⟨c, run?_reachable .refl hc, i, h⟩

end Pool

end ORC11
