import ORC11.Wf

/-!
# ORC11: thread steps at a chosen message or time

Constructors for thread steps that read a given message and write at a given
time, for replaying executions of the declarative model.
-/

namespace ORC11

variable {Loc Val : Type} [DecidableEq Loc] {S : Type} {prog : S → Instr Loc Val S}
  {s : S} {𝓥 : TView Loc} {M : Memory Loc Val} {𝓝 : View Loc}

/-- Read message `m`, with read id `tr`. -/
theorem TStep.read_at {l : Loc} {o : MemOrder} {k : Option Val → S}
    (hM : MemWf M) (hp : prog s = .read l o k) (hdrf : DrfPreRead l 𝓝 𝓥 M o)
    {m : Msg Loc Val} (hm : m ∈ M l) (hle : (𝓥.cur l).w ≤ m.time) {tr : ℕ}
    (htr : tr ∉ (𝓝 l).ar ∧ tr ∉ (𝓝 l).nr) :
    TStep prog s 𝓥 M 𝓝 (k m.val) (readTView 𝓥 o (m.view.getD ⊥) (readView o l m.time tr)) M
      (if MemOrder.rlx ≤ o then addARead 𝓝 l tr else addNRead 𝓝 l tr) := by
  refine .read hp hdrf (.read l m o _ tr ⟨⟨hle, (hM.msgWf l m hm).getD_le, rfl⟩, hm⟩)
    (.read l tr o _ _ ?_)
  by_cases ho : MemOrder.rlx ≤ o
  · simp only [DrfPostRead, ho, ↓reduceIte, true_and]; exact htr.1
  · simp only [DrfPostRead, ho, ↓reduceIte, true_and]; exact htr.2

/-- Write `v` at time `t`. -/
theorem TStep.write_at {l : Loc} {o : MemOrder} {v : Val} {k : S}
    (hT : ThreadWf 𝓥 M) (hp : prog s = .write l o v k) (hdrf : DrfPreWrite l 𝓝 𝓥 M o)
    {t : ℕ} (hfresh : ∀ m ∈ M l, m.time ≠ t) (hlt : (𝓥.cur l).w < t)
    (hlall : ∃ m ∈ M l, m.time ≤ t) :
    TStep prog s 𝓥 M 𝓝 k (writeTView 𝓥 o l t) (M.add l ⟨t, some v, writeRw 𝓥 o l t ⊥⟩)
      (if MemOrder.rlx ≤ o then addAWrite 𝓝 l t else setWriteTime 𝓝 l t) := by
  let m : Msg Loc Val := ⟨t, some v, writeRw 𝓥 o l t ⊥⟩
  have hsub : ∀ l', ∀ m' ∈ M l', m' ∈ M.add l m l' := fun _ _ => Memory.mem_add_of_mem
  have MW : MemoryWrite M l m (M.add l m) :=
    { fresh := hfresh
      eq := rfl
      wf := writeRw_wf ((TimeInfo.w_mono (hT.wf.1 l)).trans hlt.le) hlt.le (by simp)
      closed := writeRw_closed (hT.rel.mono hsub) (hT.cur.mono hsub)
        (writeView_closed ⟨m, by simp, le_rfl⟩) (View.closed_bot _)
      isval := rfl
      lall := hlall }
  refine .write hp hdrf (.write l m o _ _ v rfl ⟨MW, ⟨hlt, rfl, rfl⟩⟩) (.write l m v o _ ?_)
  by_cases ho : MemOrder.rlx ≤ o <;> simp [DrfPostWrite, ho, m]

/-- Update message `m1`, writing right after it, with read id `tr`. -/
theorem TStep.update_at {l : Loc} {or ow : MemOrder} {f : Val → Val} {k : Val → S}
    (hT : ThreadWf 𝓥 M) (hM : MemWf M) (hp : prog s = .update l or ow f k)
    (hdrf : DrfPreRead l 𝓝 𝓥 M or ∧ DrfPreWrite l 𝓝 𝓥 M ow)
    {m1 : Msg Loc Val} {v : Val} (hmem : m1 ∈ M l) (hv : m1.val = some v)
    (hcurl : (𝓥.cur l).w ≤ m1.time) (hfresh : ∀ m ∈ M l, m.time ≠ m1.time + 1)
    {tr : ℕ} (htr : tr ∉ (𝓝 l).ar) :
    TStep prog s 𝓥 M 𝓝 (k v)
      (writeTView (readTView 𝓥 or (m1.view.getD ⊥) (readView or l m1.time tr)) ow l
        (m1.time + 1))
      (M.add l ⟨m1.time + 1, some (f v),
        writeRw (readTView 𝓥 or (m1.view.getD ⊥) (readView or l m1.time tr)) ow l
          (m1.time + 1) (m1.view.getD ⊥)⟩)
      (addAWrite (addARead 𝓝 l tr) l (m1.time + 1)) := by
  have hRl := (hM.msgWf l m1 hmem).getD_le
  have hRcl := (hM.msgClosed l m1 hmem).getD
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
  let m2 : Msg Loc Val := ⟨t, some (f v), writeRw 𝓥2 ow l t R⟩
  have hsub : ∀ l', ∀ m' ∈ M l', m' ∈ M.add l m2 l' := fun _ _ => Memory.mem_add_of_mem
  have MW : MemoryWrite M l m2 (M.add l m2) :=
    { fresh := hfresh
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
    (.update l m2 or ow tr v (f v) _ ⟨rfl, htr⟩)

/-- Take branch `b` of a choice. -/
theorem TStep.choose_at {k : Bool → S} (hp : prog s = .choose k) (b : Bool) :
    TStep prog s 𝓥 M 𝓝 (k b) 𝓥 M 𝓝 :=
  .choose b hp

end ORC11
