import Mempipe.Frame

/-!
# Sender steps preserve the invariant
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ)

@[simp] theorem consumed_setS {c : Cfg ρ} {σ : SState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc} {v : ℤ} : Consumed (c.setS σ 𝓥 M' 𝓝') v ↔ Consumed c v := by
  simp [Consumed]

/-- The frame conditions for a sender step and a buffer it does not touch. -/
theorem Frame.sender {c : Cfg ρ} {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    {i : ℕ}
    (hown : M' (.own i) = c.mem (.own i)) (hlen : M' (.len i) = c.mem (.len i))
    (hcseq : M' (.cseq i) = c.mem (.cseq i)) (hchunk : M' (.chunk i) = c.mem (.chunk i))
    (hna : (𝓝' (.chunk i)).nr = (c.na (.chunk i)).nr) (hv : c.vs ≤ 𝓥.cur)
    (hfill : σ.pc.fill = some i ↔ c.s.pc.fill = some i)
    (hseal : σ.pc.sealing = some i ↔ c.s.pc.sealing = some i)
    (hpc : σ.pc.fill = some i ∨ σ.pc.sealing = some i → σ.pc = c.s.pc)
    (hnpub : c.s.pc.npub ≤ σ.pc.npub) :
    Frame c (c.setS σ 𝓥 M' 𝓝') i where
  own := by simpa using hown
  len := by simpa using hlen
  cseq := by simpa using hcseq
  chunk := by simpa using hchunk
  na := by simpa using hna
  vs l := by simpa using hv l
  vr r l := by simp
  fill := by simpa using hfill
  sealing := by simpa using hseal
  pc := by simpa using hpc
  npub := by simpa using hnpub
  cons v h := by simpa using h
  on r h := by simp
  stay r h := by simp

theorem PhaseOK.sender_frame {c : Cfg ρ} {σ : SState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc} {i : ℕ} {ph : Phase} (h : PhaseOK pay ln c i ph)
    (F : Frame c (c.setS σ 𝓥 M' 𝓝') i) : PhaseOK pay ln (c.setS σ 𝓥 M' 𝓝') i ph :=
  h.frame pay ln F (fun _ _ r hr => by simpa using hr) (fun _ _ hc => by simpa using hc)

/-- Sender steps that do not write memory and keep the sender among
non-publishing states. -/
theorem Inv.sender_noWrite {c : Cfg ρ} (h : Inv pay ln c) {σ : SState} {𝓥 : TView Loc}
    {𝓝' : View Loc}
    (hg : GenInv (c.setS σ 𝓥 c.mem 𝓝'))
    (hnaC : ∀ i, 𝓝' (.chunk i) = c.na (.chunk i))
    (hnaA : ∀ l, ¬ l.IsChunk → (𝓝' l).w = (c.na l).w ∧ (𝓝' l).nr = (c.na l).nr)
    (hv : c.vs ≤ 𝓥.cur) (hlog : σ.log = c.s.log) (hnpub : σ.pc.npub = c.s.pc.npub)
    (hnfa : σ.pc.nfa = c.s.pc.nfa) (hfault : σ.pc ≠ .fault)
    (hpub : ∀ k b i s, σ.pc ≠ .pub k b i s)
    (phase : ∀ i, ∃ ph, PhaseOK pay ln (c.setS σ 𝓥 c.mem 𝓝') i ph) :
    Inv pay ln (c.setS σ 𝓥 c.mem 𝓝') where
  gen := hg
  phase := phase
  chunkS i := by simpa using (h.chunkS i).mono (hv _).1
  chunkNa i := by simpa [hnaC] using h.chunkNa i
  chunkAt i := by simpa [hnaC] using h.chunkAt i
  atomNa l hl := by
    simp only [Cfg.setS_na]; rw [(hnaA l hl).1, (hnaA l hl).2]; exact h.atomNa l hl
  atomVal := by simpa using h.atomVal
  lenS i := by simpa using (h.lenS i).mono (hv _).1
  cseqS i := by simpa using (h.cseqS i).mono (hv _).1
  cseqVal := by simpa [hnpub] using h.cseqVal
  cseqUniq := by simpa using h.cseqUniq
  curSeqVal := by simpa using h.curSeqVal
  curSeqDown := by simpa using h.curSeqDown
  curSeqTop := by simpa [hnfa] using h.curSeqTop
  curSeqHas := by simpa [hnfa] using h.curSeqHas
  tickVal := by simpa using h.tickVal
  tickDown := by simpa using h.tickDown
  sFault := by simpa using hfault
  sPub k b i s hh := absurd (by simpa using hh) (hpub k b i s)
  sLog := by simpa [hlog, hnpub] using h.sLog
  rFault := by simpa using h.rFault
  rRel := by simpa using h.rRel
  rTix := by simpa using h.rTix
  rLog := by simpa [hnpub] using h.rLog
  tixNodup := by simpa using h.tixNodup
  tixDisj := by simpa using h.tixDisj

theorem below_add {Mm : Mem} {l0 l : Loc} {m0 : MsgT} {t t' : ℕ} (hb : Below (Mm l) t)
    (h0 : l = l0 → m0.time ≤ t') (ht : t ≤ t') : Below (Mm.add l0 m0 l) t' := by
  intro m hm
  rcases Memory.mem_add.1 hm with ⟨rfl, rfl⟩ | hm
  · exact h0 rfl
  · exact (hb m hm).trans ht

theorem vs_def (c : Cfg ρ) : c.vs = (c.th .sender).2.cur := rfl

/-! ## `start` -/

theorem inv_s_start {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} (hpc : c.s.pc = .start k)
    {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  by_cases hk : k < M
  · have hp : sprog N M pay ln c.s = .choose fun b => { c.s with pc := .alloc k b 0 } := by
      simp [sprog, hpc, hk]
    obtain ⟨b, rfl, rfl, rfl, rfl⟩ := hst.choose_inv hp
    refine h.sender_noWrite pay ln hg (fun _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) le_rfl rfl
      (by simp [hpc, SPc.npub, SPc.k]) (by simp [hpc, SPc.nfa, SPc.k]) (by simp)
      (by simp) (fun i => ?_)
    obtain ⟨ph, hph⟩ := h.phase i
    exact ⟨ph, hph.sender_frame pay ln (Frame.sender rfl rfl rfl rfl rfl le_rfl
      (by simp [hpc, SPc.fill]) (by simp [hpc, SPc.sealing]) (by simp [SPc.fill, SPc.sealing])
      (by simp [hpc, SPc.npub, SPc.k]))⟩
  · have hp : sprog N M pay ln c.s = .halt := by simp [sprog, hpc, hk]
    exact (hst.halt_inv hp).elim

/-! ## `alloc` -/

theorem inv_s_alloc {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} {b : Bool} {j : ℕ}
    (hpc : c.s.pc = .alloc k b j) {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  obtain ⟨m, hm, tr, hle, -, -, hσ, h𝓥, rfl, hpost⟩ :=
    hst.read_inv (l := .own j) (o := .acqrel) (by simp only [sprog, hpc]; rfl)
  simp only [DrfPostRead, MemOrder.rlx_le_acqrel, ite_true] at hpost
  obtain ⟨rfl, -⟩ := hpost
  have hv : c.vs ≤ 𝓥.cur := hst.cur_le
  obtain ⟨v, hmv⟩ := Option.isSome_iff_exists.1 (h.atomVal _ (by simp [Loc.IsChunk]) m hm)
  simp only [hmv] at hσ
  have hnaC : ∀ i, addARead c.na (.own j) tr (.chunk i) = c.na (.chunk i) :=
    fun i => addARead_ne _ _ (by simp)
  have hnaA : ∀ l, ¬ l.IsChunk → (addARead c.na (.own j) tr l).w = (c.na l).w ∧
      (addARead c.na (.own j) tr l).nr = (c.na l).nr := by
    intro l _
    by_cases hl : l = .own j
    · subst hl; simp
    · simp [hl]
  -- the phase of buffer `j`
  obtain ⟨phj, hphj⟩ := h.phase j
  have uniq := h.gen.uniq (.own j)
  by_cases hv0 : v = 0
  · -- the sender takes buffer `j`
    simp only [hv0, ↓reduceIte] at hσ
    subst hσ hv0
    -- buffer `j` must be free, and `m` its latest message
    have hfree : ∃ f, PhaseOK pay ln c j .free ∧ IsLatest (c.mem (.own j)) f ∧
        m = f ∧ (c.na (.chunk j)).nr ⊆ (c.vs (.chunk j)).nr ∪ ((f.view.getD ⊥) (.chunk j)).nr := by
      match phj, hphj with
      | .free, hphj' =>
        obtain ⟨_, _, _, _, f, hfl, _, hf2, hf3⟩ := id hphj'
        exact ⟨f, hphj', hfl, hfl.eq_of_le uniq hm (le_of_eq (hf2 m hm hle hmv).symm), hf3⟩
      | .fill, hphj => exact absurd hphj.1 (by simp [hpc, SPc.fill])
      | .sealing, hphj => exact absurd hphj.1 (by simp [hpc, SPc.sealing])
      | .pub s, hphj =>
        obtain ⟨_, _, _, _, _, o, q, ho, hov, hot, -⟩ := hphj
        have := ho.eq_of_le uniq hm (hot.trans hle)
        rw [this, hov] at hmv; cases hmv
    obtain ⟨f, hfree, hfl, rfl, hf3⟩ := hfree
    obtain ⟨_, _, hnr, hnl, -⟩ := hfree
    refine h.sender_noWrite pay ln hg hnaC hnaA hv rfl (by simp [hpc, SPc.npub, SPc.k])
      (by simp [hpc, SPc.nfa, SPc.k]) (by simp) (by simp) (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      refine ⟨.fill, by simp [SPc.fill], ?_, ?_, ?_, ?_, by simp, by simp⟩
      · intro r; simpa using hnr r
      · intro m' hm' v' hv'; simpa using hnl m' (by simpa using hm') v' hv'
      · -- the sender has seen the latest `client_owned[i]`
        intro m' hm'
        simp only [Cfg.setS_mem, Cfg.setS_vs] at hm' ⊢
        rw [h𝓥]
        refine (hfl.2 m' hm').trans ?_
        exact (TimeInfo.w_mono (View.le_apply (readTView_V_le _ _ _ _) _)).trans_eq' (by simp)
      · -- and acquired every non-atomic read of the chunk
        simp only [Cfg.setS_na, Cfg.setS_vs, hnaC, h𝓥]
        refine hf3.trans (Finset.union_subset ?_ ?_)
        · exact TimeInfo.nr_mono (View.le_apply (readTView_cur_le _ _ _ _) _)
        · exact TimeInfo.nr_mono (View.le_apply (readTView_R_le _ _ _ (by decide)) _)
    · obtain ⟨ph, hph⟩ := h.phase i
      exact ⟨ph, hph.sender_frame pay ln (Frame.sender rfl rfl rfl rfl (by rw [hnaC]) hv
        (by simp [hpc, SPc.fill, Ne.symm hij]) (by simp [hpc, SPc.sealing])
        (by simp [SPc.fill, SPc.sealing, Ne.symm hij]) (by simp [hpc, SPc.npub, SPc.k]))⟩
  · -- the sender moves on to the next buffer
    simp only [hv0, ↓reduceIte] at hσ
    subst hσ
    refine h.sender_noWrite pay ln hg hnaC hnaA hv rfl (by simp [hpc, SPc.npub, SPc.k])
      (by simp [hpc, SPc.nfa, SPc.k]) (by simp) (by simp) (fun i => ?_)
    obtain ⟨ph, hph⟩ := h.phase i
    exact ⟨ph, hph.sender_frame pay ln (Frame.sender rfl rfl rfl rfl (by rw [hnaC]) hv
      (by simp [hpc, SPc.fill]) (by simp [hpc, SPc.sealing]) (by simp [SPc.fill, SPc.sealing])
      (by simp [hpc, SPc.npub, SPc.k]))⟩

/-! ## `chunk`: the non-atomic write of the payload -/

theorem inv_s_chunk {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} {b : Bool} {j : ℕ}
    (hpc : c.s.pc = .chunk k b j) {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  obtain ⟨t, -, hlt, -, rfl, rfl, rfl, -, hpost⟩ :=
    hst.write_inv (l := .chunk j) (o := .na) (v := pay k) (by simp only [sprog, hpc]; rfl)
  simp only [DrfPostWrite, MemOrder.rlx_le_na, ↓reduceIte] at hpost
  subst hpost
  rw [← vs_def] at hlt
  have hv : c.vs ≤ (writeTView (c.th .sender).2 .na (.chunk j) t).cur :=
    writeTView_cur_le _ _ _ _
  have hvt : ((writeTView (c.th .sender).2 .na (.chunk j) t).cur (.chunk j)).w = t :=
    writeTView_cur_w _ _ _ hlt
  have hnaC : ∀ i, i ≠ j → setWriteTime c.na (.chunk j) t (.chunk i) = c.na (.chunk i) :=
    fun i hij => setWriteTime_ne _ _ (by simpa using hij)
  have hnaA : ∀ l, ¬ l.IsChunk → setWriteTime c.na (.chunk j) t l = c.na l := by
    intro l hl; apply setWriteTime_ne; rintro rfl; exact hl trivial
  have hmemA : ∀ l, ¬ l.IsChunk → c.mem.add (.chunk j) ⟨t, some (pay k),
      writeRw (c.th .sender).2 .na (.chunk j) t ⊥⟩ l = c.mem l := by
    intro l hl; apply Memory.add_ne; rintro rfl; exact hl trivial
  have hmemC : ∀ i, i ≠ j → c.mem.add (.chunk j) ⟨t, some (pay k),
      writeRw (c.th .sender).2 .na (.chunk j) t ⊥⟩ (.chunk i) = c.mem (.chunk i) :=
    fun i hij => Memory.add_ne _ _ (by simpa using hij)
  have NC : ∀ i, ¬ (Loc.own i).IsChunk ∧ ¬ (Loc.len i).IsChunk ∧ ¬ (Loc.cseq i).IsChunk :=
    fun i => ⟨by simp [Loc.IsChunk], by simp [Loc.IsChunk], by simp [Loc.IsChunk]⟩
  have NCs : ¬ Loc.curSeq.IsChunk ∧ ¬ Loc.tick.IsChunk := ⟨by simp [Loc.IsChunk], by simp [Loc.IsChunk]⟩
  have hk : ({ c.s with pc := .len k b j } : SState).pc.npub = c.s.pc.npub := by
    simp [hpc, SPc.npub, SPc.k]
  have hkf : ({ c.s with pc := .len k b j } : SState).pc.nfa = c.s.pc.nfa := by
    simp [hpc, SPc.nfa, SPc.k]
  refine
  { gen := hg
    phase := fun i => ?_
    chunkS := fun i => ?_
    chunkNa := fun i => ?_
    chunkAt := fun i => ?_
    atomNa := fun l hl => by simpa [hnaA l hl] using h.atomNa l hl
    atomVal := fun l hl => by simpa [hmemA l hl] using h.atomVal l hl
    lenS := fun i => by simpa [hmemA _ (NC i).2.1] using (h.lenS i).mono (hv _).1
    cseqS := fun i => by simpa [hmemA _ (NC i).2.2] using (h.cseqS i).mono (hv _).1
    cseqVal := fun i => by simpa [hmemA _ (NC i).2.2, hk] using h.cseqVal i
    cseqUniq := fun i j' => by simpa [hmemA _ (NC i).2.2, hmemA _ (NC j').2.2] using h.cseqUniq i j'
    curSeqVal := by simpa [hmemA _ NCs.1] using h.curSeqVal
    curSeqDown := by simpa [hmemA _ NCs.1] using h.curSeqDown
    curSeqTop := by simpa [hmemA _ NCs.1, hkf] using h.curSeqTop
    curSeqHas := by simpa [hmemA _ NCs.1, hkf] using h.curSeqHas
    tickVal := by simpa [hmemA _ NCs.2] using h.tickVal
    tickDown := by simpa [hmemA _ NCs.2] using h.tickDown
    sFault := by simp
    sPub := by simp
    sLog := by simpa [hk] using h.sLog
    rFault := by simpa using h.rFault
    rRel := by simpa using h.rRel
    rTix := by simpa [hmemA _ NCs.2] using h.rTix
    rLog := by simpa [hk] using h.rLog
    tixNodup := by simpa using h.tixNodup
    tixDisj := by simpa using h.tixDisj }
  · -- phases
    by_cases hij : i = j
    · subst hij
      obtain ⟨phj, hphj⟩ := h.phase i
      match phj, hphj with
      | .free, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
      | .sealing, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.sealing])
      | .pub _, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
      | .fill, hphj' =>
        obtain ⟨-, hnr, hnl, hbo, hna, -, -⟩ := hphj'
        refine ⟨.fill, by simp [SPc.fill], fun r => by simpa using hnr r, ?_, ?_, ?_, ?_, ?_⟩
        · intro m' hm' v' hv'
          simpa using hnl m' (by simpa [hmemA _ (NC i).2.2] using hm') v' hv'
        · simpa [hmemA _ (NC i).1] using hbo.mono (hv _).1
        · simpa using hna.trans (hv _).2.2.1
        · intro k' b' hk'
          simp only [Cfg.setS_s, SPc.len.injEq] at hk'
          obtain ⟨rfl, -, -⟩ := hk'
          simp only [Cfg.setS_mem, Memory.add_self]
          exact latestIs_cons_new (h.chunkS i) hlt rfl
        · intro k' b' hk'; simp at hk'
    · obtain ⟨ph, hph⟩ := h.phase i
      exact ⟨ph, hph.sender_frame pay ln (Frame.sender (hmemA _ (NC i).1) (hmemA _ (NC i).2.1)
        (hmemA _ (NC i).2.2) (hmemC i hij) (by rw [hnaC i hij]) hv
        (by simp [hpc, SPc.fill, Ne.symm hij]) (by simp [hpc, SPc.sealing])
        (by simp [SPc.fill, SPc.sealing, Ne.symm hij]) (by simp [hk]))⟩
  · -- the sender remains the only writer of chunks
    simp only [Cfg.setS_mem, Cfg.setS_vs]
    refine below_add ((h.chunkS i).mono (hv _).1) ?_ le_rfl
    intro hij; cases hij; simp [hvt]
  · by_cases hij : i = j
    · subst hij
      simp only [Cfg.setS_mem, Cfg.setS_na, Memory.add_self, setWriteTime_self]
      exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨m', hm', ht'⟩ := h.chunkNa i
      exact ⟨m', by simpa [hmemC i hij] using hm', by simpa [hnaC i hij] using ht'⟩
  · by_cases hij : i = j
    · subst hij; simpa using h.chunkAt i
    · simpa [hnaC i hij] using h.chunkAt i

/-! ## `len` and `own`: relaxed writes -/

/-- Facts about a relaxed sender write to `l0`, which is `client_len[j]` or
`client_owned[j]`. -/
theorem Inv.sender_rlx {c : Cfg ρ} (h : Inv pay ln c) {σ : SState} {l0 : Loc} {j t : ℕ}
    {v : ℤ} (hl0 : l0 = .len j ∨ l0 = .own j)
    (hg : GenInv (c.setS σ (writeTView (c.th .sender).2 .rlx l0 t)
      (c.mem.add l0 ⟨t, some v, writeRw (c.th .sender).2 .rlx l0 t ⊥⟩) (addAWrite c.na l0 t)))
    (hlt : (c.vs l0).w < t) (hlog : σ.log = c.s.log) (hnpub : σ.pc.npub = c.s.pc.npub)
    (hnfa : σ.pc.nfa = c.s.pc.nfa) (hfault : σ.pc ≠ .fault)
    (hpub : ∀ k b i s, σ.pc ≠ .pub k b i s)
    (phase : ∀ i, ∃ ph, PhaseOK pay ln (c.setS σ (writeTView (c.th .sender).2 .rlx l0 t)
      (c.mem.add l0 ⟨t, some v, writeRw (c.th .sender).2 .rlx l0 t ⊥⟩)
      (addAWrite c.na l0 t)) i ph) :
    Inv pay ln (c.setS σ (writeTView (c.th .sender).2 .rlx l0 t)
      (c.mem.add l0 ⟨t, some v, writeRw (c.th .sender).2 .rlx l0 t ⊥⟩) (addAWrite c.na l0 t)) := by
  have hv : c.vs ≤ (writeTView (c.th .sender).2 .rlx l0 t).cur := writeTView_cur_le _ _ _ _
  have hvt : ((writeTView (c.th .sender).2 .rlx l0 t).cur l0).w = t :=
    writeTView_cur_w _ _ _ hlt
  have hl0C : ¬ l0.IsChunk := by rcases hl0 with rfl | rfl <;> simp [Loc.IsChunk]
  have hmem : ∀ l, l ≠ l0 → c.mem.add l0 ⟨t, some v, writeRw (c.th .sender).2 .rlx l0 t ⊥⟩ l =
      c.mem l := fun l hl => Memory.add_ne _ _ hl
  have hC : ∀ i, Loc.chunk i ≠ l0 := by intro i; rcases hl0 with rfl | rfl <;> simp
  have hQ : ∀ i, Loc.cseq i ≠ l0 := by intro i; rcases hl0 with rfl | rfl <;> simp
  have hS : Loc.curSeq ≠ l0 := by rcases hl0 with rfl | rfl <;> simp
  have hT : Loc.tick ≠ l0 := by rcases hl0 with rfl | rfl <;> simp
  exact
  { gen := hg
    phase := phase
    chunkS := fun i => by simpa [hmem _ (hC i)] using (h.chunkS i).mono (hv _).1
    chunkNa := fun i => by simpa [hmem _ (hC i), addAWrite_ne _ _ (hC i)] using h.chunkNa i
    chunkAt := fun i => by simpa [addAWrite_ne _ _ (hC i)] using h.chunkAt i
    atomNa := fun l hl => by
      by_cases hl' : l = l0
      · subst hl'; simpa using h.atomNa l hl
      · simpa [addAWrite_ne _ _ hl'] using h.atomNa l hl
    atomVal := fun l hl m hm => by
      simp only [Cfg.setS_mem] at hm
      rcases Memory.mem_add.1 hm with ⟨-, rfl⟩ | hm
      · rfl
      · exact h.atomVal l hl m hm
    lenS := fun i => by
      simp only [Cfg.setS_mem, Cfg.setS_vs]
      refine below_add ((h.lenS i).mono (hv _).1) ?_ le_rfl
      intro hi; rw [hi, hvt]
    cseqS := fun i => by simpa [hmem _ (hQ i)] using (h.cseqS i).mono (hv _).1
    cseqVal := fun i => by simpa [hmem _ (hQ i), hnpub] using h.cseqVal i
    cseqUniq := fun i j' => by simpa [hmem _ (hQ i), hmem _ (hQ j')] using h.cseqUniq i j'
    curSeqVal := by simpa [hmem _ hS] using h.curSeqVal
    curSeqDown := by simpa [hmem _ hS] using h.curSeqDown
    curSeqTop := by simpa [hmem _ hS, hnfa] using h.curSeqTop
    curSeqHas := by simpa [hmem _ hS, hnfa] using h.curSeqHas
    tickVal := by simpa [hmem _ hT] using h.tickVal
    tickDown := by simpa [hmem _ hT] using h.tickDown
    sFault := by simpa using hfault
    sPub := fun k b i s hh => absurd (by simpa using hh) (hpub k b i s)
    sLog := by simpa [hlog, hnpub] using h.sLog
    rFault := by simpa using h.rFault
    rRel := by simpa using h.rRel
    rTix := by simpa [hmem _ hT] using h.rTix
    rLog := by simpa [hnpub] using h.rLog
    tixNodup := by simpa using h.tixNodup
    tixDisj := by simpa using h.tixDisj }

theorem inv_s_len {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} {b : Bool} {j : ℕ}
    (hpc : c.s.pc = .len k b j) {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  obtain ⟨t, -, hlt, -, rfl, rfl, rfl, -, hpost⟩ :=
    hst.write_inv (l := .len j) (o := .rlx) (v := ln k) (by simp only [sprog, hpc]; rfl)
  simp only [DrfPostWrite, MemOrder.rlx_le_rlx, ↓reduceIte] at hpost
  subst hpost
  rw [← vs_def] at hlt
  have hv : c.vs ≤ (writeTView (c.th .sender).2 .rlx (.len j) t).cur :=
    writeTView_cur_le _ _ _ _
  refine h.sender_rlx pay ln (Or.inl rfl) hg hlt rfl (by simp [hpc, SPc.npub, SPc.k])
    (by simp [hpc, SPc.nfa, SPc.k]) (by simp) (by simp) (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    obtain ⟨phj, hphj⟩ := h.phase i
    match phj, hphj with
    | .free, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
    | .sealing, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.sealing])
    | .pub _, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
    | .fill, hphj' =>
      obtain ⟨-, hnr, hnl, hbo, hna, hc1, -⟩ := hphj'
      refine ⟨.fill, by simp [SPc.fill], fun r => by simpa using hnr r, ?_, ?_, ?_, ?_, ?_⟩
      · intro m' hm' v' hv'
        simpa using hnl m' (by simpa using hm') v' hv'
      · simpa using hbo.mono (hv _).1
      · simpa using hna.trans (hv _).2.2.1
      · intro k' b' hk'; simp at hk'
      · intro k' b' hk'
        simp only [Cfg.setS_s, SPc.own.injEq] at hk'
        obtain ⟨rfl, -, -⟩ := hk'
        simp only [Cfg.setS_mem, Memory.add_self, ne_eq, reduceCtorEq, not_false_eq_true,
          Memory.add_ne]
        exact ⟨hc1 k b hpc, latestIs_cons_new (h.lenS i) hlt rfl⟩
  · obtain ⟨ph, hph⟩ := h.phase i
    refine ⟨ph, hph.sender_frame pay ln (Frame.sender ?_ ?_ ?_ ?_ ?_ hv ?_ ?_ ?_ ?_)⟩ <;>
      simp [hpc, SPc.fill, SPc.sealing, SPc.npub, SPc.k, hij, Ne.symm hij]

theorem inv_s_own {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} {b : Bool} {j : ℕ}
    (hpc : c.s.pc = .own k b j) {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  obtain ⟨t, -, hlt, -, rfl, rfl, rfl, -, hpost⟩ :=
    hst.write_inv (l := .own j) (o := .rlx) (v := 1) (by simp only [sprog, hpc]; rfl)
  simp only [DrfPostWrite, MemOrder.rlx_le_rlx, ↓reduceIte] at hpost
  subst hpost
  rw [← vs_def] at hlt
  have hv : c.vs ≤ (writeTView (c.th .sender).2 .rlx (.own j) t).cur :=
    writeTView_cur_le _ _ _ _
  have hvt : ((writeTView (c.th .sender).2 .rlx (.own j) t).cur (.own j)).w = t :=
    writeTView_cur_w _ _ _ hlt
  refine h.sender_rlx pay ln (Or.inr rfl) hg hlt rfl (by simp [hpc, SPc.npub, SPc.k])
    (by simp [hpc, SPc.nfa, SPc.k]) (by simp) (by simp) (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    obtain ⟨phj, hphj⟩ := h.phase i
    match phj, hphj with
    | .free, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
    | .sealing, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.sealing])
    | .pub _, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
    | .fill, hphj' =>
      obtain ⟨-, hnr, hnl, hbo, hna, -, hc2⟩ := hphj'
      obtain ⟨hc, hl⟩ := hc2 k b hpc
      refine ⟨.sealing, by simp [SPc.sealing], fun r => by simpa using hnr r, ?_, ?_, ?_, ?_, ?_⟩
      · intro m' hm' v' hv'
        simpa using hnl m' (by simpa using hm') v' hv'
      · simpa using hna.trans (hv _).2.2.1
      · simpa [SPc.k] using hc
      · simpa [SPc.k] using hl
      · simp only [Cfg.setS_mem, Memory.add_self, Cfg.setS_vs]
        exact ⟨_, isLatest_cons_new hbo hlt, rfl, by simp [hvt]⟩
  · obtain ⟨ph, hph⟩ := h.phase i
    refine ⟨ph, hph.sender_frame pay ln (Frame.sender ?_ ?_ ?_ ?_ ?_ hv ?_ ?_ ?_ ?_)⟩ <;>
      simp [hpc, SPc.fill, SPc.sealing, SPc.npub, SPc.k, hij, Ne.symm hij]

/-! ## `spin` -/

theorem inv_s_spin {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} {j : ℕ}
    (hpc : c.s.pc = .spin k j) {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  obtain ⟨m, hm, tr, hle, -, -, hσ, h𝓥, rfl, hpost⟩ :=
    hst.read_inv (l := .own j) (o := .rlx) (by simp only [sprog, hpc]; rfl)
  simp only [DrfPostRead, MemOrder.rlx_le_rlx, ↓reduceIte] at hpost
  obtain ⟨rfl, -⟩ := hpost
  have hv : c.vs ≤ 𝓥.cur := hst.cur_le
  obtain ⟨v, hmv⟩ := Option.isSome_iff_exists.1 (h.atomVal _ (by simp [Loc.IsChunk]) m hm)
  simp only [hmv] at hσ
  have hnaC : ∀ i, addARead c.na (.own j) tr (.chunk i) = c.na (.chunk i) :=
    fun i => addARead_ne _ _ (by simp)
  have hnaA : ∀ l, ¬ l.IsChunk → (addARead c.na (.own j) tr l).w = (c.na l).w ∧
      (addARead c.na (.own j) tr l).nr = (c.na l).nr := by
    intro l _
    by_cases hl : l = .own j
    · subst hl; simp
    · simp [hl]
  have key : σ.pc.npub = c.s.pc.npub ∧ σ.pc.nfa = c.s.pc.nfa ∧ σ.pc.fill = none ∧
      σ.pc.sealing = none ∧ σ.log = c.s.log ∧ σ.pc ≠ .fault ∧ ∀ k b i s, σ.pc ≠ .pub k b i s := by
    by_cases hv0 : v = 0 <;> simp only [hv0, ↓reduceIte] at hσ <;> subst hσ <;>
      simp [hpc, SPc.npub, SPc.nfa, SPc.k, SPc.fill, SPc.sealing]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
  refine h.sender_noWrite pay ln hg hnaC hnaA hv k5 k1 k2 k6 k7 (fun i => ?_)
  obtain ⟨ph, hph⟩ := h.phase i
  refine ⟨ph, hph.sender_frame pay ln (Frame.sender rfl rfl rfl rfl (by rw [hnaC]) hv
    ?_ ?_ ?_ ?_)⟩
  · rw [k3]; simp [hpc, SPc.fill]
  · rw [k4]; simp [hpc, SPc.sealing]
  · rw [k3, k4]; simp
  · rw [k1]

/-! ## `fadd`: `cur_seq.fetch_add(1, Relaxed)` -/

theorem inv_s_fadd {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} {b : Bool} {j : ℕ}
    (hpc : c.s.pc = .fadd k b j) {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  have hv : c.vs ≤ 𝓥.cur := hst.cur_le
  obtain ⟨m1, hm1, v, tr, hv1, -, -, hfresh, -, -, hσ, -, hM, -, hpost⟩ :=
    hst.update_inv (l := .curSeq) (or := .rlx) (ow := .rlx) (f := (· + 1))
      (by simp only [sprog, hpc]; rfl)
  obtain ⟨rfl, -⟩ := hpost
  have hnfa : c.s.pc.nfa = k := by simp [hpc, SPc.nfa, SPc.k]
  -- the update reads the latest `cur_seq`, at time `k + 1`
  have ht1 : m1.time = k + 1 := by
    obtain ⟨mt, hmt, hmt'⟩ := h.curSeqHas
    have h1 : m1.time ≤ k + 1 := hnfa ▸ h.curSeqTop m1 hm1
    by_contra hne
    obtain ⟨m', hm', ht'⟩ := h.curSeqDown mt hmt (m1.time + 1) (by omega) (by omega)
    exact hfresh m' hm' ht'
  have hvk : v = k := by
    have := h.curSeqVal m1 hm1
    rw [hv1, ht1] at this
    simp only [Option.some.injEq] at this; omega
  subst hvk
  subst hσ
  obtain ⟨mnew, hmt, hmv, rfl⟩ : ∃ mnew : MsgT, mnew.time = m1.time + 1 ∧
      mnew.val = some ((k : ℤ) + 1) ∧ M' = c.mem.add .curSeq mnew := ⟨_, rfl, rfl, hM⟩
  have hmem : ∀ l, l ≠ .curSeq → c.mem.add .curSeq mnew l = c.mem l :=
    fun l hl => Memory.add_ne _ _ hl
  have hnaC : ∀ i, addAWrite (addARead c.na .curSeq tr) .curSeq (m1.time + 1) (.chunk i) =
      c.na (.chunk i) := fun i => by simp
  have hk : ({ c.s with pc := .pub k b j (k : ℤ) } : SState).pc.npub = c.s.pc.npub := by
    simp [hpc, SPc.npub, SPc.k]
  refine
  { gen := hg
    phase := fun i => ?_
    chunkS := fun i => by simpa [hmem] using (h.chunkS i).mono (hv _).1
    chunkNa := fun i => by simpa [hmem] using h.chunkNa i
    chunkAt := fun i => by simpa using h.chunkAt i
    atomNa := fun l hl => by
      by_cases hl' : l = .curSeq
      · subst hl'; simpa using h.atomNa _ hl
      · simpa [hl'] using h.atomNa l hl
    atomVal := fun l hl m hm => by
      simp only [Cfg.setS_mem] at hm
      rcases Memory.mem_add.1 hm with ⟨-, he⟩ | hm
      · rw [he, hmv]; rfl
      · exact h.atomVal l hl m hm
    lenS := fun i => by simpa [hmem] using (h.lenS i).mono (hv _).1
    cseqS := fun i => by simpa [hmem] using (h.cseqS i).mono (hv _).1
    cseqVal := fun i => by simpa [hmem, hk] using h.cseqVal i
    cseqUniq := fun i j' => by simpa [hmem] using h.cseqUniq i j'
    curSeqVal := fun m hm => by
      simp only [Cfg.setS_mem, Memory.add_self, List.mem_cons] at hm
      rcases hm with he | hm
      · rw [he, hmv, hmt, ht1]; simp only [Option.some.injEq]; omega
      · exact h.curSeqVal m hm
    curSeqDown := fun m hm t' h1 h2 => by
      simp only [Cfg.setS_mem, Memory.add_self, List.mem_cons] at hm ⊢
      rcases hm with he | hm
      · rw [he, hmt] at h2
        by_cases ht' : t' = m1.time + 1
        · exact ⟨mnew, Or.inl rfl, by rw [hmt, ht']⟩
        · obtain ⟨m', hm', ht''⟩ := h.curSeqDown m1 hm1 t' h1 (by omega)
          exact ⟨m', Or.inr hm', ht''⟩
      · obtain ⟨m', hm', ht''⟩ := h.curSeqDown m hm t' h1 h2
        exact ⟨m', Or.inr hm', ht''⟩
    curSeqTop := fun m hm => by
      simp only [Cfg.setS_mem, Memory.add_self, List.mem_cons] at hm
      simp only [Cfg.setS_s, SPc.nfa]
      rcases hm with he | hm
      · rw [he, hmt, ht1]
      · have := h.curSeqTop m hm; rw [hnfa] at this; omega
    curSeqHas := ⟨mnew, by simp, by simp [hmt, ht1, SPc.nfa]⟩
    tickVal := by simpa [hmem] using h.tickVal
    tickDown := by simpa [hmem] using h.tickDown
    sFault := by simp
    sPub := fun k' b' i' s' hh => by simp at hh; obtain ⟨rfl, -, -, rfl⟩ := hh; rfl
    sLog := by simpa [hk] using h.sLog
    rFault := by simpa using h.rFault
    rRel := by simpa using h.rRel
    rTix := by simpa [hmem] using h.rTix
    rLog := by simpa [hk] using h.rLog
    tixNodup := by simpa using h.tixNodup
    tixDisj := by simpa using h.tixDisj }
  by_cases hij : i = j
  · subst hij
    obtain ⟨phj, hphj⟩ := h.phase i
    match phj, hphj with
    | .free, hphj' => exact absurd hphj'.2.1 (by simp [hpc, SPc.sealing])
    | .fill, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
    | .pub _, hphj' => exact absurd hphj'.2.1 (by simp [hpc, SPc.sealing])
    | .sealing, hphj' =>
      obtain ⟨-, hnr, hnl, hna, hc1, hc2, o, ho, hov, hot⟩ := hphj'
      refine ⟨.sealing, by simp [SPc.sealing], fun r => by simpa using hnr r, ?_, ?_, ?_, ?_,
        o, by simpa [hmem] using ho, hov, by simpa using hot.trans (hv _).1⟩
      · intro m' hm' v' hv'
        simpa using hnl m' (by simpa [hmem] using hm') v' hv'
      · simpa using hna.trans (hv _).2.2.1
      · simpa [hmem, hpc, SPc.k] using hc1
      · simpa [hmem, hpc, SPc.k] using hc2
  · obtain ⟨ph, hph⟩ := h.phase i
    refine ⟨ph, hph.sender_frame pay ln (Frame.sender ?_ ?_ ?_ ?_ ?_ hv ?_ ?_ ?_ ?_)⟩ <;>
      simp [hpc, SPc.fill, SPc.sealing, SPc.npub, SPc.k, hij, Ne.symm hij, hmem]

/-! ## `pub`: `client_seq[i].store(seq, Release)` -/

theorem inv_s_pub {c : Cfg ρ} (h : Inv pay ln c) {k : ℕ} {b : Bool} {j : ℕ} {s : ℤ}
    (hpc : c.s.pc = .pub k b j s) {σ : SState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  have hsk : s = k := h.sPub k b j s hpc
  subst hsk
  obtain ⟨t, -, hlt, -, hσ, rfl, hM, -, hpost⟩ :=
    hst.write_inv (l := .cseq j) (o := .acqrel) (v := (k : ℤ)) (by simp only [sprog, hpc]; rfl)
  simp only [DrfPostWrite, MemOrder.rlx_le_acqrel, ↓reduceIte] at hpost
  subst hpost
  rw [← vs_def] at hlt
  have hqv' : c.vs ≤ (writeRw (c.th .sender).2 .acqrel (.cseq j) t ⊥).getD ⊥ :=
    writeRw_rel (o := .acqrel) (by decide)
  obtain ⟨q, hqt, hqval, hqv, rfl⟩ : ∃ q : MsgT, q.time = t ∧ q.val = some (k : ℤ) ∧
      c.vs ≤ q.view.getD ⊥ ∧ M' = c.mem.add (.cseq j) q := ⟨_, rfl, rfl, hqv', hM⟩
  have hv : c.vs ≤ (writeTView (c.th .sender).2 .acqrel (.cseq j) t).cur :=
    writeTView_cur_le _ _ _ _
  have hvt : ((writeTView (c.th .sender).2 .acqrel (.cseq j) t).cur (.cseq j)).w = t :=
    writeTView_cur_w _ _ _ hlt
  have hmem : ∀ l, l ≠ .cseq j → c.mem.add (.cseq j) q l = c.mem l :=
    fun l hl => Memory.add_ne _ _ hl
  have hnaC : ∀ i, addAWrite c.na (.cseq j) t (.chunk i) = c.na (.chunk i) := fun i => by simp
  -- the new program counter
  have key : σ.pc.npub = k + 1 ∧ σ.pc.nfa = k + 1 ∧ σ.pc.fill = none ∧
      σ.pc.sealing = none ∧ σ.log = ((k : ℤ), pay k, ln k) :: c.s.log ∧ σ.pc ≠ .fault ∧
      ∀ k b i s, σ.pc ≠ .pub k b i s := by
    subst hσ; cases b <;> simp [SPc.npub, SPc.nfa, SPc.k, SPc.fill, SPc.sealing]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
  have hnp : c.s.pc.npub = k := by simp [hpc, SPc.npub, SPc.k]
  have hnf : c.s.pc.nfa = k + 1 := by simp [hpc, SPc.nfa, SPc.k]
  refine
  { gen := hg
    phase := fun i => ?_
    chunkS := fun i => by simpa [hmem] using (h.chunkS i).mono (hv _).1
    chunkNa := fun i => by simpa [hmem] using h.chunkNa i
    chunkAt := fun i => by simpa using h.chunkAt i
    atomNa := fun l hl => by
      by_cases hl' : l = .cseq j
      · subst hl'; simpa using h.atomNa _ hl
      · simpa [hl'] using h.atomNa l hl
    atomVal := fun l hl m hm => by
      simp only [Cfg.setS_mem] at hm
      rcases Memory.mem_add.1 hm with ⟨-, he⟩ | hm
      · rw [he, hqval]; rfl
      · exact h.atomVal l hl m hm
    lenS := fun i => by simpa [hmem] using (h.lenS i).mono (hv _).1
    cseqS := fun i => by
      simp only [Cfg.setS_mem, Cfg.setS_vs]
      refine below_add ((h.cseqS i).mono (hv _).1) ?_ le_rfl
      intro hi; cases hi; rw [hvt, hqt]
    cseqVal := fun i m hm v hv' => by
      simp only [Cfg.setS_mem, Cfg.setS_s, k1] at hm ⊢
      rcases Memory.mem_add.1 hm with ⟨-, he⟩ | hm
      · rw [he, hqval, Option.some.injEq] at hv'; subst hv'; right; omega
      · rcases h.cseqVal i m hm v hv' with h1 | h1
        · exact Or.inl h1
        · right; rw [hnp] at h1; omega
    cseqUniq := fun i i' m hm m' hm' v hv1 hv2 hne => by
      simp only [Cfg.setS_mem] at hm hm'
      rcases Memory.mem_add.1 hm with ⟨hi, he⟩ | hm <;>
        rcases Memory.mem_add.1 hm' with ⟨hi', he'⟩ | hm'
      · simp only [Loc.cseq.injEq] at hi hi'; rw [hi, hi']
      · rw [he, hqval, Option.some.injEq] at hv1; subst hv1
        rcases h.cseqVal i' m' hm' _ hv2 with h1 | h1
        · exact absurd h1 hne
        · rw [hnp] at h1; omega
      · rw [he', hqval, Option.some.injEq] at hv2; subst hv2
        rcases h.cseqVal i m hm _ hv1 with h1 | h1
        · exact absurd h1 hne
        · rw [hnp] at h1; omega
      · exact h.cseqUniq i i' m hm m' hm' v hv1 hv2 hne
    curSeqVal := by simpa [hmem] using h.curSeqVal
    curSeqDown := by simpa [hmem] using h.curSeqDown
    curSeqTop := by simpa [hmem, k2, hnf] using h.curSeqTop
    curSeqHas := by simpa [hmem, k2, hnf] using h.curSeqHas
    tickVal := by simpa [hmem] using h.tickVal
    tickDown := by simpa [hmem] using h.tickDown
    sFault := by simpa using k6
    sPub := fun k' b' i' s' hh => absurd (by simpa using hh) (k7 k' b' i' s')
    sLog := by simp only [Cfg.setS_s, k5, k1, h.sLog, hnp]; rfl
    rFault := by simpa using h.rFault
    rRel := by simpa using h.rRel
    rTix := by simpa [hmem] using h.rTix
    rLog := fun r e he => by
      obtain ⟨e1, e2, e3, e4⟩ := h.rLog r e (by simpa using he)
      refine ⟨e1, ?_, e3, e4⟩
      simp only [Cfg.setS_s, k1]; rw [hnp] at e2; omega
    tixNodup := by simpa using h.tixNodup
    tixDisj := by simpa using h.tixDisj }
  by_cases hij : i = j
  · subst hij
    obtain ⟨phj, hphj⟩ := h.phase i
    match phj, hphj with
    | .free, hphj' => exact absurd hphj'.2.1 (by simp [hpc, SPc.sealing])
    | .fill, hphj' => exact absurd hphj'.1 (by simp [hpc, SPc.fill])
    | .pub _, hphj' => exact absurd hphj'.2.1 (by simp [hpc, SPc.sealing])
    | .sealing, hphj' =>
      obtain ⟨-, hnr, hnl, hna, hc1, hc2, o, ho, hov, hot⟩ := hphj'
      refine ⟨.pub k, by simp [k3], by simp [k4], by simp [k1], ?_, ?_, o, q, ?_, hov,
        by simpa using hot.trans (hv _).1, ?_, hqval, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hmem, hpc, SPc.k] using hc1
      · simpa [hmem, hpc, SPc.k] using hc2
      · simpa [hmem] using ho
      · simp only [Cfg.setS_mem, Memory.add_self]
        exact isLatest_cons_new (h.cseqS i) (hqt ▸ hlt)
      · simpa [hmem] using (h.chunkS i).mono (hqv _).1
      · simpa [hmem] using (h.lenS i).mono (hqv _).1
      · exact hot.trans (hqv _).1
      · intro m hm v hv'
        simp only [Cfg.setS_mem, Memory.add_self, List.mem_cons] at hm
        rcases hm with he | hm
        · exact Or.inr (Or.inr (by rw [he]))
        · rcases hnl m hm v hv' with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inl (by simpa using h1))
      · intro r hr; exact absurd (by simpa using hr) (hnr r)
      · intro id hid
        simp only [Cfg.setS_na, hnaC] at hid
        exact Or.inl ((hv _).2.2.1 (hna hid))
      · -- the new sequence number is not consumed yet
        intro hc
        obtain ⟨r, hr⟩ := (consumed_setS).1 hc
        obtain ⟨e, he, he1⟩ := List.mem_map.1 hr
        have := (h.rLog r e he).2.1
        rw [he1, hnp] at this; omega
  · obtain ⟨ph, hph⟩ := h.phase i
    refine ⟨ph, hph.sender_frame pay ln (Frame.sender ?_ ?_ ?_ ?_ ?_ hv ?_ ?_ ?_ ?_)⟩
    · simp [hmem]
    · simp [hmem]
    · simp [hmem, hij]
    · simp [hmem]
    · simp [hnaC]
    · rw [k3, hpc]; simp [SPc.fill]
    · rw [k4, hpc]; simp [SPc.sealing, Ne.symm hij]
    · rw [k3, k4]; simp
    · rw [k1, hnp]; omega

/-! ## All sender steps -/

theorem inv_sender {c : Cfg ρ} (h : Inv pay ln c) {σ : SState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setS σ 𝓥 M' 𝓝')) : Inv pay ln (c.setS σ 𝓥 M' 𝓝') := by
  cases hpc : c.s.pc with
  | start k => exact inv_s_start N M pay ln h hpc hst hg
  | alloc k b i => exact inv_s_alloc N M pay ln h hpc hst hg
  | chunk k b i => exact inv_s_chunk N M pay ln h hpc hst hg
  | len k b i => exact inv_s_len N M pay ln h hpc hst hg
  | own k b i => exact inv_s_own N M pay ln h hpc hst hg
  | fadd k b i => exact inv_s_fadd N M pay ln h hpc hst hg
  | pub k b i s => exact inv_s_pub N M pay ln h hpc hst hg
  | spin k i => exact inv_s_spin N M pay ln h hpc hst hg
  | fault => exact (hst.fault_inv (by simp [sprog, hpc])).elim

end Mempipe
