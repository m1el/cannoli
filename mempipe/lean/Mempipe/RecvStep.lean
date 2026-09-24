import Mempipe.SenderStep

/-!
# Receiver steps preserve the invariant
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ)

theorem vr_def (c : Cfg ρ) (r : ρ) : c.vr r = (c.th (.recv r)).2.cur := rfl

/-- Accessors of a receiver step, by cases on the receiver. -/
theorem setR_r (c : Cfg ρ) (r0 r : ρ) (σ : RState) (𝓥 : TView Loc) (M' : Mem)
    (𝓝' : View Loc) : (c.setR r0 σ 𝓥 M' 𝓝').r r = if r = r0 then σ else c.r r := by
  split_ifs with h
  · subst h; simp
  · exact Cfg.setR_r_ne _ _ _ _ _ h

theorem setR_vr (c : Cfg ρ) (r0 r : ρ) (σ : RState) (𝓥 : TView Loc) (M' : Mem)
    (𝓝' : View Loc) : (c.setR r0 σ 𝓥 M' 𝓝').vr r = if r = r0 then 𝓥.cur else c.vr r := by
  split_ifs with h
  · subst h; simp
  · exact Cfg.setR_vr_ne _ _ _ _ _ h

theorem consumed_setR {c : Cfg ρ} {r0 : ρ} {σ : RState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc} (hlog : ∀ e ∈ (c.r r0).log, e ∈ σ.log) {v : ℤ} (h : Consumed c v) :
    Consumed (c.setR r0 σ 𝓥 M' 𝓝') v := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [setR_r]
  split_ifs with h
  · subst h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
    exact List.mem_map.2 ⟨e, hlog e he, rfl⟩
  · exact hr

/-- The frame conditions for a receiver step and a buffer it does not touch. -/
theorem Frame.recv {c : Cfg ρ} {r0 : ρ} {σ : RState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc} {i : ℕ}
    (hown : M' (.own i) = c.mem (.own i)) (hlen : M' (.len i) = c.mem (.len i))
    (hcseq : M' (.cseq i) = c.mem (.cseq i)) (hchunk : M' (.chunk i) = c.mem (.chunk i))
    (hna : (𝓝' (.chunk i)).nr = (c.na (.chunk i)).nr) (hv : c.vr r0 ≤ 𝓥.cur)
    (hlog : ∀ e ∈ (c.r r0).log, e ∈ σ.log)
    (hon : σ.pc.onBuf = some i → σ.pc = (c.r r0).pc)
    (hstay : (c.r r0).pc.onBuf = some i → σ.pc = (c.r r0).pc) :
    Frame c (c.setR r0 σ 𝓥 M' 𝓝') i where
  own := by simpa using hown
  len := by simpa using hlen
  cseq := by simpa using hcseq
  chunk := by simpa using hchunk
  na := by simpa using hna
  vs l := by simp
  vr r l := by
    rw [setR_vr]; split_ifs with h
    · subst h; exact hv l
    · exact le_rfl
  fill := by simp
  sealing := by simp
  pc := by simp
  npub := by simp
  cons v h := consumed_setR hlog h
  on r h := by
    rw [setR_r] at h ⊢; split_ifs at h ⊢ with hr
    · subst hr; exact hon h
    · rfl
  stay r h := by
    rw [setR_r]; split_ifs with hr
    · subst hr; exact hstay h
    · rfl

theorem PhaseOK.recv_frame {c : Cfg ρ} {r0 : ρ} {σ : RState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc} {i : ℕ} {ph : Phase} (h : PhaseOK pay ln c i ph)
    (F : Frame c (c.setR r0 σ 𝓥 M' 𝓝') i)
    (htk : ∀ s, ph = .pub s → (c.r r0).pc.ticket = some (s : ℤ) →
      σ.pc.ticket = some (s : ℤ))
    (hcons : ∀ s, ph = .pub s → Consumed (c.setR r0 σ 𝓥 M' 𝓝') (s : ℤ) → Consumed c (s : ℤ)) :
    PhaseOK pay ln (c.setR r0 σ 𝓥 M' 𝓝') i ph :=
  h.frame pay ln F (fun s hs r hr => by
    rw [setR_r]; split_ifs with h
    · subst h; exact htk s hs hr
    · exact hr) hcons

/-- With an unchanged log, consumption is unchanged. -/
theorem consumed_setR_same {c : Cfg ρ} {r0 : ρ} {σ : RState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc} (hlog : σ.log = (c.r r0).log) {v : ℤ} :
    Consumed (c.setR r0 σ 𝓥 M' 𝓝') v ↔ Consumed c v := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [setR_r] at hr; split_ifs at hr with h
    · subst h; rwa [hlog] at hr
    · exact hr
  · exact consumed_setR (fun e he => hlog ▸ he)

/-- Receiver steps that do not write memory. -/
theorem Inv.recv_noWrite {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {σ : RState}
    {𝓥 : TView Loc} {𝓝' : View Loc}
    (hg : GenInv (c.setR r0 σ 𝓥 c.mem 𝓝'))
    (hnaC : ∀ i, (𝓝' (.chunk i)).w = (c.na (.chunk i)).w ∧
      (𝓝' (.chunk i)).aw = (c.na (.chunk i)).aw ∧ (𝓝' (.chunk i)).ar = (c.na (.chunk i)).ar)
    (hnaA : ∀ l, ¬ l.IsChunk → (𝓝' l).w = (c.na l).w ∧ (𝓝' l).nr = (c.na l).nr)
    (hfault : σ.pc ≠ .fault) (hrel : ∀ t i, σ.pc = .rel t i → t ∈ σ.log.map Prod.fst)
    (htix : tix σ = tix (c.r r0))
    (hlog : ∀ e ∈ σ.log, 0 ≤ e.1 ∧ e.1 < c.s.pc.npub ∧ e.2.1 = pay e.1.toNat ∧
      e.2.2 = ln e.1.toNat)
    (phase : ∀ i, ∃ ph, PhaseOK pay ln (c.setR r0 σ 𝓥 c.mem 𝓝') i ph) :
    Inv pay ln (c.setR r0 σ 𝓥 c.mem 𝓝') where
  gen := hg
  phase := phase
  chunkS := by simpa using h.chunkS
  chunkNa i := by simpa [(hnaC i).1] using h.chunkNa i
  chunkAt i := by simpa [(hnaC i).2.1, (hnaC i).2.2] using h.chunkAt i
  atomNa l hl := by
    simp only [Cfg.setR_na]; rw [(hnaA l hl).1, (hnaA l hl).2]; exact h.atomNa l hl
  atomVal := by simpa using h.atomVal
  lenS := by simpa using h.lenS
  cseqS := by simpa using h.cseqS
  cseqVal := by simpa using h.cseqVal
  cseqUniq := by simpa using h.cseqUniq
  curSeqVal := by simpa using h.curSeqVal
  curSeqDown := by simpa using h.curSeqDown
  curSeqTop := by simpa using h.curSeqTop
  curSeqHas := by simpa using h.curSeqHas
  tickVal := by simpa using h.tickVal
  tickDown := by simpa using h.tickDown
  sFault := by simpa using h.sFault
  sPub := by simpa using h.sPub
  sLog := by simpa using h.sLog
  rFault r := by
    rw [setR_r]; split_ifs with hr
    · exact hfault
    · exact h.rFault r
  rRel r := by
    rw [setR_r]; split_ifs with hr
    · exact hrel
    · exact h.rRel r
  rTix r := by
    rw [setR_r]; split_ifs with hr
    · subst hr; rw [htix]; simpa using h.rTix r
    · simpa using h.rTix r
  rLog r := by
    rw [setR_r]; split_ifs with hr
    · simpa using hlog
    · simpa using h.rLog r
  tixNodup r := by
    rw [setR_r]; split_ifs with hr
    · subst hr; rw [htix]; exact h.tixNodup r
    · exact h.tixNodup r
  tixDisj r r' hne := by
    rw [setR_r, setR_r]
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1; rw [htix]; exact h.tixDisj r r' hne
    · subst h2; rw [htix]; exact h.tixDisj r r' hne
    · exact h.tixDisj r r' hne

/-- A receiver working on a buffer holds the buffer's ticket and has seen its
publication. -/
theorem Inv.onBuf {c : Cfg ρ} (h : Inv pay ln c) {r : ρ} {i : ℕ}
    (hr : (c.r r).pc.onBuf = some i) :
    ∃ s o, PhaseOK pay ln c i (.pub s) ∧ IsLatest (c.mem (.own i)) o ∧ o.val = some 1 ∧
      RecvOK pay ln c i s o r := by
  obtain ⟨ph, hph⟩ := h.phase i
  match ph, hph with
  | .free, hph' => exact absurd hr (hph'.2.2.1 r)
  | .fill, hph' => exact absurd hr (hph'.2.1 r)
  | .sealing, hph' => exact absurd hr (hph'.2.1 r)
  | .pub s, hph' =>
    obtain ⟨_, _, _, _, _, o, q, ho, hov, _, _, _, _, _, _, _, hrecv, _⟩ := id hph'
    exact ⟨s, o, hph', ho, hov, hrecv r hr⟩

theorem Inv.ticket_nonneg {c : Cfg ρ} (h : Inv pay ln c) {r : ρ} {t : ℤ}
    (hr : t ∈ (c.r r).pc.held) : 0 ≤ t :=
  (h.rTix r t (tix_held hr)).1

theorem Frame0.recv {c : Cfg ρ} {r0 : ρ} {σ : RState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc} {i : ℕ}
    (hown : M' (.own i) = c.mem (.own i)) (hlen : M' (.len i) = c.mem (.len i))
    (hcseq : M' (.cseq i) = c.mem (.cseq i)) (hchunk : M' (.chunk i) = c.mem (.chunk i))
    (hv : c.vr r0 ≤ 𝓥.cur) (hlog : ∀ e ∈ (c.r r0).log, e ∈ σ.log) :
    Frame0 c (c.setR r0 σ 𝓥 M' 𝓝') i where
  own := by simpa using hown
  len := by simpa using hlen
  cseq := by simpa using hcseq
  chunk := by simpa using hchunk
  vs l := by simp
  vr r l := by
    rw [setR_vr]; split_ifs with h
    · subst h; exact hv l
    · exact le_rfl
  fill := by simp
  sealing := by simp
  pc := by simp
  npub := by simp
  cons v h := consumed_setR hlog h

omit [DecidableEq ρ] in
theorem RecvOK.of_le {c : Cfg ρ} {i s : ℕ} {o o' : MsgT} {r : ρ} (h : RecvOK pay ln c i s o r)
    (ht : o'.time ≤ o.time) : RecvOK pay ln c i s o' r :=
  ⟨h.1, ht.trans h.2.1, h.2.2⟩

/-! ## `scan`: `client_seq[i].load(Acquire)` -/

theorem inv_r_scan {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {t : ℤ} {j : ℕ}
    (hpc : (c.r r0).pc = .scan t j) {σ : RState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  have hv : c.vr r0 ≤ 𝓥.cur := hst.cur_le
  obtain ⟨m, hm, tr, -, -, -, hσ, h𝓥, rfl, hpost⟩ :=
    hst.read_inv (l := .cseq j) (o := .acqrel) (by simp only [rprog, hpc]; rfl)
  simp only [DrfPostRead, MemOrder.rlx_le_acqrel, ↓reduceIte] at hpost
  obtain ⟨rfl, -⟩ := hpost
  obtain ⟨v, hmv⟩ := Option.isSome_iff_exists.1 (h.atomVal _ (by simp [Loc.IsChunk]) m hm)
  simp only [hmv] at hσ
  have hnaC : ∀ i, (addARead c.na (.cseq j) tr (.chunk i)) = c.na (.chunk i) :=
    fun i => addARead_ne _ _ (by simp)
  have hnaA : ∀ l, ¬ l.IsChunk → (addARead c.na (.cseq j) tr l).w = (c.na l).w ∧
      (addARead c.na (.cseq j) tr l).nr = (c.na l).nr := by
    intro l _
    by_cases hl : l = .cseq j
    · subst hl; simp
    · simp [hl]
  have hheld : t ∈ (c.r r0).pc.held := by simp [hpc, RPc.held]
  have ht0 : 0 ≤ t := h.ticket_nonneg pay ln hheld
  have hnc : ¬ Consumed c t := h.held_not_consumed pay ln hheld
  have common : ∀ σ' : RState, σ'.log = (c.r r0).log → σ'.pc.held = [t] →
      σ'.pc ≠ .fault ∧ (∀ t' i, σ'.pc ≠ .rel t' i) ∧ tix σ' = tix (c.r r0) := by
    intro σ' h1 h2
    refine ⟨fun h3 => by rw [h3] at h2; simp [RPc.held] at h2,
      fun t' i h3 => by rw [h3] at h2; simp [RPc.held] at h2, ?_⟩
    rw [tix, tix, h1, h2, hpc]; rfl
  by_cases hvt : v = t
  · -- the ticket matches: buffer `j` is published with sequence number `t`
    subst hvt
    simp only [↓reduceIte] at hσ
    subst hσ
    obtain ⟨c1, c2, c3⟩ := common { c.r r0 with pc := .own v j } rfl (by simp [RPc.held])
    have hno : ∀ i, NoLive c i → m ∈ c.mem (.cseq i) → False := by
      intro i hnl hmi
      rcases hnl m hmi v hmv with h1 | h1
      · rw [h1, NO_SEQ] at ht0; omega
      · exact hnc h1
    obtain ⟨phj, hphj⟩ := h.phase j
    obtain ⟨s, hs⟩ : ∃ s : ℕ, PhaseOK pay ln c j (.pub s) ∧ v = s ∧
        ∃ q, IsLatest (c.mem (.cseq j)) q ∧ m = q := by
      match phj, hphj with
      | .free, hphj' => exact (hno j hphj'.2.2.2.1 hm).elim
      | .fill, hphj' => exact (hno j hphj'.2.2.1 hm).elim
      | .sealing, hphj' => exact (hno j hphj'.2.2.1 hm).elim
      | .pub s, hphj' =>
        obtain ⟨_, _, _, _, _, o, q, _, _, _, hq, hqv, _, _, _, hq4, _, _⟩ := id hphj'
        rcases hq4 m hm v hmv with h1 | h1 | h1
        · rw [h1, NO_SEQ] at ht0; omega
        · exact (hnc h1).elim
        · have hmq : m = q := hq.eq_of_le (h.gen.uniq _) hm (le_of_eq h1.symm)
          rw [hmq, hqv, Option.some.injEq] at hmv
          exact ⟨s, hphj', hmv.symm, q, hq, hmq⟩
    obtain ⟨hphj, rfl, q, hq, rfl⟩ := hs
    -- what the acquire load gives the receiver
    have hacq : m.view.getD ⊥ ≤ 𝓥.cur := by rw [h𝓥]; exact readTView_R_le _ _ _ (by decide)
    refine h.recv_noWrite pay ln hg (fun i => by simp) hnaA c1 (fun t' i h => absurd h (c2 t' i))
      c3 (fun e he => h.rLog r0 e he) (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      refine ⟨.pub s, hphj.pub_frame pay ln (Frame0.recv rfl rfl rfl rfl hv (fun e he => he))
        ?_ ?_ ?_ ?_⟩
      · intro r hr
        rw [setR_r]; split_ifs with h1
        · subst h1; simpa [hpc, RPc.ticket] using hr
        · exact hr
      · intro o ho hov hot r hr
        rw [setR_r] at hr ⊢
        split_ifs at hr ⊢ with h1
        · subst h1
          obtain ⟨-, -, -, -, -, o', q', ho', -, -, hq', hq'v, hqc, hql, hqo, -⟩ := id hphj
          have hqq : q' = m := hq.eq_of_le (h.gen.uniq _) hq'.1 (hq'.2 m hq.1)
          subst hqq
          have hoo : o.time ≤ o'.time := ho'.2 o ho.1
          right
          refine ⟨by simp [RPc.ticket], ?_, ?_, ?_, by simp, by simp⟩
          · rw [setR_vr, if_pos rfl]
            exact hoo.trans (hqo.trans (hacq _).1)
          · rw [setR_vr, if_pos rfl]; simpa using hqc.mono (hacq _).1
          · rw [setR_vr, if_pos rfl]; simpa using hql.mono (hacq _).1
        · exact Or.inl rfl
      · intro id hid; left; simpa [hnaC] using hid
      · intro hc; exact absurd ((consumed_setR_same (by rfl)).1 hc) hnc
    · obtain ⟨ph, hph⟩ := h.phase i
      refine ⟨ph, hph.recv_frame pay ln (Frame.recv rfl rfl rfl rfl (by simp) hv
        (fun e he => he) ?_ ?_) ?_ (fun s' _ hc => (consumed_setR_same (by rfl)).1 hc)⟩
      · intro h1; simp [RPc.onBuf] at h1; exact absurd h1.symm hij
      · intro h1; simp [hpc, RPc.onBuf] at h1
      · intro s' _ h1; simpa [hpc, RPc.ticket] using h1
  · -- no match: move on
    simp only [hvt, ↓reduceIte] at hσ
    subst hσ
    obtain ⟨c1, c2, c3⟩ := common { c.r r0 with pc := .scan t ((j + 1) % N) } rfl
      (by simp [RPc.held])
    refine h.recv_noWrite pay ln hg (fun i => by simp) hnaA c1 (fun t' i h => absurd h (c2 t' i))
      c3 (fun e he => h.rLog r0 e he) (fun i => ?_)
    obtain ⟨ph, hph⟩ := h.phase i
    refine ⟨ph, hph.recv_frame pay ln (Frame.recv rfl rfl rfl rfl (by simp) hv
      (fun e he => he) ?_ ?_) ?_ (fun s' _ hc => (consumed_setR_same (by rfl)).1 hc)⟩
    · intro h1; simp [RPc.onBuf] at h1
    · intro h1; simp [hpc, RPc.onBuf] at h1
    · intro s' _ h1; simpa [hpc, RPc.ticket] using h1

/-! ## Steps on the receiver's buffer -/

/-- A receiver step that does not write memory, taken by the receiver working
on buffer `j` (published with `s`), which it keeps working on (or leaves). -/
theorem Inv.recv_onBuf {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {j s : ℕ} {o : MsgT}
    {σ : RState} {𝓥 : TView Loc} {𝓝' : View Loc}
    (hphj : PhaseOK pay ln c j (.pub s)) (ho : IsLatest (c.mem (.own j)) o)
    (hg : GenInv (c.setR r0 σ 𝓥 c.mem 𝓝'))
    (hnaC : ∀ i, (𝓝' (.chunk i)).w = (c.na (.chunk i)).w ∧
      (𝓝' (.chunk i)).aw = (c.na (.chunk i)).aw ∧ (𝓝' (.chunk i)).ar = (c.na (.chunk i)).ar)
    (hnaCi : ∀ i, i ≠ j → 𝓝' (.chunk i) = c.na (.chunk i))
    (hnaA : ∀ l, ¬ l.IsChunk → (𝓝' l).w = (c.na l).w ∧ (𝓝' l).nr = (c.na l).nr)
    (hnaJ : ∀ id ∈ (𝓝' (.chunk j)).nr, id ∈ (c.na (.chunk j)).nr ∨ id ∈ (𝓥.cur (.chunk j)).nr)
    (hv : c.vr r0 ≤ 𝓥.cur)
    (htk0 : (c.r r0).pc.ticket = some (s : ℤ)) (htk : σ.pc.ticket = some (s : ℤ))
    (hlog : ∀ e ∈ (c.r r0).log, e ∈ σ.log)
    (hon : ∀ i, σ.pc.onBuf = some i → i = j)
    (hokj : σ.pc.onBuf = some j → RecvOK pay ln (c.setR r0 σ 𝓥 c.mem 𝓝') j s o r0)
    (hfault : σ.pc ≠ .fault) (hrel : ∀ t i, σ.pc = .rel t i → t ∈ σ.log.map Prod.fst)
    (htix : tix σ = tix (c.r r0))
    (hrlog : ∀ e ∈ σ.log, 0 ≤ e.1 ∧ e.1 < c.s.pc.npub ∧ e.2.1 = pay e.1.toNat ∧
      e.2.2 = ln e.1.toNat)
    (hon0 : (c.r r0).pc.onBuf = some j)
    (hconsO : ∀ v, Consumed (c.setR r0 σ 𝓥 c.mem 𝓝') v → Consumed c v ∨ v = s)
    (hrelc : Consumed (c.setR r0 σ 𝓥 c.mem 𝓝') (s : ℤ) →
      ∃ r, ((c.setR r0 σ 𝓥 c.mem 𝓝').r r).pc = .rel (s : ℤ) j) :
    Inv pay ln (c.setR r0 σ 𝓥 c.mem 𝓝') := by
  refine h.recv_noWrite pay ln hg hnaC hnaA hfault hrel htix hrlog (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    refine ⟨.pub s, hphj.pub_frame pay ln (Frame0.recv rfl rfl rfl rfl hv hlog) ?_ ?_ ?_
      hrelc⟩
    · intro r hr
      rw [setR_r]; split_ifs with h1
      · exact htk
      · exact hr
    · intro o' ho' _ _ r hr
      rw [setR_r] at hr ⊢
      split_ifs at hr ⊢ with h1
      · subst h1; right; exact (hokj hr).of_le pay ln (ho.2 o' ho'.1)
      · exact Or.inl rfl
    · intro id hid
      rcases hnaJ id hid with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨r0, by simpa using htk, by simpa using h1⟩
  · obtain ⟨ph, hph⟩ := h.phase i
    refine ⟨ph, hph.recv_frame pay ln (Frame.recv rfl rfl rfl rfl (by rw [hnaCi i hij]) hv hlog
      ?_ ?_) ?_ ?_⟩
    · intro h1; exact absurd (hon i h1) hij
    · intro h1; rw [hon0, Option.some.injEq] at h1; exact absurd h1.symm hij
    · intro s' _ h1; rw [htk0] at h1; rw [htk, h1]
    · -- the one sequence number consumed now is not the one of buffer `i`
      intro s' hs' hc
      rcases hconsO _ hc with h1 | h1
      · exact h1
      · subst hs'
        obtain ⟨-, -, -, -, -, -, qi, -, -, -, hqi, hqiv, -⟩ := hph
        obtain ⟨-, -, -, -, -, -, qj, -, -, -, hqj, hqjv, -⟩ := hphj
        have := h.cseqUniq i j qi hqi.1 qj hqj.1 _ hqiv (by rw [hqjv, h1])
          (by rw [NO_SEQ]; omega)
        exact absurd this hij

/-- The data of the receiver working on a buffer. -/
theorem Inv.onBuf' {c : Cfg ρ} (h : Inv pay ln c) {r : ρ} {t : ℤ} {i : ℕ}
    (hr : (c.r r).pc.onBuf = some i) (ht : (c.r r).pc.ticket = some t) :
    ∃ s : ℕ, t = s ∧ ∃ o, PhaseOK pay ln c i (.pub s) ∧ IsLatest (c.mem (.own i)) o ∧
      o.val = some 1 ∧ RecvOK pay ln c i s o r := by
  obtain ⟨s, o, h1, h2, h3, h4⟩ := h.onBuf pay ln hr
  refine ⟨s, ?_, o, h1, h2, h3, h4⟩
  have := h4.1; rw [ht, Option.some.injEq] at this; exact this

/-! ## `own`: the `debug_assert` -/

theorem inv_r_own {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {t : ℤ} {j : ℕ}
    (hpc : (c.r r0).pc = .own t j) {σ : RState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  have hv : c.vr r0 ≤ 𝓥.cur := hst.cur_le
  obtain ⟨m, hm, tr, hle, -, -, hσ, -, rfl, hpost⟩ :=
    hst.read_inv (l := .own j) (o := .rlx) (by simp only [rprog, hpc]; rfl)
  simp only [DrfPostRead, MemOrder.rlx_le_rlx, ↓reduceIte] at hpost
  obtain ⟨rfl, -⟩ := hpost
  obtain ⟨s, rfl, o, hphj, ho, hov, hok⟩ :=
    h.onBuf' pay ln (r := r0) (t := t) (i := j) (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
  -- the receiver reads `client_owned[j] = true`
  have hmo : m = o := ho.eq_of_le (h.gen.uniq _) hm (hok.2.1.trans hle)
  rw [hmo, hov] at hσ
  simp only [one_ne_zero, ↓reduceIte] at hσ
  subst hσ
  have hnaA : ∀ l, ¬ l.IsChunk → (addARead c.na (.own j) tr l).w = (c.na l).w ∧
      (addARead c.na (.own j) tr l).nr = (c.na l).nr := by
    intro l _
    by_cases hl : l = .own j
    · subst hl; simp
    · simp [hl]
  obtain ⟨k1, k2, k3, k4, -, -⟩ := hok
  refine h.recv_onBuf pay ln hphj ho hg (fun i => by simp) (fun i _ => by simp) hnaA
    (fun id hid => Or.inl (by simpa using hid)) hv (by simp [hpc, RPc.ticket])
    (by simp [RPc.ticket]) (fun e he => he) (fun i hi => by simpa [RPc.onBuf] using hi.symm)
    (fun _ => ?_) (by simp) (fun t i h => by simp at h) (by simp [tix, hpc, RPc.held])
    (fun e he => h.rLog r0 e he)
    (by simp [hpc, RPc.onBuf]) (fun v hc => Or.inl ((consumed_setR_same (by rfl)).1 hc))
    (fun hc => absurd ((consumed_setR_same (by rfl)).1 hc)
      (h.held_not_consumed pay ln (r := r0) (by simp [hpc, RPc.held])))
  refine ⟨by simp [RPc.ticket], ?_, ?_, ?_, by simp, by simp⟩
  · simpa using k2.trans (hv _).1
  · simpa using k3.mono (hv _).1
  · simpa using k4.mono (hv _).1

/-! ## `len`: `client_len[i].load(Relaxed)` -/

theorem inv_r_len {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {t : ℤ} {j : ℕ}
    (hpc : (c.r r0).pc = .len t j) {σ : RState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  have hv : c.vr r0 ≤ 𝓥.cur := hst.cur_le
  obtain ⟨m, hm, tr, hle, -, -, hσ, -, rfl, hpost⟩ :=
    hst.read_inv (l := .len j) (o := .rlx) (by simp only [rprog, hpc]; rfl)
  simp only [DrfPostRead, MemOrder.rlx_le_rlx, ↓reduceIte] at hpost
  obtain ⟨rfl, -⟩ := hpost
  obtain ⟨s, rfl, o, hphj, ho, hov, hok⟩ :=
    h.onBuf' pay ln (r := r0) (t := t) (i := j) (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
  -- the receiver reads the length of this publication
  have hml : m.val = some (ln s) := by
    obtain ⟨-, -, -, -, hc2, -⟩ := hphj
    exact hc2.read (h.gen.uniq _) hok.2.2.2.1 hm hle
  rw [hml] at hσ
  subst hσ
  have hnaA : ∀ l, ¬ l.IsChunk → (addARead c.na (.len j) tr l).w = (c.na l).w ∧
      (addARead c.na (.len j) tr l).nr = (c.na l).nr := by
    intro l _
    by_cases hl : l = .len j
    · subst hl; simp
    · simp [hl]
  obtain ⟨k1, k2, k3, k4, -, -⟩ := hok
  refine h.recv_onBuf pay ln hphj ho hg (fun i => by simp) (fun i _ => by simp) hnaA
    (fun id hid => Or.inl (by simpa using hid)) hv (by simp [hpc, RPc.ticket])
    (by simp [RPc.ticket]) (fun e he => he) (fun i hi => by simpa [RPc.onBuf] using hi.symm)
    (fun _ => ?_) (by simp) (fun t i h => by simp at h) (by simp [tix, hpc, RPc.held])
    (fun e he => h.rLog r0 e he)
    (by simp [hpc, RPc.onBuf]) (fun v hc => Or.inl ((consumed_setR_same (by rfl)).1 hc))
    (fun hc => absurd ((consumed_setR_same (by rfl)).1 hc)
      (h.held_not_consumed pay ln (r := r0) (by simp [hpc, RPc.held])))
  refine ⟨by simp [RPc.ticket], ?_, ?_, ?_, fun t n hn => ?_, by simp⟩
  · simpa using k2.trans (hv _).1
  · simpa using k3.mono (hv _).1
  · simpa using k4.mono (hv _).1
  · simp only [Cfg.setR_r_self, RPc.chunk.injEq] at hn; exact hn.2.2.symm

/-! ## `chunk`: the non-atomic read of the payload -/

theorem inv_r_chunk {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {t : ℤ} {j : ℕ} {n : ℤ}
    (hpc : (c.r r0).pc = .chunk t j n) {σ : RState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  have hv : c.vr r0 ≤ 𝓥.cur := hst.cur_le
  obtain ⟨m, hm, tr, hle, -, -, hσ, h𝓥, rfl, hpost⟩ :=
    hst.read_inv (l := .chunk j) (o := .na) (by simp only [rprog, hpc]; rfl)
  simp only [DrfPostRead, MemOrder.rlx_le_na, ↓reduceIte] at hpost
  obtain ⟨rfl, -⟩ := hpost
  obtain ⟨s, rfl, o, hphj, ho, hov, hok⟩ :=
    h.onBuf' pay ln (r := r0) (t := t) (i := j) (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
  -- the receiver reads the payload of this publication
  have hmp : m.val = some (pay s) := by
    obtain ⟨-, -, -, hc1, -⟩ := hphj
    exact hc1.read (h.gen.uniq _) hok.2.2.1 hm hle
  rw [hmp] at hσ
  subst hσ
  have htr : tr ∈ (𝓥.cur (.chunk j)).nr := by
    rw [h𝓥]
    exact TimeInfo.nr_mono (View.le_apply (readTView_V_le _ _ _ _) _) (by simp)
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := hok
  have hn : n = ln s := k5 _ _ hpc
  refine h.recv_onBuf pay ln hphj ho hg (fun i => ?_) (fun i hij => ?_) (fun l hl => ?_)
    (fun id hid => ?_) hv (by simp [hpc, RPc.ticket])
    (by simp [RPc.ticket]) (fun e he => he) (fun i hi => by simpa [RPc.onBuf] using hi.symm)
    (fun _ => ?_) (by simp) (fun t i h => by simp at h) (by simp [tix, hpc, RPc.held])
    (fun e he => h.rLog r0 e he)
    (by simp [hpc, RPc.onBuf]) (fun v hc => Or.inl ((consumed_setR_same (by rfl)).1 hc))
    (fun hc => absurd ((consumed_setR_same (by rfl)).1 hc)
      (h.held_not_consumed pay ln (r := r0) (by simp [hpc, RPc.held])))
  · by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · simp [hij]
  · have : l ≠ .chunk j := by rintro rfl; exact hl trivial
    simp [this]
  · simp only [addNRead_self, Finset.mem_insert] at hid
    rcases hid with rfl | hid
    · exact Or.inr htr
    · exact Or.inl hid
  · refine ⟨by simp [RPc.ticket], ?_, ?_, ?_, by simp, fun t' n' p' hp => ?_⟩
    · simpa using k2.trans (hv _).1
    · simpa using k3.mono (hv _).1
    · simpa using k4.mono (hv _).1
    · simp only [Cfg.setR_r_self, RPc.cb.injEq] at hp
      obtain ⟨-, -, rfl, rfl⟩ := hp
      exact ⟨hn, rfl⟩

/-! ## `cb`: the callback returns `Ok` or `Err` -/

theorem inv_r_cb {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {t : ℤ} {j : ℕ} {n p : ℤ}
    (hpc : (c.r r0).pc = .cb t j n p) {σ : RState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  obtain ⟨ok, rfl, rfl, rfl, rfl⟩ := hst.choose_inv (by simp only [rprog, hpc]; rfl)
  obtain ⟨s, rfl, o, hphj, ho, hov, hok⟩ :=
    h.onBuf' pay ln (r := r0) (t := t) (i := j) (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
  obtain ⟨k1, k2, k3, k4, -, k6⟩ := hok
  obtain ⟨hn, hp⟩ := k6 _ _ _ hpc
  subst hn hp
  have hnp : s < c.s.pc.npub := hphj.2.2.1
  cases ok with
  | true =>
    simp only [↓reduceIte]
    refine h.recv_onBuf pay ln hphj ho hg (fun i => by simp) (fun i _ => rfl)
      (fun l _ => ⟨rfl, rfl⟩) (fun id hid => Or.inl hid) le_rfl (by simp [hpc, RPc.ticket])
      (by simp [RPc.ticket]) (fun e he => List.mem_cons_of_mem _ he)
      (fun i hi => by simpa [RPc.onBuf] using hi.symm) (fun _ => ?_) (by simp)
      (fun t' i h => by simp at h; obtain ⟨rfl, -⟩ := h; simp)
      (by simp [tix, hpc, RPc.held]) (fun e he => ?_) (by simp [hpc, RPc.onBuf]) ?_
      (fun _ => ⟨r0, by simp⟩)
    · refine ⟨by simp [RPc.ticket], ?_, ?_, ?_, by simp, by simp⟩
      · simp only [Cfg.setR_vr_self]; exact k2
      · simp only [Cfg.setR_vr_self, Cfg.setR_mem]; exact k3
      · simp only [Cfg.setR_vr_self, Cfg.setR_mem]; exact k4
    · simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨by omega, by simpa using hnp, by simp, by simp⟩
      · exact h.rLog r0 e he
    · -- only the ticket of this buffer becomes consumed
      rintro v ⟨r, hr⟩
      rw [setR_r] at hr
      split_ifs at hr with h1
      · subst h1
        simp only [List.map_cons, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact Or.inr rfl
        · exact Or.inl ⟨r, hr⟩
      · exact Or.inl ⟨r, hr⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine h.recv_onBuf pay ln hphj ho hg (fun i => by simp) (fun i _ => rfl)
      (fun l _ => ⟨rfl, rfl⟩) (fun id hid => Or.inl hid) le_rfl (by simp [hpc, RPc.ticket])
      (by simp [RPc.ticket]) (fun e he => he)
      (fun i hi => by simp [RPc.onBuf] at hi) (fun hi => by simp [RPc.onBuf] at hi) (by simp)
      (fun t' i h => by simp at h)
      (by simp [tix, hpc, RPc.held]) (fun e he => h.rLog r0 e he)
      (by simp [hpc, RPc.onBuf]) (fun v hc => Or.inl ((consumed_setR_same (by rfl)).1 hc))
      (fun hc => absurd ((consumed_setR_same (by rfl)).1 hc)
        (h.held_not_consumed pay ln (r := r0) (by simp [hpc, RPc.held])))

/-! ## `rel`: `client_owned[i].store(false, Release)` -/

theorem inv_r_rel {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {t : ℤ} {j : ℕ}
    (hpc : (c.r r0).pc = .rel t j) {σ : RState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  have hv : c.vr r0 ≤ 𝓥.cur := hst.cur_le
  obtain ⟨t', -, hlt, -, rfl, rfl, hM, -, hpost⟩ :=
    hst.write_inv (l := .own j) (o := .acqrel) (v := 0) (by simp only [rprog, hpc]; rfl)
  simp only [DrfPostWrite, MemOrder.rlx_le_acqrel, ↓reduceIte] at hpost
  subst hpost
  rw [← vr_def] at hlt
  have hfv' : c.vr r0 ≤ (writeRw (c.th (.recv r0)).2 .acqrel (.own j) t' ⊥).getD ⊥ :=
    writeRw_rel (o := .acqrel) (by decide)
  obtain ⟨f, hft, hfval, hfv, rfl⟩ : ∃ f : MsgT, f.time = t' ∧ f.val = some 0 ∧
      c.vr r0 ≤ f.view.getD ⊥ ∧ M' = c.mem.add (.own j) f := ⟨_, rfl, rfl, hfv', hM⟩
  obtain ⟨s, rfl, o, hphj, ho, hov, hok⟩ :=
    h.onBuf' pay ln (r := r0) (t := t) (i := j) (by simp [hpc, RPc.onBuf])
      (by simp [hpc, RPc.ticket])
  have htk0 : (c.r r0).pc.ticket = some (s : ℤ) := by simp [hpc, RPc.ticket]
  have hlogged : (s : ℤ) ∈ (c.r r0).log.map Prod.fst := h.rRel r0 _ j hpc
  have hmem : ∀ l, l ≠ .own j → c.mem.add (.own j) f l = c.mem l :=
    fun l hl => Memory.add_ne _ _ hl
  have hnaC : ∀ i, addAWrite c.na (.own j) t' (.chunk i) = c.na (.chunk i) := fun i => by simp
  have NC : ∀ i, Loc.chunk i ≠ .own j ∧ Loc.len i ≠ .own j ∧ Loc.cseq i ≠ .own j :=
    fun i => ⟨by simp, by simp, by simp⟩
  have htix : tix { c.r r0 with pc := .init } = tix (c.r r0) := by
    simp [tix, hpc, RPc.held]
  have hcons : ∀ v, Consumed c v →
      Consumed (c.setR r0 { c.r r0 with pc := .init } (writeTView (c.th (.recv r0)).2 .acqrel (.own j) t')
        (c.mem.add (.own j) f) (addAWrite c.na (.own j) t')) v :=
    fun v hv => consumed_setR (σ := { c.r r0 with pc := .init }) (fun e he => he) hv
  refine
  { gen := hg
    phase := fun i => ?_
    chunkS := fun i => by simpa [hmem _ (NC i).1] using h.chunkS i
    chunkNa := fun i => by simpa [hmem _ (NC i).1] using h.chunkNa i
    chunkAt := fun i => by simpa using h.chunkAt i
    atomNa := fun l hl => by
      by_cases hl' : l = .own j
      · subst hl'; simpa using h.atomNa _ hl
      · simpa [hl'] using h.atomNa l hl
    atomVal := fun l hl m hm => by
      simp only [Cfg.setR_mem] at hm
      rcases Memory.mem_add.1 hm with ⟨-, he⟩ | hm
      · rw [he, hfval]; rfl
      · exact h.atomVal l hl m hm
    lenS := fun i => by simpa [hmem _ (NC i).2.1] using h.lenS i
    cseqS := fun i => by simpa [hmem _ (NC i).2.2] using h.cseqS i
    cseqVal := fun i => by simpa [hmem _ (NC i).2.2] using h.cseqVal i
    cseqUniq := fun i i' => by simpa [hmem _ (NC i).2.2, hmem _ (NC i').2.2] using h.cseqUniq i i'
    curSeqVal := by simpa [hmem] using h.curSeqVal
    curSeqDown := by simpa [hmem] using h.curSeqDown
    curSeqTop := by simpa [hmem] using h.curSeqTop
    curSeqHas := by simpa [hmem] using h.curSeqHas
    tickVal := by simpa [hmem] using h.tickVal
    tickDown := by simpa [hmem] using h.tickDown
    sFault := by simpa using h.sFault
    sPub := by simpa using h.sPub
    sLog := by simpa using h.sLog
    rFault := fun r => by
      rw [setR_r]; split_ifs with hr
      · simp
      · exact h.rFault r
    rRel := fun r => by
      rw [setR_r]; split_ifs with hr
      · intro t i h; simp at h
      · exact h.rRel r
    rTix := fun r => by
      rw [setR_r]; split_ifs with hr
      · subst hr; rw [htix]; simpa [hmem] using h.rTix r
      · simpa [hmem] using h.rTix r
    rLog := fun r => by
      rw [setR_r]; split_ifs with hr
      · subst hr; simpa using h.rLog r
      · simpa using h.rLog r
    tixNodup := fun r => by
      rw [setR_r]; split_ifs with hr
      · subst hr; rw [htix]; exact h.tixNodup r
      · exact h.tixNodup r
    tixDisj := fun r r' hne => by
      rw [setR_r, setR_r]
      split_ifs with h1 h2 h2
      · exact absurd (h1.trans h2.symm) hne
      · subst h1; rw [htix]; exact h.tixDisj r r' hne
      · subst h2; rw [htix]; exact h.tixDisj r r' hne
      · exact h.tixDisj r r' hne }
  by_cases hij : i = j
  · -- the buffer is free again
    subst hij
    obtain ⟨hf, hs, -, -, -, o', q, ho', -, hot, hq, hqv, -, -, -, hq4, hrecv, hnr, -⟩ :=
      id hphj
    have hoo : o' = o := ho.eq_of_le (h.gen.uniq _) ho'.1 (ho'.2 o ho.1)
    rw [hoo] at hot
    refine ⟨.free, by simpa using hf, by simpa using hs, ?_, ?_, f, ?_, hfval, ?_, ?_⟩
    · -- no receiver works on the buffer any more
      intro r hr
      rw [setR_r] at hr
      split_ifs at hr with h1
      · simp [RPc.onBuf] at hr
      · obtain ⟨k1, -⟩ := hrecv r hr
        exact h1 (h.ticket_unique pay ln k1 htk0)
    · -- its sequence number has been consumed
      intro m hm v hv'
      simp only [Cfg.setR_mem, hmem _ (NC i).2.2] at hm
      rcases hq4 m hm v hv' with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (hcons v h1)
      · have hmq : m = q := h.gen.uniq _ m hm q hq.1 h1
        rw [hmq, hqv, Option.some.injEq] at hv'
        subst hv'
        exact Or.inr ⟨r0, by simpa using hlogged⟩
    · simp only [Cfg.setR_mem, Memory.add_self]
      exact isLatest_cons_new (ho.below.mono hok.2.1) (hft ▸ hlt)
    · -- the sender can only read the new `false`
      intro m hm hle hv'
      simp only [Cfg.setR_mem, Memory.add_self, List.mem_cons, Cfg.setR_vs] at hm hle
      rcases hm with he | hm
      · rw [he]
      · have hmo : m = o := ho.eq_of_le (h.gen.uniq _) hm (hot.trans hle)
        rw [hmo, hov] at hv'; cases hv'
    · -- every read of the chunk is in the sender's view or in the new message's view
      intro id hid
      simp only [Cfg.setR_na, hnaC, Cfg.setR_vs] at hid ⊢
      rcases hnr id hid with h1 | ⟨r, hr1, hr2⟩
      · exact Finset.mem_union_left _ h1
      · have := h.ticket_unique pay ln hr1 htk0
        subst this
        exact Finset.mem_union_right _ ((hfv _).2.2.1 hr2)
  · obtain ⟨ph, hph⟩ := h.phase i
    refine ⟨ph, hph.recv_frame pay ln (Frame.recv (by simp [hij]) (by simp) (by simp)
      (by simp) (by simp) hv (fun e he => he) (fun h1 => by simp [RPc.onBuf] at h1)
      (fun h1 => by rw [hpc] at h1; simp [RPc.onBuf] at h1; exact absurd h1.symm hij)) ?_
      (fun s' _ hc => (consumed_setR_same (by rfl)).1 hc)⟩
    -- the ticket this receiver gives up is not the one of another buffer
    intro s' hs' h1
    subst hs'
    rw [htk0, Option.some.injEq] at h1
    obtain ⟨-, -, -, -, -, -, qi, -, -, -, hqi, hqiv, -⟩ := hph
    obtain ⟨-, -, -, -, -, -, qj, -, -, -, hqj, hqjv, -⟩ := hphj
    have := h.cseqUniq i j qi hqi.1 qj hqj.1 _ hqiv (by rw [hqjv, h1])
      (by rw [NO_SEQ]; omega)
    exact absurd this hij

/-! ## `init`: `request_ticket`, `seq.fetch_add(1, Relaxed)` -/

theorem inv_r_init {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ}
    (hpc : (c.r r0).pc = .init) {σ : RState} {𝓥 : TView Loc} {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  have hv : c.vr r0 ≤ 𝓥.cur := hst.cur_le
  obtain ⟨m1, hm1, v, tr, hv1, -, -, hfresh, -, -, hσ, -, hM, -, hpost⟩ :=
    hst.update_inv (l := .tick) (or := .rlx) (ow := .rlx) (f := (· + 1))
      (by simp only [rprog, hpc]; rfl)
  obtain ⟨rfl, -⟩ := hpost
  subst hσ
  -- the update reads the latest ticket counter
  have hlatest : ∀ m ∈ c.mem .tick, m.time ≤ m1.time := by
    intro m hm
    by_contra hlt
    obtain ⟨m', hm', ht'⟩ := h.tickDown m hm (m1.time + 1) (by omega) (by omega)
    exact hfresh m' hm' ht'
  have hpos : 1 ≤ m1.time := h.gen.pos _ m1 hm1
  have hvv : v = (m1.time : ℤ) - 1 := by
    have := h.tickVal m1 hm1; rw [hv1, Option.some.injEq] at this; exact this
  obtain ⟨mnew, hmt, hmv, rfl⟩ : ∃ mnew : MsgT, mnew.time = m1.time + 1 ∧
      mnew.val = some (v + 1) ∧ M' = c.mem.add .tick mnew := ⟨_, rfl, rfl, hM⟩
  have hmem : ∀ l, l ≠ .tick → c.mem.add .tick mnew l = c.mem l :=
    fun l hl => Memory.add_ne _ _ hl
  -- every ticket handed out so far is smaller
  have hsmall : ∀ r, ∀ τ ∈ tix (c.r r), τ < v := by
    intro r τ hτ
    obtain ⟨-, m, hm, hmτ⟩ := h.rTix r τ hτ
    have h1 := h.tickVal m hm
    rw [hmτ, Option.some.injEq] at h1
    have h2 := hlatest m hm
    omega
  have htix : tix { c.r r0 with pc := .scan v 0 } = v :: tix (c.r r0) := by
    simp [tix, hpc, RPc.held]
  refine
  { gen := hg
    phase := fun i => ?_
    chunkS := fun i => by simpa [hmem] using h.chunkS i
    chunkNa := fun i => by simpa [hmem] using h.chunkNa i
    chunkAt := fun i => by simpa using h.chunkAt i
    atomNa := fun l hl => by
      by_cases hl' : l = .tick
      · subst hl'; simpa using h.atomNa _ hl
      · simpa [hl'] using h.atomNa l hl
    atomVal := fun l hl m hm => by
      simp only [Cfg.setR_mem] at hm
      rcases Memory.mem_add.1 hm with ⟨-, he⟩ | hm
      · rw [he, hmv]; rfl
      · exact h.atomVal l hl m hm
    lenS := fun i => by simpa [hmem] using h.lenS i
    cseqS := fun i => by simpa [hmem] using h.cseqS i
    cseqVal := fun i => by simpa [hmem] using h.cseqVal i
    cseqUniq := fun i i' => by simpa [hmem] using h.cseqUniq i i'
    curSeqVal := by simpa [hmem] using h.curSeqVal
    curSeqDown := by simpa [hmem] using h.curSeqDown
    curSeqTop := by simpa [hmem] using h.curSeqTop
    curSeqHas := by simpa [hmem] using h.curSeqHas
    tickVal := fun m hm => by
      simp only [Cfg.setR_mem, Memory.add_self, List.mem_cons] at hm
      rcases hm with he | hm
      · rw [he, hmv, hmt, hvv]; simp only [Option.some.injEq]; omega
      · exact h.tickVal m hm
    tickDown := fun m hm t' h1 h2 => by
      simp only [Cfg.setR_mem, Memory.add_self, List.mem_cons] at hm ⊢
      rcases hm with he | hm
      · rw [he, hmt] at h2
        by_cases ht' : t' = m1.time + 1
        · exact ⟨mnew, Or.inl rfl, by rw [hmt, ht']⟩
        · obtain ⟨m', hm', ht''⟩ := h.tickDown m1 hm1 t' h1 (by omega)
          exact ⟨m', Or.inr hm', ht''⟩
      · obtain ⟨m', hm', ht''⟩ := h.tickDown m hm t' h1 h2
        exact ⟨m', Or.inr hm', ht''⟩
    sFault := by simpa using h.sFault
    sPub := by simpa using h.sPub
    sLog := by simpa using h.sLog
    rFault := fun r => by
      rw [setR_r]; split_ifs with hr
      · simp
      · exact h.rFault r
    rRel := fun r => by
      rw [setR_r]; split_ifs with hr
      · intro t i h; simp at h
      · exact h.rRel r
    rTix := fun r τ hτ => by
      rw [setR_r] at hτ
      split_ifs at hτ with hr
      · subst hr
        rw [htix, List.mem_cons] at hτ
        rcases hτ with rfl | hτ
        · exact ⟨by omega, mnew, by simp, hmv⟩
        · obtain ⟨h1, m, hm, h2⟩ := h.rTix r τ hτ
          exact ⟨h1, m, by simp [hm], h2⟩
      · obtain ⟨h1, m, hm, h2⟩ := h.rTix r τ hτ
        exact ⟨h1, m, by simp [hm], h2⟩
    rLog := fun r => by
      rw [setR_r]; split_ifs with hr
      · subst hr; simpa using h.rLog r
      · simpa using h.rLog r
    tixNodup := fun r => by
      rw [setR_r]; split_ifs with hr
      · subst hr; rw [htix]
        exact List.nodup_cons.2 ⟨fun hm => lt_irrefl _ (hsmall r v hm), h.tixNodup r⟩
      · exact h.tixNodup r
    tixDisj := fun r r' hne => by
      rw [setR_r, setR_r]
      split_ifs with h1 h2 h2
      · exact absurd (h1.trans h2.symm) hne
      · subst h1; rw [htix]
        intro τ hτ
        rcases List.mem_cons.1 hτ with rfl | hτ
        · exact fun hm => lt_irrefl _ (hsmall r' τ hm)
        · exact h.tixDisj r r' hne τ hτ
      · subst h2; rw [htix]
        intro τ hτ hm
        rcases List.mem_cons.1 hm with rfl | hm
        · exact lt_irrefl _ (hsmall r τ hτ)
        · exact h.tixDisj r r' hne τ hτ hm
      · exact h.tixDisj r r' hne }
  obtain ⟨ph, hph⟩ := h.phase i
  refine ⟨ph, hph.recv_frame pay ln (Frame.recv (by simp) (by simp) (by simp)
    (by simp) (by simp) hv (fun e he => he) (fun h1 => by simp [RPc.onBuf] at h1)
    (fun h1 => by simp [hpc, RPc.onBuf] at h1)) ?_
    (fun s' _ hc => (consumed_setR_same (by rfl)).1 hc)⟩
  intro s' _ h1; simp [hpc, RPc.ticket] at h1

/-! ## All receiver steps -/

theorem inv_recv {c : Cfg ρ} (h : Inv pay ln c) {r0 : ρ} {σ : RState} {𝓥 : TView Loc}
    {M' : Mem} {𝓝' : View Loc}
    (hst : TStep (rprog N) (c.r r0) (c.th (.recv r0)).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hg : GenInv (c.setR r0 σ 𝓥 M' 𝓝')) : Inv pay ln (c.setR r0 σ 𝓥 M' 𝓝') := by
  cases hpc : (c.r r0).pc with
  | init => exact inv_r_init N pay ln h hpc hst hg
  | scan t i => exact inv_r_scan N pay ln h hpc hst hg
  | own t i => exact inv_r_own N pay ln h hpc hst hg
  | len t i => exact inv_r_len N pay ln h hpc hst hg
  | chunk t i n => exact inv_r_chunk N pay ln h hpc hst hg
  | cb t i n p => exact inv_r_cb N pay ln h hpc hst hg
  | rel t i => exact inv_r_rel N pay ln h hpc hst hg
  | fault => exact (hst.fault_inv (by simp [rprog, hpc])).elim

end Mempipe
