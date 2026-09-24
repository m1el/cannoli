import Mempipe.Invariant

/-!
# Frame lemma for the per-buffer invariant

A step that does not touch buffer `i`'s locations, only grows views, and
does not move any thread onto or off buffer `i` preserves its phase.
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ] (pay ln : ℕ → ℤ)

/-- Frame hypotheses about memory, views and the sender. -/
structure Frame0 (c c' : Cfg ρ) (i : ℕ) : Prop where
  own : c'.mem (.own i) = c.mem (.own i)
  len : c'.mem (.len i) = c.mem (.len i)
  cseq : c'.mem (.cseq i) = c.mem (.cseq i)
  chunk : c'.mem (.chunk i) = c.mem (.chunk i)
  vs : ∀ l, c.vs l ≤ c'.vs l
  vr : ∀ r l, c.vr r l ≤ c'.vr r l
  fill : c'.s.pc.fill = some i ↔ c.s.pc.fill = some i
  sealing : c'.s.pc.sealing = some i ↔ c.s.pc.sealing = some i
  pc : c'.s.pc.fill = some i ∨ c'.s.pc.sealing = some i → c'.s.pc = c.s.pc
  npub : c.s.pc.npub ≤ c'.s.pc.npub
  cons : ∀ v, Consumed c v → Consumed c' v

/-- Hypotheses of the frame lemma. -/
structure Frame (c c' : Cfg ρ) (i : ℕ) : Prop extends Frame0 c c' i where
  na : (c'.na (.chunk i)).nr = (c.na (.chunk i)).nr
  on : ∀ r, (c'.r r).pc.onBuf = some i → (c'.r r).pc = (c.r r).pc

theorem PhaseOK.frame {c c' : Cfg ρ} {i : ℕ} {ph : Phase}
    (h : PhaseOK pay ln c i ph) (F : Frame c c' i)
    (htk : ∀ s, ph = .pub s → ∀ r, (c.r r).pc.ticket = some (s : ℤ) →
      (c'.r r).pc.ticket = some (s : ℤ)) :
    PhaseOK pay ln c' i ph := by
  have noRecv : NoRecv c i → NoRecv c' i := fun h r hr => h r (F.on r hr ▸ hr)
  have noLive : NoLive c i → NoLive c' i := fun h m hm v hv => by
    rw [F.cseq] at hm
    rcases h m hm v hv with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (F.cons v h1)
  cases ph with
  | free =>
    obtain ⟨hf, hs, hnr, hnl, f, hfl, hfv, hf2, hf3⟩ := h
    refine ⟨fun h' => hf (F.fill.1 h'), fun h' => hs (F.sealing.1 h'), noRecv hnr,
      noLive hnl, f, F.own ▸ hfl, hfv, ?_, ?_⟩
    · intro m hm ht hv
      rw [F.own] at hm
      exact hf2 m hm ((F.vs _).1.trans ht) hv
    · rw [F.na]
      exact hf3.trans (Finset.union_subset_union (F.vs _).2.2.1 subset_rfl)
  | fill =>
    obtain ⟨hf, hnr, hnl, hb, hna, hc1, hc2⟩ := h
    have hpc : c'.s.pc = c.s.pc := F.pc (Or.inl (F.fill.2 hf))
    refine ⟨F.fill.2 hf, noRecv hnr, noLive hnl, ?_, ?_, ?_, ?_⟩
    · rw [F.own]; exact hb.mono (F.vs _).1
    · rw [F.na]; exact hna.trans (F.vs _).2.2.1
    · intro k b hk; rw [F.chunk]; exact hc1 k b (hpc ▸ hk)
    · intro k b hk; rw [F.chunk, F.len]; exact hc2 k b (hpc ▸ hk)
  | sealing =>
    obtain ⟨hs, hnr, hnl, hna, hc1, hc2, o, ho, hov, hot⟩ := h
    have hpc : c'.s.pc = c.s.pc := F.pc (Or.inr (F.sealing.2 hs))
    refine ⟨F.sealing.2 hs, noRecv hnr, noLive hnl, ?_, ?_, ?_, o, F.own ▸ ho, hov,
      hot.trans (F.vs _).1⟩
    · rw [F.na]; exact hna.trans (F.vs _).2.2.1
    · rw [F.chunk, hpc]; exact hc1
    · rw [F.len, hpc]; exact hc2
  | pub s =>
    obtain ⟨hf, hs, hnp, hc1, hc2, o, q, ho, hov, hot, hq, hqv, hqc, hql, hqo, hq4, hrecv,
      hnr⟩ := h
    refine ⟨fun h' => hf (F.fill.1 h'), fun h' => hs (F.sealing.1 h'),
      lt_of_lt_of_le hnp F.npub, F.chunk ▸ hc1, F.len ▸ hc2, o, q, F.own ▸ ho, hov,
      hot.trans (F.vs _).1, F.cseq ▸ hq, hqv, F.chunk ▸ hqc, F.len ▸ hql, hqo, ?_, ?_, ?_⟩
    · intro m hm v hv
      rw [F.cseq] at hm
      rcases hq4 m hm v hv with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (F.cons v h1))
      · exact Or.inr (Or.inr h1)
    · intro r hr
      have hpc := F.on r hr
      obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hrecv r (hpc ▸ hr)
      refine ⟨hpc ▸ t1, t2.trans (F.vr r _).1, ?_, ?_, fun t n h => t5 t n (hpc ▸ h),
        fun t n p h => t6 t n p (hpc ▸ h)⟩
      · rw [F.chunk]; exact t3.mono (F.vr r _).1
      · rw [F.len]; exact t4.mono (F.vr r _).1
    · intro id hid
      rw [F.na] at hid
      rcases hnr id hid with h1 | ⟨r, hr1, hr2⟩
      · exact Or.inl ((F.vs _).2.2.1 h1)
      · exact Or.inr ⟨r, htk s rfl r hr1, (F.vr r _).2.2.1 hr2⟩

/-- A variant for the published phase, for steps of the receiver working on
the buffer: receivers may change state on the buffer if they keep its facts,
and the race detector may record new chunk reads by the ticket's holder. -/
theorem PhaseOK.pub_frame {c c' : Cfg ρ} {i s : ℕ}
    (h : PhaseOK pay ln c i (.pub s)) (F : Frame0 c c' i)
    (htk : ∀ r, (c.r r).pc.ticket = some (s : ℤ) → (c'.r r).pc.ticket = some (s : ℤ))
    (hon : ∀ o, IsLatest (c.mem (.own i)) o → o.val = some 1 → o.time ≤ (c.vs (.own i)).w →
      ∀ r, (c'.r r).pc.onBuf = some i →
        (c'.r r).pc = (c.r r).pc ∨ RecvOK pay ln c' i s o r)
    (hna : ∀ id ∈ (c'.na (.chunk i)).nr, id ∈ (c.na (.chunk i)).nr ∨
      ∃ r, (c'.r r).pc.ticket = some (s : ℤ) ∧ id ∈ (c'.vr r (.chunk i)).nr) :
    PhaseOK pay ln c' i (.pub s) := by
  obtain ⟨hf, hs, hnp, hc1, hc2, o, q, ho, hov, hot, hq, hqv, hqc, hql, hqo, hq4, hrecv,
    hnr⟩ := h
  refine ⟨fun h' => hf (F.fill.1 h'), fun h' => hs (F.sealing.1 h'),
    lt_of_lt_of_le hnp F.npub, F.chunk ▸ hc1, F.len ▸ hc2, o, q, F.own ▸ ho, hov,
    hot.trans (F.vs _).1, F.cseq ▸ hq, hqv, F.chunk ▸ hqc, F.len ▸ hql, hqo, ?_, ?_, ?_⟩
  · intro m hm v hv
    rw [F.cseq] at hm
    rcases hq4 m hm v hv with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (F.cons v h1))
    · exact Or.inr (Or.inr h1)
  · intro r hr
    rcases hon o ho hov hot r hr with hpc | hok
    · obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hrecv r (hpc ▸ hr)
      refine ⟨hpc ▸ t1, t2.trans (F.vr r _).1, ?_, ?_, fun t n h => t5 t n (hpc ▸ h),
        fun t n p h => t6 t n p (hpc ▸ h)⟩
      · rw [F.chunk]; exact t3.mono (F.vr r _).1
      · rw [F.len]; exact t4.mono (F.vr r _).1
    · exact hok
  · intro id hid
    rcases hna id hid with hid | hid
    · rcases hnr id hid with h1 | ⟨r, hr1, hr2⟩
      · exact Or.inl ((F.vs _).2.2.1 h1)
      · exact Or.inr ⟨r, htk r hr1, (F.vr r _).2.2.1 hr2⟩
    · exact Or.inr hid

end Mempipe
