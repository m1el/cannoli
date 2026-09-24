import Mempipe.Idx

/-!
# Invariants for progress

* `live`: a published sequence number that is not consumed yet is the latest
  `client_seq` of some buffer (so it is still in its buffer);
* `issued`: every ticket handed out belongs to some receiver, which holds it
  or logged it;
* `spin`: a sender waiting for buffer `i` after sending message `k` still sees
  `k` as the latest `client_seq[i]`.
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ)

/-- Ticket `t` was handed out: the counter went past it. -/
def Issued (c : Cfg ρ) (t : ℤ) : Prop := ∃ m ∈ c.mem .tick, m.val = some (t + 1)

structure PInv (c : Cfg ρ) : Prop where
  live : ∀ s : ℕ, s < c.s.pc.npub → ¬ Consumed c (s : ℤ) →
    ∃ j, LatestIs (c.mem (.cseq j)) (s : ℤ)
  issued : ∀ t : ℤ, 0 ≤ t → Issued c t → ∃ r, t ∈ tix (c.r r)
  spin : ∀ k i, c.s.pc = .spin k i → LatestIs (c.mem (.cseq i)) (k : ℤ)

/-! ## What steps do to the relevant state -/

/-- Receivers never write `client_seq`, never forget tickets, and only the
ticket counter's new messages hand out tickets they then hold. -/
theorem recv_facts {σ σ' : RState} {𝓥 𝓥' : TView Loc} {Mm Mm' : Mem} {𝓝 𝓝' : View Loc}
    (hst : TStep (rprog N) σ 𝓥 Mm 𝓝 σ' 𝓥' Mm' 𝓝') (hnf : σ'.pc ≠ .fault) :
    (∀ j, Mm' (.cseq j) = Mm (.cseq j)) ∧ (∀ t ∈ tix σ, t ∈ tix σ') ∧
    (∀ e ∈ σ.log, e ∈ σ'.log) ∧
    (∀ m ∈ Mm' .tick, m ∈ Mm .tick ∨ ∃ v, m.val = some (v + 1) ∧ v ∈ tix σ') := by
  have same : ∀ l, Mm' = Mm → Mm' l = Mm l := fun l h => by rw [h]
  cases hpc : σ.pc with
  | init =>
    obtain ⟨m1, -, v, -, -, -, -, -, -, -, rfl, -, rfl, -⟩ :=
      hst.update_inv (by simp only [rprog, hpc]; rfl)
    refine ⟨fun j => Memory.add_ne _ _ (by simp), fun t ht => ?_, fun e he => he, ?_⟩
    · simp only [tix, hpc, RPc.held, List.nil_append] at ht ⊢
      exact List.mem_append_right _ ht
    · intro m hm
      rcases Memory.mem_add.1 hm with ⟨-, rfl⟩ | hm
      · exact Or.inr ⟨v, rfl, by simp [tix, RPc.held]⟩
      · exact Or.inl hm
  | scan t i | own t i | len t i | chunk t i _ =>
    obtain ⟨m, -, -, -, -, -, hσ, -, rfl, -⟩ := hst.read_inv (by simp only [rprog, hpc]; rfl)
    have key : σ'.log = σ.log ∧ (σ'.pc = .fault ∨ σ'.pc.held = σ.pc.held) := by
      subst hσ; rcases hmv : m.val with _ | v
      · simp
      · simp only [hmv]; (try split_ifs) <;> simp [RPc.held, hpc]
    obtain ⟨hl, hh⟩ := key
    rcases hh with hf | hh
    · exact absurd hf hnf
    refine ⟨fun _ => rfl, fun t' ht' => ?_, fun e he => by rw [hl]; exact he,
      fun m hm => Or.inl hm⟩
    simp only [tix, hl, hh] at ht' ⊢; exact ht'
  | cb t i n p =>
    obtain ⟨b, rfl, -, rfl, -⟩ := hst.choose_inv (by simp only [rprog, hpc]; rfl)
    refine ⟨fun _ => rfl, fun t' ht' => ?_, fun e he => ?_, fun m hm => Or.inl hm⟩ <;>
      cases b <;> simp_all [tix, RPc.held]
  | rel t i =>
    obtain ⟨-, -, -, -, rfl, -, rfl, -⟩ := hst.write_inv (by simp only [rprog, hpc]; rfl)
    refine ⟨fun j => Memory.add_ne _ _ (by simp), fun t' ht' => ?_, fun e he => he,
      fun m hm => Or.inl (by simpa using hm)⟩
    simpa [tix, hpc, RPc.held] using ht'
  | fault => exact (hst.fault_inv (by simp [rprog, hpc])).elim

/-- The sender never writes the ticket counter; it writes `client_seq` only
when publishing. -/
theorem sender_facts {c : Cfg ρ} (h : Inv pay ln c) {σ : SState} {𝓥 : TView Loc} {M' : Mem}
    {𝓝' : View Loc}
    (hst : TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝')
    (hnf : σ.pc ≠ .fault) :
    M' .tick = c.mem .tick ∧
    ((∀ j, M' (.cseq j) = c.mem (.cseq j)) ∧ σ.pc.npub = c.s.pc.npub ∧
        (∀ k i, σ.pc = .spin k i → c.s.pc = .spin k i) ∨
      ∃ k b j, c.s.pc = .pub k b j k ∧ σ.pc.npub = k + 1 ∧
        LatestIs (M' (.cseq j)) (k : ℤ) ∧ (∀ j', j' ≠ j → M' (.cseq j') = c.mem (.cseq j')) ∧
        (∀ k' i', σ.pc = .spin k' i' → k' = k ∧ i' = j)) := by
  cases hpc : c.s.pc with
  | start k =>
    by_cases hk : k < M
    · obtain ⟨b, rfl, -, rfl, -⟩ := hst.choose_inv (by simp [sprog, hpc, hk]; rfl)
      exact ⟨rfl, Or.inl ⟨fun _ => rfl, by simp [SPc.npub, SPc.k], by simp⟩⟩
    · exact (hst.halt_inv (by simp [sprog, hpc, hk])).elim
  | alloc k b i =>
    obtain ⟨m, -, -, -, -, -, hσ, -, rfl, -⟩ := hst.read_inv (by simp only [sprog, hpc]; rfl)
    have key : σ.pc.npub = k ∧ ∀ k' i', σ.pc ≠ .spin k' i' := by
      subst hσ; rcases hmv : m.val with _ | v
      · simp [hmv] at hnf
      · simp only [hmv]; split_ifs <;> simp [SPc.npub, SPc.k]
    exact ⟨rfl, Or.inl ⟨fun _ => rfl, by simpa [SPc.npub, SPc.k] using key.1,
      fun k' i' h' => absurd h' (key.2 k' i')⟩⟩
  | chunk k b i =>
    obtain ⟨-, -, -, -, rfl, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    exact ⟨Memory.add_ne _ _ (by simp),
      Or.inl ⟨fun _ => Memory.add_ne _ _ (by simp), by simp [SPc.npub, SPc.k], by simp⟩⟩
  | len k b i =>
    obtain ⟨-, -, -, -, rfl, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    exact ⟨Memory.add_ne _ _ (by simp),
      Or.inl ⟨fun _ => Memory.add_ne _ _ (by simp), by simp [SPc.npub, SPc.k], by simp⟩⟩
  | own k b i =>
    obtain ⟨-, -, -, -, rfl, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    exact ⟨Memory.add_ne _ _ (by simp),
      Or.inl ⟨fun _ => Memory.add_ne _ _ (by simp), by simp [SPc.npub, SPc.k], by simp⟩⟩
  | fadd k b i =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, rfl, -, rfl, -⟩ :=
      hst.update_inv (by simp only [sprog, hpc]; rfl)
    exact ⟨Memory.add_ne _ _ (by simp),
      Or.inl ⟨fun _ => Memory.add_ne _ _ (by simp), by simp [SPc.npub, SPc.k], by simp⟩⟩
  | pub k b i s =>
    have hs : s = k := h.sPub k b i s hpc
    subst hs
    obtain ⟨t, -, hlt, -, rfl, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    refine ⟨Memory.add_ne _ _ (by simp), Or.inr ⟨k, b, i, rfl, ?_, ?_, ?_, ?_⟩⟩
    · cases b <;> simp [SPc.npub, SPc.k]
    · simp only [Memory.add_self]
      exact latestIs_cons_new (h.cseqS i) hlt rfl
    · intro j' hj'; exact Memory.add_ne _ _ (by simpa using hj')
    · intro k' i' h'; cases b <;> simp at h'; exact ⟨h'.1.symm, h'.2.symm⟩
  | spin k i =>
    obtain ⟨m, -, -, -, -, -, hσ, -, rfl, -⟩ := hst.read_inv (by simp only [sprog, hpc]; rfl)
    have key : σ.pc.npub = k + 1 ∧ ∀ k' i', σ.pc = .spin k' i' → k' = k ∧ i' = i := by
      subst hσ; rcases hmv : m.val with _ | v
      · simp [hmv] at hnf
      · simp only [hmv]; split_ifs <;> simp [SPc.npub, SPc.k]
    exact ⟨rfl, Or.inl ⟨fun _ => rfl, by simpa [SPc.npub, SPc.k] using key.1,
      fun k' i' h' => by obtain ⟨rfl, rfl⟩ := key.2 k' i' h'; rfl⟩⟩
  | fault => exact (hst.fault_inv (by simp [sprog, hpc])).elim

/-! ## Preservation -/

theorem consumed_step {c c' : Cfg ρ} (hr : Reach N M pay ln c)
    (hs : Step (prog N M pay ln) c c') {v : ℤ}
    (h : Consumed c v) : Consumed c' v := by
  rcases step_cases N M pay ln hs with ⟨σ, 𝓥, M', 𝓝', hst, rfl⟩ | ⟨r0, σ, 𝓥, M', 𝓝', hst, rfl⟩
  · exact (consumed_setS).2 h
  · have hc' := reach_inv N M pay ln (hr.tail hs)
    exact consumed_setR (recv_facts N hst (by simpa using hc'.rFault r0)).2.2.1 h

omit [DecidableEq ρ] in
theorem pinv_init : PInv (initConfig init0 initVal : Cfg ρ) where
  live s hs := by simp [SPc.npub, SPc.k] at hs
  issued t ht hi := by
    obtain ⟨m, hm, hv⟩ := hi
    simp only [init_mem, List.mem_singleton] at hm; subst hm
    simp [initVal] at hv; omega
  spin k i h := by simp at h

theorem pinv_step {c c' : Cfg ρ} (h : Inv pay ln c) (h' : Inv pay ln c') (hp : PInv c)
    (hs : Step (prog N M pay ln) c c') : PInv c' := by
  rcases step_cases N M pay ln hs with ⟨σ, 𝓥, M', 𝓝', hst, rfl⟩ | ⟨r0, σ, 𝓥, M', 𝓝', hst, rfl⟩
  · obtain ⟨htick, hcase⟩ := sender_facts N M pay ln h hst (by simpa using h'.sFault)
    refine ⟨?_, ?_, ?_⟩
    · intro s hs hnc
      rw [consumed_setS] at hnc
      simp only [Cfg.setS_s, Cfg.setS_mem] at hs ⊢
      rcases hcase with ⟨hq, hnp, -⟩ | ⟨k, b, j, hpc, hnp, hlat, hq, -⟩
      · obtain ⟨j, hj⟩ := hp.live s (hnp ▸ hs) hnc
        exact ⟨j, by rw [hq]; exact hj⟩
      · by_cases hsk : s = k
        · subst hsk; exact ⟨j, hlat⟩
        · have hs' : s < c.s.pc.npub := by
            rw [hnp] at hs; simp [hpc, SPc.npub, SPc.k]; omega
          obtain ⟨j', hj'⟩ := hp.live s hs' hnc
          by_cases hjj : j' = j
          · -- buffer `j` was being sealed, so its old sequence numbers are consumed
            subst hjj
            exfalso
            obtain ⟨ph, hph⟩ := h.phase j'
            have hnl : NoLive c j' := by
              match ph, hph with
              | .free, hph' => exact absurd hph'.2.1 (by simp [hpc, SPc.sealing])
              | .fill, hph' => exact absurd hph'.1 (by simp [hpc, SPc.fill])
              | .sealing, hph' => exact hph'.2.2.1
              | .pub _, hph' => exact absurd hph'.2.1 (by simp [hpc, SPc.sealing])
            obtain ⟨q, hq', hqv⟩ := hj'
            rcases hnl q hq'.1 _ hqv with h1 | h1
            · rw [NO_SEQ] at h1; omega
            · exact hnc h1
          · exact ⟨j', by rw [hq j' hjj]; exact hj'⟩
    · intro t ht hi
      obtain ⟨m, hm, hv⟩ := hi
      simp only [Cfg.setS_mem, htick] at hm
      obtain ⟨r, hr⟩ := hp.issued t ht ⟨m, hm, hv⟩
      exact ⟨r, by simpa using hr⟩
    · intro k i hk
      simp only [Cfg.setS_s, Cfg.setS_mem] at hk ⊢
      rcases hcase with ⟨hq, -, hspin⟩ | ⟨k', b, j, -, -, hlat, -, hspin⟩
      · rw [hq]; exact hp.spin k i (hspin k i hk)
      · obtain ⟨rfl, rfl⟩ := hspin k i hk; exact hlat
  · obtain ⟨hq, htix, hlog, htick⟩ := recv_facts N hst (by simpa using h'.rFault r0)
    refine ⟨?_, ?_, ?_⟩
    · intro s hs hnc
      simp only [Cfg.setR_s, Cfg.setR_mem] at hs ⊢
      obtain ⟨j, hj⟩ := hp.live s hs (fun h' => hnc (consumed_setR hlog h'))
      exact ⟨j, by rw [hq]; exact hj⟩
    · intro t ht hi
      obtain ⟨m, hm, hv⟩ := hi
      simp only [Cfg.setR_mem] at hm
      rcases htick m hm with hm | ⟨v, hmv, hvt⟩
      · obtain ⟨r, hr⟩ := hp.issued t ht ⟨m, hm, hv⟩
        refine ⟨r, ?_⟩
        rw [setR_r]; split_ifs with h1
        · subst h1; exact htix t hr
        · exact hr
      · rw [hv, Option.some.injEq] at hmv
        have : t = v := by omega
        subst this
        exact ⟨r0, by simpa using hvt⟩
    · intro k i hk
      simp only [Cfg.setR_s, Cfg.setR_mem] at hk ⊢
      rw [hq]; exact hp.spin k i hk

theorem reach_pinv {c : Cfg ρ} (hr : Reach N M pay ln c) : PInv c := by
  induction hr with
  | refl => exact pinv_init
  | @tail c1 c2 hr1 hs ih =>
    exact pinv_step N M pay ln (reach_inv N M pay ln hr1) (reach_inv N M pay ln (hr1.tail hs)) ih hs

end Mempipe
