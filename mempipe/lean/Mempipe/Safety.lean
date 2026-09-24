import Mempipe.RecvStep

/-!
# Safety of mempipe

For any number of buffers `N`, messages `M`, payloads and lengths, and any
type `ρ` of receivers, in every reachable configuration:

* `no_race`: no thread's next memory access is racy (ORC11's race detector
  never fires);
* `no_fault`: no thread is at a fault: the `debug_assert!(client_owned)` in
  `try_recv` holds, and nobody reads uninitialized memory;
* `sender_log`: the sender published sequence numbers `0, 1, …` in order, with
  the payload and length of its `k`-th message for sequence number `k`;
* `recv_correct`: every message a receiver accepted is exactly what the
  sender published under that sequence number;
* `recv_once`: no sequence number is accepted twice, by the same receiver or
  by two receivers.
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ)

theorem inv_step {c c' : Cfg ρ} (h : Inv pay ln c) (hs : Step (prog N M pay ln) c c') :
    Inv pay ln c' := by
  have hg := genInv_step h.gen hs
  rcases step_cases N M pay ln hs with ⟨σ, 𝓥, M', 𝓝', hst, rfl⟩ | ⟨r, σ, 𝓥, M', 𝓝', hst, rfl⟩
  · exact inv_sender N M pay ln h hst hg
  · exact inv_recv N pay ln h hst hg

theorem reach_inv {c : Cfg ρ} (h : Reach N M pay ln c) : Inv pay ln c := by
  induction h with
  | refl => exact inv_init pay ln
  | tail _ hs ih => exact inv_step N M pay ln ih hs

/-! ## No data races -/

theorem drfPreRead_atomic {c : Cfg ρ} (h : Inv pay ln c) {l : Loc} {o : MemOrder}
    {𝓥 : TView Loc} (hl : ¬ l.IsChunk) (hcur : 1 ≤ (𝓥.cur l).w) (ho : MemOrder.rlx ≤ o) :
    DrfPreRead l c.na 𝓥 c.mem o :=
  ⟨by rw [(h.atomNa l hl).1]; exact hcur, fun h' => absurd ho h'⟩

theorem drfPreWrite_atomic {c : Cfg ρ} (h : Inv pay ln c) {l : Loc} {o : MemOrder}
    {𝓥 : TView Loc} (hl : ¬ l.IsChunk) (hcur : 1 ≤ (𝓥.cur l).w) (ho : MemOrder.rlx ≤ o) :
    DrfPreWrite l c.na 𝓥 c.mem o :=
  ⟨by rw [(h.atomNa l hl).2]; exact Finset.empty_subset _,
    by rw [(h.atomNa l hl).1]; exact hcur, fun h' => absurd ho h'⟩

/-- The race detector never fires. -/
theorem no_race {c : Cfg ρ} (hr : Reach N M pay ln c) : ¬ Racy (prog N M pay ln) c := by
  have h := reach_inv N M pay ln hr
  rintro ⟨i, hi⟩
  apply hi
  have hcur := h.gen.cur i
  have NC : ∀ j, ¬ (Loc.own j).IsChunk ∧ ¬ (Loc.len j).IsChunk ∧ ¬ (Loc.cseq j).IsChunk ∧
      ¬ Loc.curSeq.IsChunk ∧ ¬ Loc.tick.IsChunk := fun j => by simp [Loc.IsChunk]
  cases i with
  | sender =>
    show (sprog N M pay ln c.s).DrfPreOk c.na (c.th .sender).2 c.mem
    cases hpc : c.s.pc with
    | start k =>
      simp only [sprog, hpc]; split <;> trivial
    | alloc k b j =>
      simp only [sprog, hpc, Instr.DrfPreOk]
      exact drfPreRead_atomic pay ln h (NC j).1 (hcur _) (by decide)
    | chunk k b j =>
      simp only [sprog, hpc, Instr.DrfPreOk]
      obtain ⟨ph, hph⟩ := h.phase j
      have hnr : (c.na (.chunk j)).nr ⊆ (c.vs (.chunk j)).nr := by
        match ph, hph with
        | .free, hph' => exact absurd hph'.1 (by simp [hpc, SPc.fill])
        | .fill, hph' => exact hph'.2.2.2.2.1
        | .sealing, hph' => exact absurd hph'.1 (by simp [hpc, SPc.sealing])
        | .pub _, hph' => exact absurd hph'.1 (by simp [hpc, SPc.fill])
      obtain ⟨m, hm, hmt⟩ := h.chunkNa j
      refine ⟨hnr, ?_, fun _ => ⟨h.chunkS j, ?_, ?_⟩⟩
      · rw [← hmt]; exact h.chunkS j m hm
      · rw [(h.chunkAt j).1]; exact Finset.empty_subset _
      · rw [(h.chunkAt j).2]; exact Finset.empty_subset _
    | len k b j =>
      simp only [sprog, hpc, Instr.DrfPreOk]
      exact drfPreWrite_atomic pay ln h (NC j).2.1 (hcur _) (by decide)
    | own k b j =>
      simp only [sprog, hpc, Instr.DrfPreOk]
      exact drfPreWrite_atomic pay ln h (NC j).1 (hcur _) (by decide)
    | fadd k b j =>
      simp only [sprog, hpc, Instr.DrfPreOk]
      exact ⟨drfPreRead_atomic pay ln h (NC j).2.2.2.1 (hcur _) (by decide),
        drfPreWrite_atomic pay ln h (NC j).2.2.2.1 (hcur _) (by decide)⟩
    | pub k b j s =>
      simp only [sprog, hpc, Instr.DrfPreOk]
      exact drfPreWrite_atomic pay ln h (NC j).2.2.1 (hcur _) (by decide)
    | spin k j =>
      simp only [sprog, hpc, Instr.DrfPreOk]
      exact drfPreRead_atomic pay ln h (NC j).1 (hcur _) (by decide)
    | fault => simp only [sprog, hpc]; trivial
  | recv r =>
    show (rprog N (c.r r)).DrfPreOk c.na (c.th (.recv r)).2 c.mem
    cases hpc : (c.r r).pc with
    | init =>
      simp only [rprog, hpc, Instr.DrfPreOk]
      exact ⟨drfPreRead_atomic pay ln h (NC 0).2.2.2.2 (hcur _) (by decide),
        drfPreWrite_atomic pay ln h (NC 0).2.2.2.2 (hcur _) (by decide)⟩
    | scan t j =>
      simp only [rprog, hpc, Instr.DrfPreOk]
      exact drfPreRead_atomic pay ln h (NC j).2.2.1 (hcur _) (by decide)
    | own t j =>
      simp only [rprog, hpc, Instr.DrfPreOk]
      exact drfPreRead_atomic pay ln h (NC j).1 (hcur _) (by decide)
    | len t j =>
      simp only [rprog, hpc, Instr.DrfPreOk]
      exact drfPreRead_atomic pay ln h (NC j).2.1 (hcur _) (by decide)
    | chunk t j n =>
      simp only [rprog, hpc, Instr.DrfPreOk]
      obtain ⟨s, o, -, -, -, hok⟩ := h.onBuf pay ln (r := r) (i := j) (by simp [hpc, RPc.onBuf])
      have hb : Below (c.mem (.chunk j)) (c.vr r (.chunk j)).w := hok.2.2.1
      obtain ⟨m, hm, hmt⟩ := h.chunkNa j
      refine ⟨?_, fun _ => ⟨hb, ?_⟩⟩
      · rw [← hmt]; exact hb m hm
      · rw [(h.chunkAt j).1]; exact Finset.empty_subset _
    | cb t j n p => simp only [rprog, hpc]; trivial
    | rel t j =>
      simp only [rprog, hpc, Instr.DrfPreOk]
      exact drfPreWrite_atomic pay ln h (NC j).1 (hcur _) (by decide)
    | fault => simp only [rprog, hpc]; trivial

/-! ## No faults -/

/-- No thread is at a fault: the `debug_assert` holds and no uninitialized
memory is read. -/
theorem no_fault {c : Cfg ρ} (hr : Reach N M pay ln c) : ¬ Faulty (prog N M pay ln) c := by
  have h := reach_inv N M pay ln hr
  rintro ⟨i, hi⟩
  cases i with
  | sender =>
    change sprog N M pay ln c.s = .fault at hi
    cases hpc : c.s.pc
    all_goals first
      | exact h.sFault hpc
      | (simp only [sprog, hpc] at hi; split at hi <;> cases hi)
      | simp [sprog, hpc] at hi
  | recv r =>
    change rprog N (c.r r) = .fault at hi
    cases hpc : (c.r r).pc
    all_goals first
      | exact h.rFault r hpc
      | simp [rprog, hpc] at hi

/-! ## Delivery -/

theorem mem_sentLog {k : ℕ} {e : Entry} :
    e ∈ sentLog pay ln k ↔ ∃ j < k, e = ((j : ℤ), pay j, ln j) := by
  induction k with
  | zero => simp [sentLog]
  | succ k ih =>
    simp only [sentLog, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases hjk : j = k
      · subst hjk; exact Or.inl rfl
      · exact Or.inr ⟨j, by omega, rfl⟩

/-- The sender publishes its `k`-th message, with payload `pay k` and length
`ln k`, under sequence number `k`. -/
theorem sender_log {c : Cfg ρ} (hr : Reach N M pay ln c) :
    c.s.log = sentLog pay ln c.s.pc.npub :=
  (reach_inv N M pay ln hr).sLog

/-- Every message a receiver accepted is one the sender published, with the
payload and length the sender wrote for that sequence number. -/
theorem recv_correct {c : Cfg ρ} (hr : Reach N M pay ln c) {r : ρ} {e : Entry}
    (he : e ∈ (c.r r).log) : e ∈ c.s.log := by
  have h := reach_inv N M pay ln hr
  obtain ⟨e1, e2, e3, e4⟩ := h.rLog r e he
  rw [h.sLog, mem_sentLog]
  refine ⟨e.1.toNat, by omega, ?_⟩
  obtain ⟨a, b, d⟩ := e
  simp only at e1 e2 e3 e4 ⊢
  rw [e3, e4, Int.toNat_of_nonneg e1]

/-- No sequence number is accepted twice. -/
theorem recv_once {c : Cfg ρ} (hr : Reach N M pay ln c) :
    (∀ r, ((c.r r).log.map Prod.fst).Nodup) ∧
    (∀ r r', r ≠ r' → ∀ t ∈ (c.r r).log.map Prod.fst, t ∉ (c.r r').log.map Prod.fst) := by
  have h := reach_inv N M pay ln hr
  refine ⟨fun r => ?_, fun r r' hne t ht ht' => h.tixDisj r r' hne t (tix_log ht) (tix_log ht')⟩
  have := h.tixNodup r
  exact (List.nodup_append.1 this).2.1

end Mempipe
