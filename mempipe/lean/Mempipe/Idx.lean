import Mempipe.Safety

/-!
# Index bounds

With `0 < N`, every buffer index in a program counter is below `N`, and the
sender never goes past message `M`.
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ)

def SPc.Idx : SPc → Prop
  | .start k => k ≤ M
  | .alloc k _ i | .chunk k _ i | .len k _ i | .own k _ i | .fadd k _ i | .pub k _ i _
  | .spin k i => k < M ∧ i < N
  | .fault => True

def RPc.Idx : RPc → Prop
  | .scan _ i | .own _ i | .len _ i | .chunk _ i _ | .cb _ i _ _ | .rel _ i => i < N
  | .init | .fault => True

/-- Index bounds of all threads. -/
def IdxInv (c : Cfg ρ) : Prop := c.s.pc.Idx N M ∧ ∀ r, (c.r r).pc.Idx N

theorem sprog_idx (hN : 0 < N) {σ σ' : SState} {𝓥 𝓥' : TView Loc} {Mm Mm' : Mem}
    {𝓝 𝓝' : View Loc} (hst : TStep (sprog N M pay ln) σ 𝓥 Mm 𝓝 σ' 𝓥' Mm' 𝓝')
    (h : σ.pc.Idx N M) : σ'.pc.Idx N M := by
  cases hpc : σ.pc with
  | start k =>
    rw [hpc] at h
    by_cases hk : k < M
    · obtain ⟨b, rfl, -⟩ := hst.choose_inv (by simp [sprog, hpc, hk]; rfl)
      exact ⟨hk, hN⟩
    · exact (hst.halt_inv (by simp [sprog, hpc, hk])).elim
  | alloc k b i =>
    rw [hpc] at h
    obtain ⟨m, -, -, -, -, -, rfl, -⟩ := hst.read_inv (by simp only [sprog, hpc]; rfl)
    rcases m.val with _ | v
    · trivial
    · dsimp only; split_ifs
      · exact h
      · exact ⟨h.1, Nat.mod_lt _ hN⟩
  | chunk k b i =>
    rw [hpc] at h
    obtain ⟨-, -, -, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    exact h
  | len k b i =>
    rw [hpc] at h
    obtain ⟨-, -, -, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    exact h
  | own k b i =>
    rw [hpc] at h
    obtain ⟨-, -, -, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    exact h
  | fadd k b i =>
    rw [hpc] at h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, rfl, -⟩ :=
      hst.update_inv (by simp only [sprog, hpc]; rfl)
    exact h
  | pub k b i s =>
    rw [hpc] at h
    obtain ⟨-, -, -, -, rfl, -⟩ := hst.write_inv (by simp only [sprog, hpc]; rfl)
    cases b
    · show k + 1 ≤ M; exact h.1
    · exact h
  | spin k i =>
    rw [hpc] at h
    obtain ⟨m, -, -, -, -, -, rfl, -⟩ := hst.read_inv (by simp only [sprog, hpc]; rfl)
    rcases m.val with _ | v
    · trivial
    · dsimp only; split_ifs
      · show k + 1 ≤ M; exact h.1
      · exact h
  | fault => exact (hst.fault_inv (by simp [sprog, hpc])).elim

theorem rprog_idx (hN : 0 < N) {σ σ' : RState} {𝓥 𝓥' : TView Loc} {Mm Mm' : Mem}
    {𝓝 𝓝' : View Loc} (hst : TStep (rprog N) σ 𝓥 Mm 𝓝 σ' 𝓥' Mm' 𝓝')
    (h : σ.pc.Idx N) : σ'.pc.Idx N := by
  cases hpc : σ.pc with
  | init =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, rfl, -⟩ :=
      hst.update_inv (by simp only [rprog, hpc]; rfl)
    exact hN
  | scan t i =>
    rw [hpc] at h
    obtain ⟨m, -, -, -, -, -, rfl, -⟩ := hst.read_inv (by simp only [rprog, hpc]; rfl)
    rcases m.val with _ | v
    · trivial
    · dsimp only; split_ifs
      · exact h
      · exact Nat.mod_lt _ hN
  | own t i =>
    rw [hpc] at h
    obtain ⟨m, -, -, -, -, -, rfl, -⟩ := hst.read_inv (by simp only [rprog, hpc]; rfl)
    rcases m.val with _ | v
    · trivial
    · dsimp only; split_ifs
      · trivial
      · exact h
  | len t i =>
    rw [hpc] at h
    obtain ⟨m, -, -, -, -, -, rfl, -⟩ := hst.read_inv (by simp only [rprog, hpc]; rfl)
    rcases m.val with _ | v
    · trivial
    · exact h
  | chunk t i n =>
    rw [hpc] at h
    obtain ⟨m, -, -, -, -, -, rfl, -⟩ := hst.read_inv (by simp only [rprog, hpc]; rfl)
    rcases m.val with _ | v
    · trivial
    · exact h
  | cb t i n p =>
    rw [hpc] at h
    obtain ⟨b, rfl, -⟩ := hst.choose_inv (by simp only [rprog, hpc]; rfl)
    cases b
    · exact hN
    · exact h
  | rel t i =>
    obtain ⟨-, -, -, -, rfl, -⟩ := hst.write_inv (by simp only [rprog, hpc]; rfl)
    trivial
  | fault => exact (hst.fault_inv (by simp [rprog, hpc])).elim

theorem idx_step (hN : 0 < N) {c c' : Cfg ρ} (h : IdxInv N M c)
    (hs : Step (prog N M pay ln) c c') : IdxInv N M c' := by
  rcases step_cases N M pay ln hs with ⟨σ, 𝓥, M', 𝓝', hst, rfl⟩ | ⟨r0, σ, 𝓥, M', 𝓝', hst, rfl⟩
  · exact ⟨by simpa using sprog_idx N M pay ln hN hst h.1, fun r => by simpa using h.2 r⟩
  · refine ⟨by simpa using h.1, fun r => ?_⟩
    rw [setR_r]; split_ifs with hr
    · subst hr; exact rprog_idx N hN hst (h.2 r)
    · exact h.2 r

theorem reach_idx (hN : 0 < N) {c : Cfg ρ} (h : Reach N M pay ln c) : IdxInv N M c := by
  induction h with
  | refl => exact ⟨Nat.zero_le _, fun r => trivial⟩
  | tail _ hs ih => exact idx_step N M pay ln hN ih hs

end Mempipe
