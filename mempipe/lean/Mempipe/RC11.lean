import Mempipe.Safety
import ORC11.Replay

/-!
# mempipe is safe under RC11

Every RC11-consistent execution graph of mempipe (`ORC11/RC11.lean`) is
race-free, reaches no fault, and delivers correctly. The ORC11 safety theorems
carry over because mempipe is location-disciplined (chunks are only accessed
non-atomically, everything else only atomically) and every RC11-consistent
execution of a disciplined program either makes ORC11 race or is an ORC11 run
(`RC11.Exec.replay`). The first is impossible by `no_race`.
-/

namespace Mempipe

open ORC11 ORC11.RC11

variable {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ)

/-- Chunks are the non-atomic locations, everything else is atomic. -/
theorem disciplined : Disciplined (prog (ρ := ρ) N M pay ln) (fun l => ¬ l.IsChunk) := by
  intro i s
  cases i with
  | sender =>
    change (sprog N M pay ln s).Disc _
    cases hpc : s.pc <;> simp only [sprog, hpc] <;> (try split) <;>
      simp [Instr.Disc, Loc.IsChunk]
  | recv r =>
    change (rprog N s).Disc _
    cases hpc : s.pc <;> simp [rprog, hpc, Instr.Disc, Loc.IsChunk]

/-- **mempipe under RC11.** Every RC11-consistent execution of the pipe is
race-free, has no thread at a fault (the `debug_assert` holds and nothing
uninitialized is read), publishes message `k` under sequence number `k`, and
delivers each accepted buffer exactly as published, at most once. -/
theorem rc11_safe (G : Exec (prog (ρ := ρ) N M pay ln) init0 initVal) (hc : G.Consistent) :
    ¬ G.Racy ∧ (G.final .sender).pc ≠ .fault ∧ (∀ r, (G.final (.recv r)).pc ≠ .fault) ∧
      (G.final .sender).log = sentLog pay ln (G.final .sender).pc.npub ∧
      (∀ r, ∀ e ∈ (G.final (.recv r)).log, e ∈ (G.final .sender).log) ∧
      (∀ r, ((G.final (.recv r)).log.map Prod.fst).Nodup) ∧
      (∀ r r', r ≠ r' → ∀ t ∈ (G.final (.recv r)).log.map Prod.fst,
        t ∉ (G.final (.recv r')).log.map Prod.fst) := by
  rcases G.replay hc (disciplined N M pay ln) with ⟨c, hr, hracy⟩ | ⟨hnr, c, hr, hfin⟩
  · exact absurd hracy (no_race N M pay ln hr)
  have hs : Cfg.s c = G.final .sender := hfin .sender
  have hrr : ∀ r, Cfg.r c r = G.final (.recv r) := fun r => hfin (.recv r)
  have h := reach_inv N M pay ln hr
  obtain ⟨h1, h2⟩ := recv_once N M pay ln hr
  refine ⟨hnr, hs ▸ h.sFault, fun r => hrr r ▸ h.rFault r, hs ▸ h.sLog, fun r e he => ?_,
    fun r => hrr r ▸ h1 r, fun r r' hne t ht => ?_⟩
  · rw [← hs]; exact recv_correct N M pay ln hr (by rw [hrr]; exact he)
  · rw [← hrr] at ht ⊢; exact h2 r r' hne t ht

end Mempipe
