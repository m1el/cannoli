import Mempipe.ProgressInv
import ORC11.Wf

/-!
# Progress: no stranding

From every reachable configuration, some continuation delivers every message:
the sender finishes all `M` messages and every sequence number `k < M` is
accepted by some receiver, with the payload and length of message `k`. The
continuation only takes latest steps (`StepL`): every load reads the latest
write of its location and every store goes after all of them, so it is a
sequentially consistent execution. It needs at least one buffer and one
receiver.

The continuation delivers messages in order. To deliver `s` (all earlier
ones consumed): the sender publishes `s` if it has not (freeing a buffer
first by letting a receiver finish its release); a receiver takes ticket `s`
if nobody holds it; then the holder of `s` scans to the buffer and accepts it.
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ] (N M : ℕ) (pay ln : ℕ → ℤ)

/-- Runs of latest steps. -/
abbrev Run (c c' : Cfg ρ) : Prop := Relation.ReflTransGen (StepL (prog N M pay ln)) c c'

section Basic

variable {N M pay ln}

theorem Reach.run {c c' : Cfg ρ} (hr : Reach N M pay ln c) (h : Run N M pay ln c c') :
    Reach N M pay ln c' :=
  hr.trans (StepL.reflTransGen_toStep h)

theorem Reach.stepL {c c' : Cfg ρ} (hr : Reach N M pay ln c)
    (h : StepL (prog N M pay ln) c c') : Reach N M pay ln c' :=
  hr.tail h.toStep

theorem Reach.wf {c : Cfg ρ} (hr : Reach N M pay ln c) : WfInv c := Reachable.wfInv hr

theorem Reach.drf {c : Cfg ρ} (hr : Reach N M pay ln c) (i : TId ρ) :
    (prog N M pay ln i (c.th i).1).DrfPreOk c.na (c.th i).2 c.mem := by
  by_contra hne; exact no_race N M pay ln hr ⟨i, hne⟩

end Basic

/-! ## Single latest steps -/

section Steps

variable {N M pay ln}

theorem sender_read {c : Cfg ρ} (hr : Reach N M pay ln c) {l : Loc} {o : MemOrder}
    {k : Option ℤ → SState} (hp : sprog N M pay ln c.s = .read l o k) {m : MsgT}
    (hm : IsLatest (c.mem l) m) :
    ∃ 𝓥 𝓝, StepL (prog N M pay ln) c (c.setS (k m.val) 𝓥 c.mem 𝓝) := by
  have hd := hr.drf .sender
  change (sprog N M pay ln c.s).DrfPreOk _ _ _ at hd
  rw [hp] at hd
  obtain ⟨𝓥, 𝓝, h⟩ := TStepL.exists_read (prog := sprog N M pay ln) (hr.wf.cur TId.sender)
    hr.wf.msgWf hp hd hm
  exact ⟨𝓥, 𝓝, StepL.of_tstepL (i := TId.sender) h⟩

theorem sender_write {c : Cfg ρ} (hr : Reach N M pay ln c) {l : Loc} {o : MemOrder} {v : ℤ}
    {k : SState} (hp : sprog N M pay ln c.s = .write l o v k) :
    ∃ m 𝓥 𝓝, m.val = some v ∧ (∀ m' ∈ c.mem l, m'.time < m.time) ∧
      StepL (prog N M pay ln) c (c.setS k 𝓥 (c.mem.add l m) 𝓝) := by
  have hd := hr.drf .sender
  change (sprog N M pay ln c.s).DrfPreOk _ _ _ at hd
  rw [hp] at hd
  obtain ⟨m, 𝓥, 𝓝, hv, hlt, h⟩ := TStepL.exists_write (prog := sprog N M pay ln)
    (hr.wf.tview TId.sender) (hr.wf.rel TId.sender) (hr.wf.cur TId.sender) hr.wf.nonempty hp hd
  exact ⟨m, 𝓥, 𝓝, hv, hlt, StepL.of_tstepL (i := TId.sender) h⟩

theorem sender_update {c : Cfg ρ} (hr : Reach N M pay ln c) {l : Loc} {or ow : MemOrder}
    {f : ℤ → ℤ} {k : ℤ → SState} (hp : sprog N M pay ln c.s = .update l or ow f k)
    {m1 : MsgT} {v : ℤ} (hm1 : IsLatest (c.mem l) m1) (hv : m1.val = some v) :
    ∃ m2 𝓥 𝓝, m2.time = m1.time + 1 ∧ m2.val = some (f v) ∧
      (∀ m' ∈ c.mem l, m'.time < m2.time) ∧
      StepL (prog N M pay ln) c (c.setS (k v) 𝓥 (c.mem.add l m2) 𝓝) := by
  have hd := hr.drf .sender
  change (sprog N M pay ln c.s).DrfPreOk _ _ _ at hd
  rw [hp] at hd
  obtain ⟨m2, 𝓥, 𝓝, ht, hv', hlt, h⟩ := TStepL.exists_update (prog := sprog N M pay ln)
    (hr.wf.tview TId.sender) (hr.wf.rel TId.sender) (hr.wf.cur TId.sender) hr.wf.msgWf
    hr.wf.msgClosed hp hd hm1 hv
  exact ⟨m2, 𝓥, 𝓝, ht, hv', hlt, StepL.of_tstepL (i := TId.sender) h⟩

theorem sender_choose {c : Cfg ρ} {k : Bool → SState}
    (hp : sprog N M pay ln c.s = .choose k) (b : Bool) :
    StepL (prog N M pay ln) c (c.setS (k b) (c.th .sender).2 c.mem c.na) :=
  StepL.of_tstepL (i := TId.sender) (TStepL.exists_choose (prog := sprog N M pay ln) hp b)

theorem recv_read {c : Cfg ρ} (hr : Reach N M pay ln c) {r : ρ} {l : Loc} {o : MemOrder}
    {k : Option ℤ → RState} (hp : rprog N (c.r r) = .read l o k) {m : MsgT}
    (hm : IsLatest (c.mem l) m) :
    ∃ 𝓥 𝓝, StepL (prog N M pay ln) c (c.setR r (k m.val) 𝓥 c.mem 𝓝) := by
  have hd := hr.drf (.recv r)
  change (rprog N (c.r r)).DrfPreOk _ _ _ at hd
  rw [hp] at hd
  obtain ⟨𝓥, 𝓝, h⟩ := TStepL.exists_read (prog := rprog N) (hr.wf.cur (TId.recv r))
    hr.wf.msgWf hp hd hm
  exact ⟨𝓥, 𝓝, StepL.of_tstepL (i := TId.recv r) h⟩

theorem recv_write {c : Cfg ρ} (hr : Reach N M pay ln c) {r : ρ} {l : Loc} {o : MemOrder}
    {v : ℤ} {k : RState} (hp : rprog N (c.r r) = .write l o v k) :
    ∃ m 𝓥 𝓝, m.val = some v ∧ (∀ m' ∈ c.mem l, m'.time < m.time) ∧
      StepL (prog N M pay ln) c (c.setR r k 𝓥 (c.mem.add l m) 𝓝) := by
  have hd := hr.drf (.recv r)
  change (rprog N (c.r r)).DrfPreOk _ _ _ at hd
  rw [hp] at hd
  obtain ⟨m, 𝓥, 𝓝, hv, hlt, h⟩ := TStepL.exists_write (prog := rprog N)
    (hr.wf.tview (TId.recv r)) (hr.wf.rel (TId.recv r)) (hr.wf.cur (TId.recv r)) hr.wf.nonempty hp hd
  exact ⟨m, 𝓥, 𝓝, hv, hlt, StepL.of_tstepL (i := TId.recv r) h⟩

theorem recv_update {c : Cfg ρ} (hr : Reach N M pay ln c) {r : ρ} {l : Loc}
    {or ow : MemOrder} {f : ℤ → ℤ} {k : ℤ → RState}
    (hp : rprog N (c.r r) = .update l or ow f k)
    {m1 : MsgT} {v : ℤ} (hm1 : IsLatest (c.mem l) m1) (hv : m1.val = some v) :
    ∃ m2 𝓥 𝓝, m2.time = m1.time + 1 ∧ m2.val = some (f v) ∧
      (∀ m' ∈ c.mem l, m'.time < m2.time) ∧
      StepL (prog N M pay ln) c (c.setR r (k v) 𝓥 (c.mem.add l m2) 𝓝) := by
  have hd := hr.drf (.recv r)
  change (rprog N (c.r r)).DrfPreOk _ _ _ at hd
  rw [hp] at hd
  obtain ⟨m2, 𝓥, 𝓝, ht, hv', hlt, h⟩ := TStepL.exists_update (prog := rprog N)
    (hr.wf.tview (TId.recv r)) (hr.wf.rel (TId.recv r)) (hr.wf.cur (TId.recv r)) hr.wf.msgWf
    hr.wf.msgClosed hp hd hm1 hv
  exact ⟨m2, 𝓥, 𝓝, ht, hv', hlt, StepL.of_tstepL (i := TId.recv r) h⟩

theorem recv_choose {c : Cfg ρ} {r : ρ} {k : Bool → RState}
    (hp : rprog N (c.r r) = .choose k) (b : Bool) :
    StepL (prog N M pay ln) c (c.setR r (k b) (c.th (.recv r)).2 c.mem c.na) :=
  StepL.of_tstepL (i := TId.recv r) (TStepL.exists_choose (prog := rprog N) hp b)

end Steps

/-! ## Reading phases off the latest messages -/

section Phases

variable {N M pay ln}

theorem LatestIs.unique {C : List MsgT} {v v' : ℤ}
    (uniq : ∀ a ∈ C, ∀ b ∈ C, a.time = b.time → a = b)
    (h1 : LatestIs C v) (h2 : LatestIs C v') : v = v' := by
  obtain ⟨a, ha, hav⟩ := h1
  obtain ⟨b, hb, hbv⟩ := h2
  have : b = a := ha.eq_of_le uniq hb.1 (hb.2 a ha.1)
  rw [this, hav] at hbv; exact Option.some.inj hbv

theorem PhaseOK.pub_own {c : Cfg ρ} {j s : ℕ} (h : PhaseOK pay ln c j (.pub s)) :
    LatestIs (c.mem (.own j)) 1 :=
  let ⟨_, _, _, _, _, o, _, ho, hov, _⟩ := h; ⟨o, ho, hov⟩

theorem PhaseOK.pub_cseq {c : Cfg ρ} {j s : ℕ} (h : PhaseOK pay ln c j (.pub s)) :
    LatestIs (c.mem (.cseq j)) (s : ℤ) :=
  let ⟨_, _, _, _, _, _, q, _, _, _, hq, hqv, _⟩ := h; ⟨q, hq, hqv⟩

theorem PhaseOK.free_own {c : Cfg ρ} {j : ℕ} (h : PhaseOK pay ln c j .free) :
    LatestIs (c.mem (.own j)) 0 :=
  let ⟨_, _, _, _, f, hf, hfv, _⟩ := h; ⟨f, hf, hfv⟩

/-- A buffer whose latest `client_owned` is `true` and whose latest
`client_seq` is `s`, and which the sender is not working on, is published
with `s`. -/
theorem Inv.pub_of {c : Cfg ρ} (h : Inv pay ln c) {j s : ℕ}
    (ho : LatestIs (c.mem (.own j)) 1) (hq : LatestIs (c.mem (.cseq j)) (s : ℤ))
    (hf : c.s.pc.fill ≠ some j) (hs : c.s.pc.sealing ≠ some j) :
    PhaseOK pay ln c j (.pub s) := by
  obtain ⟨ph, hph⟩ := h.phase j
  match ph, hph with
  | .free, hph' =>
    exact absurd (LatestIs.unique (h.gen.uniq _) hph'.free_own ho) (by decide)
  | .fill, hph' => exact absurd hph'.1 hf
  | .sealing, hph' => exact absurd hph'.1 hs
  | .pub s', hph' =>
    have := LatestIs.unique (h.gen.uniq _) hph'.pub_cseq hq
    have : s' = s := by omega
    rw [this] at hph'; exact hph'

/-- A buffer whose latest `client_owned` is `false`, and which the sender is
not working on, is free. -/
theorem Inv.free_of {c : Cfg ρ} (h : Inv pay ln c) {j : ℕ}
    (ho : LatestIs (c.mem (.own j)) 0)
    (hf : c.s.pc.fill ≠ some j) (hs : c.s.pc.sealing ≠ some j) :
    PhaseOK pay ln c j .free := by
  obtain ⟨ph, hph⟩ := h.phase j
  match ph, hph with
  | .free, hph' => exact hph'
  | .fill, hph' => exact absurd hph'.1 hf
  | .sealing, hph' => exact absurd hph'.1 hs
  | .pub s', hph' =>
    exact absurd (LatestIs.unique (h.gen.uniq _) hph'.pub_own ho) (by decide)

/-- A buffer the sender is not working on is free or published. -/
theorem Inv.free_or_pub {c : Cfg ρ} (h : Inv pay ln c) (j : ℕ)
    (hf : c.s.pc.fill ≠ some j) (hs : c.s.pc.sealing ≠ some j) :
    PhaseOK pay ln c j .free ∨ ∃ s, PhaseOK pay ln c j (.pub s) := by
  obtain ⟨ph, hph⟩ := h.phase j
  match ph, hph with
  | .free, hph' => exact Or.inl hph'
  | .fill, hph' => exact absurd hph'.1 hf
  | .sealing, hph' => exact absurd hph'.1 hs
  | .pub s', hph' => exact Or.inr ⟨s', hph'⟩

/-- Two published buffers with the same sequence number are the same. -/
theorem Inv.pub_unique {c : Cfg ρ} (h : Inv pay ln c) {i j s : ℕ}
    (hi : PhaseOK pay ln c i (.pub s)) (hj : PhaseOK pay ln c j (.pub s)) : i = j := by
  obtain ⟨qi, hqi, hqiv⟩ := hi.pub_cseq
  obtain ⟨qj, hqj, hqjv⟩ := hj.pub_cseq
  exact h.cseqUniq i j qi hqi.1 qj hqj.1 _ hqiv hqjv (by rw [NO_SEQ]; omega)

end Phases

/-! ## Scanning distance -/

/-- Steps from buffer `i` to buffer `j` when scanning `0, 1, …, N - 1, 0, …`. -/
def dist (N i j : ℕ) : ℕ := if i ≤ j then j - i else N - i + j

theorem next_idx {N i : ℕ} (hi : i < N) :
    (i + 1) % N = if i + 1 < N then i + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : i + 1 = N := by omega
    rw [this, Nat.mod_self]

theorem dist_next {N i j : ℕ} (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    dist N ((i + 1) % N) j + 1 = dist N i j := by
  rw [next_idx hi]
  unfold dist
  split_ifs <;> omega

/-- How far a receiver is from accepting buffer `j`. -/
def stage (N j : ℕ) : RPc → ℕ
  | .scan _ i => dist N i j + 5
  | .own _ _ => 4
  | .len _ _ => 3
  | .chunk _ _ _ => 2
  | .cb _ _ _ _ => 1
  | _ => 0

/-! ## Receivers -/

section Receivers

variable {N M pay ln}

theorem pub_after_recv {c c1 : Cfg ρ} (h1 : Inv pay ln c1) {j s : ℕ}
    (hph : PhaseOK pay ln c j (.pub s)) (hs : c1.s = c.s)
    (ho : c1.mem (.own j) = c.mem (.own j)) (hq : c1.mem (.cseq j) = c.mem (.cseq j)) :
    PhaseOK pay ln c1 j (.pub s) :=
  h1.pub_of (ho ▸ hph.pub_own) (hq ▸ hph.pub_cseq) (hs ▸ hph.1) (hs ▸ hph.2.1)

/-- A receiver working on a buffer works on the buffer published with its
ticket. -/
theorem Inv.onBuf_eq {c : Cfg ρ} (h : Inv pay ln c) {r : ρ} {i j s : ℕ}
    (hph : PhaseOK pay ln c j (.pub s)) (hon : (c.r r).pc.onBuf = some i)
    (ht : (c.r r).pc.ticket = some (s : ℤ)) : i = j := by
  obtain ⟨s', o, hpi, -, -, hok⟩ := h.onBuf pay ln hon
  have : (s' : ℤ) = s := by rw [← Option.some.injEq, ← hok.1, ht]
  have : s' = s := by omega
  subst this
  exact h.pub_unique hpi hph

/-- The holder of the ticket of a published buffer accepts it and reaches the
release store. -/
theorem recv_to_rel (hN : 0 < N) (n : ℕ) : ∀ {c : Cfg ρ} {r : ρ} {s j : ℕ},
    Reach N M pay ln c → PhaseOK pay ln c j (.pub s) → j < N → (c.r r).pc.Idx N →
    (c.r r).pc.ticket = some (s : ℤ) → stage N j (c.r r).pc ≤ n →
    ∃ c', Run N M pay ln c c' ∧ (c'.r r).pc = .rel s j ∧ c'.s = c.s ∧
      ∀ r', r' ≠ r → c'.r r' = c.r r' := by
  induction n with
  | zero =>
    intro c r s j hr hph hj hidx ht hst
    have h := reach_inv N M pay ln hr
    cases hpc : (c.r r).pc with
    | rel t i =>
      rw [hpc] at ht; simp only [RPc.ticket, Option.some.injEq] at ht; subst ht
      have := h.onBuf_eq (r := r) (i := i) hph (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
      subst this
      exact ⟨c, .refl, hpc, rfl, fun _ _ => rfl⟩
    | init | fault => rw [hpc] at ht; simp [RPc.ticket] at ht
    | scan _ _ | own _ _ | len _ _ | chunk _ _ _ | cb _ _ _ _ =>
      rw [hpc] at hst; simp [stage] at hst
  | succ n ih =>
    intro c r s j hr hph hj hidx ht hst
    have h := reach_inv N M pay ln hr
    -- continue from a configuration one step later
    have cont : ∀ c1 : Cfg ρ, StepL (prog N M pay ln) c c1 → (c1.r r).pc.Idx N →
        (c1.r r).pc.ticket = some (s : ℤ) → stage N j (c1.r r).pc ≤ n → c1.s = c.s →
        c1.mem (.own j) = c.mem (.own j) → c1.mem (.cseq j) = c.mem (.cseq j) →
        (∀ r', r' ≠ r → c1.r r' = c.r r') →
        ∃ c', Run N M pay ln c c' ∧ (c'.r r).pc = .rel s j ∧ c'.s = c.s ∧
          ∀ r', r' ≠ r → c'.r r' = c.r r' := by
      intro c1 hs1 hidx1 ht1 hst1 hss ho hq hoth
      have hr1 := hr.stepL hs1
      obtain ⟨c', hrun, h1, h2, h3⟩ := ih hr1
        (pub_after_recv (reach_inv N M pay ln hr1) hph hss ho hq) hj hidx1 ht1 hst1
      exact ⟨c', .head hs1 hrun, h1, h2.trans hss, fun r' hr' => (h3 r' hr').trans (hoth r' hr')⟩
    cases hpc : (c.r r).pc with
    | rel t i =>
      rw [hpc] at ht; simp only [RPc.ticket, Option.some.injEq] at ht; subst ht
      have := h.onBuf_eq (r := r) (i := i) hph (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
      subst this
      exact ⟨c, .refl, hpc, rfl, fun _ _ => rfl⟩
    | init | fault => rw [hpc] at ht; simp [RPc.ticket] at ht
    | scan t i =>
      rw [hpc] at ht hidx hst; simp only [RPc.ticket, Option.some.injEq] at ht; subst ht
      simp only [RPc.Idx] at hidx
      simp only [stage] at hst
      obtain ⟨q, hq⟩ := exists_isLatest (hr.wf.nonempty (.cseq i))
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
        (h.atomVal _ (by simp [Loc.IsChunk]) q hq.1)
      obtain ⟨𝓥, 𝓝, hs1⟩ := recv_read hr (r := r) (by simp only [rprog, hpc]; rfl) hq
      by_cases hij : i = j
      · subst hij
        have hvs : v = s := LatestIs.unique (h.gen.uniq _) ⟨q, hq, hv⟩ hph.pub_cseq
        subst hvs
        refine cont _ hs1 ?_ ?_ ?_ (by simp) (by simp) (by simp)
          (fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr')
        · simp [hv, RPc.Idx]; exact hidx
        · simp [hv, RPc.ticket]
        · simp only [Cfg.setR_r_self, hv, ↓reduceIte, stage]
          unfold dist at hst; simp at hst; omega
      · have hvs : v ≠ s := by
          intro hvs; subst hvs
          obtain ⟨qj, hqj, hqjv⟩ := hph.pub_cseq
          exact hij (h.cseqUniq i j q hq.1 qj hqj.1 _ hv hqjv (by rw [NO_SEQ]; omega))
        refine cont _ hs1 ?_ ?_ ?_ (by simp) (by simp) (by simp)
          (fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr')
        · simp only [Cfg.setR_r_self, hv, hvs, ↓reduceIte, RPc.Idx]; exact Nat.mod_lt _ hN
        · simp [hv, hvs, RPc.ticket]
        · simp only [Cfg.setR_r_self, hv, hvs, ↓reduceIte, stage]
          have := dist_next hidx hj hij; omega
    | own t i =>
      rw [hpc] at ht hidx hst; simp only [RPc.ticket, Option.some.injEq] at ht; subst ht
      have := h.onBuf_eq (r := r) (i := i) hph (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
      subst this
      obtain ⟨o, ho, hov⟩ := hph.pub_own
      obtain ⟨𝓥, 𝓝, hs1⟩ := recv_read hr (r := r) (by simp only [rprog, hpc]; rfl) ho
      refine cont _ hs1 ?_ ?_ ?_ (by simp) (by simp) (by simp)
        (fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr')
      · simp [hov, RPc.Idx]; exact hidx
      · simp [hov, RPc.ticket]
      · simp [hov, stage]; simp [stage] at hst; omega
    | len t i =>
      rw [hpc] at ht hidx hst; simp only [RPc.ticket, Option.some.injEq] at ht; subst ht
      have := h.onBuf_eq (r := r) (i := i) hph (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
      subst this
      obtain ⟨m, hm, hmv⟩ := hph.2.2.2.2.1
      obtain ⟨𝓥, 𝓝, hs1⟩ := recv_read hr (r := r) (by simp only [rprog, hpc]; rfl) hm
      refine cont _ hs1 ?_ ?_ ?_ (by simp) (by simp) (by simp)
        (fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr')
      · simp [hmv, RPc.Idx]; exact hidx
      · simp [hmv, RPc.ticket]
      · simp [hmv, stage]; simp [stage] at hst; omega
    | chunk t i n' =>
      rw [hpc] at ht hidx hst; simp only [RPc.ticket, Option.some.injEq] at ht; subst ht
      have := h.onBuf_eq (r := r) (i := i) hph (by simp [hpc, RPc.onBuf]) (by simp [hpc, RPc.ticket])
      subst this
      obtain ⟨m, hm, hmv⟩ := hph.2.2.2.1
      obtain ⟨𝓥, 𝓝, hs1⟩ := recv_read hr (r := r) (by simp only [rprog, hpc]; rfl) hm
      refine cont _ hs1 ?_ ?_ ?_ (by simp) (by simp) (by simp)
        (fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr')
      · simp [hmv, RPc.Idx]; exact hidx
      · simp [hmv, RPc.ticket]
      · simp [hmv, stage]; simp [stage] at hst; omega
    | cb t i n' p =>
      rw [hpc] at ht hidx hst; simp only [RPc.ticket, Option.some.injEq] at ht; subst ht
      have hs1 := recv_choose (N := N) (M := M) (pay := pay) (ln := ln) (c := c) (r := r)
        (by simp only [rprog, hpc]; rfl) true
      refine cont _ hs1 ?_ ?_ ?_ (by simp) (by simp) (by simp)
        (fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr')
      · simp [RPc.Idx]; exact hidx
      · simp [RPc.ticket]
      · simp [stage]

end Receivers

theorem latestIs_add_top {C : List MsgT} {m : MsgT} {v : ℤ}
    (hlt : ∀ m' ∈ C, m'.time < m.time) (hv : m.val = some v) : LatestIs (m :: C) v :=
  ⟨m, ⟨List.mem_cons_self, fun m' hm' => by
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact le_rfl
    · exact (hlt m' hm').le⟩, hv⟩

section Receivers2

variable {N M pay ln}

/-- A receiver at the release store releases its buffer. -/
theorem recv_release {c : Cfg ρ} (hr : Reach N M pay ln c) {r : ρ} {t : ℤ} {j : ℕ}
    (hpc : (c.r r).pc = .rel t j) :
    ∃ c1 : Cfg ρ, StepL (prog N M pay ln) c c1 ∧ (c1.r r).pc = .init ∧ c1.s = c.s ∧
      (∀ r', r' ≠ r → c1.r r' = c.r r') ∧ LatestIs (c1.mem (.own j)) 0 ∧
      (∀ l, l ≠ .own j → c1.mem l = c.mem l) ∧ (c1.r r).log = (c.r r).log := by
  obtain ⟨m, 𝓥, 𝓝, hv, hlt, hs⟩ := recv_write hr (r := r) (by simp only [rprog, hpc]; rfl)
  refine ⟨_, hs, by simp, by simp, fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr', ?_,
    fun l hl => by simp [hl], by simp⟩
  simp only [Cfg.setR_mem, Memory.add_self]
  exact latestIs_add_top hlt hv

/-- A receiver at `request_ticket` takes the next ticket. -/
theorem recv_ticket {c : Cfg ρ} (hr : Reach N M pay ln c) {r : ρ}
    (hpc : (c.r r).pc = .init) :
    ∃ (c1 : Cfg ρ) (m1 : MsgT) (τ : ℤ), IsLatest (c.mem .tick) m1 ∧ m1.val = some τ ∧
      StepL (prog N M pay ln) c c1 ∧ (c1.r r).pc = .scan τ 0 ∧ c1.s = c.s ∧
      (∀ r', r' ≠ r → c1.r r' = c.r r') ∧ (∀ l, l ≠ .tick → c1.mem l = c.mem l) ∧
      (c1.r r).log = (c.r r).log := by
  have h := reach_inv N M pay ln hr
  obtain ⟨m1, hm1⟩ := exists_isLatest (hr.wf.nonempty .tick)
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.1 (h.atomVal _ (by simp [Loc.IsChunk]) m1 hm1.1)
  obtain ⟨m2, 𝓥, 𝓝, -, -, -, hs⟩ :=
    recv_update hr (r := r) (by simp only [rprog, hpc]; rfl) hm1 hτ
  exact ⟨_, m1, τ, hm1, hτ, hs, by simp, by simp, fun r' hr' => Cfg.setR_r_ne _ _ _ _ _ hr',
    fun l hl => by simp [hl], by simp⟩

end Receivers2

/-! ## The sender -/

section Sender

variable {N M pay ln}

/-- The sender scans for a buffer and takes one; buffer `j` is free. -/
theorem sender_alloc (hN : 0 < N) {j : ℕ} (hj : j < N) (n : ℕ) : ∀ {c : Cfg ρ} {k : ℕ}
    {b : Bool} {i : ℕ}, Reach N M pay ln c → c.s.pc = .alloc k b i → i < N →
    LatestIs (c.mem (.own j)) 0 → dist N i j ≤ n →
    ∃ c' i', Run N M pay ln c c' ∧ c'.s.pc = .chunk k b i' ∧ i' < N ∧
      c'.s.log = c.s.log ∧ (∀ r, c'.r r = c.r r) ∧ c'.mem = c.mem := by
  induction n with
  | zero =>
    intro c k b i hr hpc hi hfree hd
    have hij : i = j := by unfold dist at hd; split_ifs at hd <;> omega
    subst hij
    obtain ⟨o, ho, hov⟩ := hfree
    obtain ⟨𝓥, 𝓝, hs⟩ := sender_read hr (by simp only [sprog, hpc]; rfl) ho
    exact ⟨_, i, .single hs, by simp [hov], hi, by simp [hov], fun r => by simp, rfl⟩
  | succ n ih =>
    intro c k b i hr hpc hi hfree hd
    have h := reach_inv N M pay ln hr
    obtain ⟨o, ho⟩ := exists_isLatest (hr.wf.nonempty (.own i))
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.atomVal _ (by simp [Loc.IsChunk]) o ho.1)
    obtain ⟨𝓥, 𝓝, hs⟩ := sender_read hr (by simp only [sprog, hpc]; rfl) ho
    by_cases hv0 : v = 0
    · subst hv0
      exact ⟨_, i, .single hs, by simp [hv], hi, by simp [hv], fun r => by simp, rfl⟩
    · have hij : i ≠ j := by
        rintro rfl
        exact hv0 (LatestIs.unique (h.gen.uniq _) ⟨o, ho, hv⟩ hfree)
      obtain ⟨c', i', hrun, h1, h2, h3, h4, h5⟩ := ih (k := k) (b := b) (i := (i + 1) % N) (hr.stepL hs)
        (by simp [hv, hv0]) (Nat.mod_lt _ hN) (by simpa using hfree)
        (by have := dist_next hi hj hij; omega)
      exact ⟨c', i', .head hs hrun, h1, h2, by simpa [hv, hv0] using h3,
        fun r => by simpa using h4 r,
        by simpa using h5⟩

/-- The sender fills and publishes the buffer it took. -/
theorem sender_publish {c : Cfg ρ} (hr : Reach N M pay ln c) {k : ℕ} {b : Bool} {j : ℕ}
    (hpc : c.s.pc = .chunk k b j ∨ c.s.pc = .len k b j ∨ c.s.pc = .own k b j ∨
      c.s.pc = .fadd k b j ∨ ∃ s, c.s.pc = .pub k b j s) :
    ∃ c', Run N M pay ln c c' ∧
      (c'.s.pc = (if b then .spin k j else .start (k + 1))) ∧ (∀ r, c'.r r = c.r r) := by
  -- the publication step
  have pub : ∀ {c : Cfg ρ}, Reach N M pay ln c → (∃ s, c.s.pc = .pub k b j s) →
      ∃ c', Run N M pay ln c c' ∧
        (c'.s.pc = (if b then .spin k j else .start (k + 1))) ∧ (∀ r, c'.r r = c.r r) := by
    intro c hr ⟨s, hpc⟩
    obtain ⟨m, 𝓥, 𝓝, -, -, hs⟩ := sender_write hr (by simp only [sprog, hpc]; rfl)
    exact ⟨_, .single hs, by simp, fun r => by simp⟩
  have fadd : ∀ {c : Cfg ρ}, Reach N M pay ln c → c.s.pc = .fadd k b j →
      ∃ c', Run N M pay ln c c' ∧
        (c'.s.pc = (if b then .spin k j else .start (k + 1))) ∧ (∀ r, c'.r r = c.r r) := by
    intro c hr hpc
    have h := reach_inv N M pay ln hr
    obtain ⟨m1, hm1⟩ := exists_isLatest (hr.wf.nonempty .curSeq)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
      (h.atomVal _ (by simp [Loc.IsChunk]) m1 hm1.1)
    obtain ⟨m2, 𝓥, 𝓝, -, -, -, hs⟩ := sender_update hr (by simp only [sprog, hpc]; rfl) hm1 hv
    obtain ⟨c', h1, h2, h3⟩ := pub (hr.stepL hs) ⟨v, by simp⟩
    exact ⟨c', .head hs h1, h2, fun r => by simpa using h3 r⟩
  have own : ∀ {c : Cfg ρ}, Reach N M pay ln c → c.s.pc = .own k b j →
      ∃ c', Run N M pay ln c c' ∧
        (c'.s.pc = (if b then .spin k j else .start (k + 1))) ∧ (∀ r, c'.r r = c.r r) := by
    intro c hr hpc
    obtain ⟨m, 𝓥, 𝓝, -, -, hs⟩ := sender_write hr (by simp only [sprog, hpc]; rfl)
    obtain ⟨c', h1, h2, h3⟩ := fadd (hr.stepL hs) (by simp)
    exact ⟨c', .head hs h1, h2, fun r => by simpa using h3 r⟩
  have len : ∀ {c : Cfg ρ}, Reach N M pay ln c → c.s.pc = .len k b j →
      ∃ c', Run N M pay ln c c' ∧
        (c'.s.pc = (if b then .spin k j else .start (k + 1))) ∧ (∀ r, c'.r r = c.r r) := by
    intro c hr hpc
    obtain ⟨m, 𝓥, 𝓝, -, -, hs⟩ := sender_write hr (by simp only [sprog, hpc]; rfl)
    obtain ⟨c', h1, h2, h3⟩ := own (hr.stepL hs) (by simp)
    exact ⟨c', .head hs h1, h2, fun r => by simpa using h3 r⟩
  have chunk : ∀ {c : Cfg ρ}, Reach N M pay ln c → c.s.pc = .chunk k b j →
      ∃ c', Run N M pay ln c c' ∧
        (c'.s.pc = (if b then .spin k j else .start (k + 1))) ∧ (∀ r, c'.r r = c.r r) := by
    intro c hr hpc
    obtain ⟨m, 𝓥, 𝓝, -, -, hs⟩ := sender_write hr (by simp only [sprog, hpc]; rfl)
    obtain ⟨c', h1, h2, h3⟩ := len (hr.stepL hs) (by simp)
    exact ⟨c', .head hs h1, h2, fun r => by simpa using h3 r⟩
  rcases hpc with hpc | hpc | hpc | hpc | hpc
  · exact chunk hr hpc
  · exact len hr hpc
  · exact own hr hpc
  · exact fadd hr hpc
  · exact pub hr hpc

/-- A waiting sender sees its buffer released. -/
theorem sender_unspin {c : Cfg ρ} (hr : Reach N M pay ln c) {k i : ℕ}
    (hpc : c.s.pc = .spin k i) (hfree : LatestIs (c.mem (.own i)) 0) :
    ∃ c1 : Cfg ρ, StepL (prog N M pay ln) c c1 ∧ c1.s.pc = .start (k + 1) ∧ ∀ r, c1.r r = c.r r := by
  obtain ⟨o, ho, hov⟩ := hfree
  obtain ⟨𝓥, 𝓝, hs⟩ := sender_read hr (by simp only [sprog, hpc]; rfl) ho
  exact ⟨_, hs, by simp [hov], fun r => by simp⟩

end Sender

/-! ## Delivering the messages in order -/

section Deliver

variable {N M pay ln}

theorem consumed_run {c c' : Cfg ρ} (hr : Reach N M pay ln c) (h : Run N M pay ln c c')
    {v : ℤ} (hv : Consumed c v) : Consumed c' v := by
  induction h with
  | refl => exact hv
  | @tail c1 c2 h12 hs ih =>
    exact consumed_step N M pay ln (hr.run h12) hs.toStep ih

theorem PhaseOK.pub_rel {c : Cfg ρ} {j s : ℕ} (h : PhaseOK pay ln c j (.pub s))
    (hc : Consumed c (s : ℤ)) : ∃ r, (c.r r).pc = .rel (s : ℤ) j :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrel⟩ := h; hrel hc

/-- A consumed ticket was handed out. -/
theorem Inv.issued_of_consumed {c : Cfg ρ} (h : Inv pay ln c) {t : ℤ}
    (hc : Consumed c t) : Issued c t := by
  obtain ⟨r, hr⟩ := hc
  obtain ⟨-, m, hm, hmv⟩ := h.rTix r t (tix_log hr)
  exact ⟨m, hm, hmv⟩

/-- Tickets are handed out in order. -/
theorem Inv.issued_lt {c : Cfg ρ} (h : Inv pay ln c) {t s : ℤ} (hs : 0 ≤ s)
    (ht : Issued c t) (hns : ¬ Issued c s) : t < s := by
  by_contra hle
  obtain ⟨m, hm, hmv⟩ := ht
  have hval := h.tickVal m hm
  rw [hmv, Option.some.injEq] at hval
  obtain ⟨m', hm', ht'⟩ := h.tickDown m hm (s.toNat + 2) (by omega) (by omega)
  have hval' := h.tickVal m' hm'
  exact hns ⟨m', hm', by rw [hval', ht']; congr 1; omega⟩

/-- An unconsumed published sequence number has its buffer. -/
theorem live_pub (hN : 0 < N) {c : Cfg ρ} (hr : Reach N M pay ln c) {s : ℕ}
    (hs : s < c.s.pc.npub) (hnc : ¬ Consumed c (s : ℤ)) :
    ∃ j, j < N ∧ PhaseOK pay ln c j (.pub s) := by
  have h := reach_inv N M pay ln hr
  obtain ⟨j, hjN, q, hq, hqv⟩ := (reach_pinv N M pay ln hN hr).live s hs hnc
  refine ⟨j, hjN, ?_⟩
  have hno : NoLive c j → False := fun hnl => by
    rcases hnl q hq.1 _ hqv with h1 | h1
    · rw [NO_SEQ] at h1; omega
    · exact hnc h1
  obtain ⟨ph, hph⟩ := h.phase j
  match ph, hph with
  | .free, hph' => exact (hno hph'.2.2.2.1).elim
  | .fill, hph' => exact (hno hph'.2.2.1).elim
  | .sealing, hph' => exact (hno hph'.2.2.1).elim
  | .pub s', hph' =>
    have := LatestIs.unique (h.gen.uniq _) hph'.pub_cseq ⟨q, hq, hqv⟩
    have : s' = s := by omega
    rw [this] at hph'; exact hph'

/-- Free a buffer the sender is not working on, if all published messages are
consumed. -/
theorem free_buffer {c : Cfg ρ} (hr : Reach N M pay ln c) {j : ℕ}
    (hf : c.s.pc.fill ≠ some j) (hsl : c.s.pc.sealing ≠ some j)
    (hall : ∀ k < c.s.pc.npub, Consumed c (k : ℤ)) :
    ∃ c', Run N M pay ln c c' ∧ c'.s = c.s ∧ LatestIs (c'.mem (.own j)) 0 := by
  have h := reach_inv N M pay ln hr
  rcases h.free_or_pub j hf hsl with hfr | ⟨s, hph⟩
  · exact ⟨c, .refl, rfl, hfr.free_own⟩
  · obtain ⟨r, hrel⟩ := hph.pub_rel (hall s hph.2.2.1)
    obtain ⟨c1, hs1, -, hss, -, hlat, -, -⟩ := recv_release hr hrel
    exact ⟨c1, .single hs1, hss, hlat⟩

/-- The sender publishes message `s`, if all earlier ones are consumed. -/
theorem ensure_published (hN : 0 < N) {c : Cfg ρ} (hr : Reach N M pay ln c) {s : ℕ}
    (hsM : s < M) (hall : ∀ k < s, Consumed c (k : ℤ)) :
    ∃ c', Run N M pay ln c c' ∧ s < c'.s.pc.npub := by
  have h := reach_inv N M pay ln hr
  have hidx := reach_idx N M pay ln hN hr
  -- the sender is at `s` at least
  have hge : s ≤ c.s.pc.npub := by
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · exact Nat.zero_le _
    · obtain ⟨r, hr'⟩ := hall (s - 1) (by omega)
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hr'
      have := (h.rLog r e he).2.1
      rw [he1] at this; omega
  rcases Nat.lt_or_ge s c.s.pc.npub with hlt | hle
  · exact ⟨c, .refl, hlt⟩
  have hnp : c.s.pc.npub = s := le_antisymm hle hge
  have hall' : ∀ k < c.s.pc.npub, Consumed c (k : ℤ) := fun k hk => hall k (hnp ▸ hk)
  -- publishing from a state that took a buffer
  have fin : ∀ {c : Cfg ρ}, Reach N M pay ln c → ∀ b j, (c.s.pc = .chunk s b j ∨
      c.s.pc = .len s b j ∨ c.s.pc = .own s b j ∨ c.s.pc = .fadd s b j ∨
      ∃ s', c.s.pc = .pub s b j s') → ∃ c', Run N M pay ln c c' ∧ s < c'.s.pc.npub := by
    intro c hr b j hpc
    obtain ⟨c', hrun, hpc', -⟩ := sender_publish hr hpc
    refine ⟨c', hrun, ?_⟩
    rw [hpc']; cases b <;> simp [SPc.npub, SPc.k]
  -- from `alloc`
  have alloc : ∀ {c : Cfg ρ}, Reach N M pay ln c → ∀ b i, c.s.pc = .alloc s b i → i < N →
      (∀ k < c.s.pc.npub, Consumed c (k : ℤ)) →
      ∃ c', Run N M pay ln c c' ∧ s < c'.s.pc.npub := by
    intro c hr b i hpc hi hall
    obtain ⟨c1, hrun1, hss, hfree⟩ := free_buffer hr (j := 0) (by simp [hpc, SPc.fill])
      (by simp [hpc, SPc.sealing]) hall
    have hr1 := hr.run hrun1
    obtain ⟨c2, i', hrun2, hpc2, -⟩ := sender_alloc hN hN (dist N i 0) hr1
      (by rw [hss, hpc]) hi hfree le_rfl
    obtain ⟨c3, hrun3, h3⟩ := fin (hr1.run hrun2) b i' (Or.inl hpc2)
    exact ⟨c3, hrun1.trans (hrun2.trans hrun3), h3⟩
  -- from `start`
  have start : ∀ {c : Cfg ρ}, Reach N M pay ln c → c.s.pc = .start s →
      (∀ k < c.s.pc.npub, Consumed c (k : ℤ)) →
      ∃ c', Run N M pay ln c c' ∧ s < c'.s.pc.npub := by
    intro c hr hpc hall
    have hs1 := sender_choose (N := N) (M := M) (pay := pay) (ln := ln) (c := c)
      (by simp [sprog, hpc, hsM]; rfl) false
    obtain ⟨c', h1, h2⟩ := alloc (hr.stepL hs1) false 0 (by simp) hN
      (by simpa [hpc, SPc.npub, SPc.k] using hall)
    exact ⟨c', .head hs1 h1, h2⟩
  cases hpc : c.s.pc with
  | start k =>
    have : k = s := by rw [← hnp, hpc]; rfl
    subst this; exact start hr hpc hall'
  | alloc k b i =>
    have : k = s := by rw [← hnp, hpc]; rfl
    subst this
    have := hidx.1; rw [hpc] at this
    exact alloc hr b i hpc this.2 hall'
  | chunk k b i =>
    have : k = s := by rw [← hnp, hpc]; rfl
    subst this; exact fin hr b i (Or.inl hpc)
  | len k b i =>
    have : k = s := by rw [← hnp, hpc]; rfl
    subst this; exact fin hr b i (Or.inr (Or.inl hpc))
  | own k b i =>
    have : k = s := by rw [← hnp, hpc]; rfl
    subst this; exact fin hr b i (Or.inr (Or.inr (Or.inl hpc)))
  | fadd k b i =>
    have : k = s := by rw [← hnp, hpc]; rfl
    subst this; exact fin hr b i (Or.inr (Or.inr (Or.inr (Or.inl hpc))))
  | pub k b i s' =>
    have : k = s := by rw [← hnp, hpc]; rfl
    subst this; exact fin hr b i (Or.inr (Or.inr (Or.inr (Or.inr ⟨s', hpc⟩))))
  | spin k i =>
    -- the sender waits for message `k = s - 1`, which is consumed
    have hks : k + 1 = s := by rw [← hnp, hpc]; rfl
    obtain ⟨c1, hrun1, hss, hfree⟩ := free_buffer hr (j := i) (by simp [hpc, SPc.fill])
      (by simp [hpc, SPc.sealing]) hall'
    have hr1 := hr.run hrun1
    obtain ⟨c2, hs2, hpc2, -⟩ := sender_unspin hr1 (by rw [hss, hpc]) hfree
    have hr2 := hr1.stepL hs2
    rw [hks] at hpc2
    obtain ⟨c3, h3, h3'⟩ := start hr2 hpc2 (fun k hk => by
      rw [hpc2] at hk; simp [SPc.npub, SPc.k] at hk
      exact consumed_run hr (hrun1.trans (.single hs2)) (hall k hk))
    exact ⟨c3, hrun1.trans (.head hs2 h3), h3'⟩
  | fault => exact absurd hpc h.sFault

end Deliver

section Deliver2

variable {N M pay ln}

/-- Some receiver takes ticket `s`, if all earlier ones are consumed. -/
theorem ensure_ticket (hN : 0 < N) [Nonempty ρ] {c : Cfg ρ} (hr : Reach N M pay ln c) {s : ℕ}
    (hall : ∀ k < s, Consumed c (k : ℤ)) (hnc : ¬ Consumed c (s : ℤ)) :
    ∃ c' r, Run N M pay ln c c' ∧ (s : ℤ) ∈ (c'.r r).pc.held ∧ c'.s = c.s ∧
      ¬ Consumed c' (s : ℤ) := by
  have h := reach_inv N M pay ln hr
  by_cases hheld : ∃ r, (s : ℤ) ∈ (c.r r).pc.held
  · obtain ⟨r, hr'⟩ := hheld
    exact ⟨c, r, .refl, hr', rfl, hnc⟩
  push_neg at hheld
  -- ticket `s` was not handed out yet
  have hni : ¬ Issued c (s : ℤ) := by
    intro hi
    obtain ⟨r, hr'⟩ := (reach_pinv N M pay ln hN hr).issued s (by omega) hi
    rcases List.mem_append.1 hr' with h1 | h1
    · exact hheld r h1
    · exact hnc ⟨r, h1⟩
  -- so any receiver holds no ticket
  obtain ⟨r0⟩ := ‹Nonempty ρ›
  have hfree : ∀ t, t ∉ (c.r r0).pc.held := by
    intro t ht
    have ht0 := h.ticket_nonneg pay ln ht
    obtain ⟨-, m, hm, hmv⟩ := h.rTix r0 t (tix_held ht)
    have hlt := h.issued_lt (by omega) ⟨m, hm, hmv⟩ hni
    exact h.held_not_consumed pay ln ht
      (by have := hall t.toNat (by omega); rwa [Int.toNat_of_nonneg ht0] at this)
  -- bring it to `request_ticket`
  obtain ⟨c1, hrun1, hpc1, hss1, hoth1, htick1, hlog1⟩ : ∃ c1 : Cfg ρ, Run N M pay ln c c1 ∧
      (c1.r r0).pc = .init ∧ c1.s = c.s ∧ (∀ r', r' ≠ r0 → c1.r r' = c.r r') ∧
      c1.mem .tick = c.mem .tick ∧ (c1.r r0).log = (c.r r0).log := by
    cases hpc : (c.r r0).pc with
    | init => exact ⟨c, .refl, hpc, rfl, fun _ _ => rfl, rfl, rfl⟩
    | rel t j =>
      obtain ⟨c1, hs1, h1, h2, h3, -, h5, h6⟩ := recv_release hr hpc
      exact ⟨c1, .single hs1, h1, h2, h3, h5 _ (by simp), h6⟩
    | fault => exact absurd hpc (h.rFault r0)
    | scan t _ | own t _ | len t _ | chunk t _ _ | cb t _ _ _ =>
      exact absurd (by simp [hpc, RPc.held]) (hfree t)
  have hr1 := hr.run hrun1
  have h1 := reach_inv N M pay ln hr1
  obtain ⟨c2, m1, τ, hm1, hτ, hs2, hpc2, hss2, hoth2, -, hlog2⟩ := recv_ticket hr1 hpc1
  -- the ticket it takes is `s`
  have hτs : τ = s := by
    have hval := h1.tickVal m1 hm1.1
    rw [hτ, Option.some.injEq] at hval
    have hpos := h1.gen.pos _ m1 hm1.1
    apply le_antisymm
    · by_contra hlt
      obtain ⟨m', hm', ht'⟩ := h1.tickDown m1 hm1.1 (s + 2) (by omega) (by omega)
      have hval' := h1.tickVal m' hm'
      exact hni ⟨m', by rwa [← htick1], by rw [hval', ht']; congr 1; omega⟩
    · rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · rw [hs0]; push_cast; omega
      · obtain ⟨m, hm, hmv⟩ := h.issued_of_consumed (hall (s - 1) (by omega))
        rw [← htick1] at hm
        have := h1.tickVal m hm
        rw [hmv, Option.some.injEq] at this
        have := hm1.2 m hm
        omega
  subst hτs
  refine ⟨c2, r0, hrun1.trans (.single hs2), by simp [hpc2, RPc.held], hss2.trans hss1, ?_⟩
  -- nobody logged anything
  rintro ⟨r, hr'⟩
  by_cases hrr : r = r0
  · subst hrr
    exact hnc ⟨r, by rwa [hlog2, hlog1] at hr'⟩
  · exact hnc ⟨r, by rwa [hoth2 r hrr, hoth1 r hrr] at hr'⟩

end Deliver2

theorem RPc.ticket_of_held {pc : RPc} {t : ℤ} (h : t ∈ pc.held) : pc.ticket = some t := by
  cases pc <;> simp_all [RPc.held, RPc.ticket]

section Deliver3

variable {N M pay ln}

/-- Deliver message `s`, if all earlier ones are consumed. -/
theorem deliver (hN : 0 < N) [Nonempty ρ] {c : Cfg ρ} (hr : Reach N M pay ln c) {s : ℕ}
    (hsM : s < M) (hall : ∀ k < s, Consumed c (k : ℤ)) :
    ∃ c', Run N M pay ln c c' ∧ ∀ k < s + 1, Consumed c' (k : ℤ) := by
  have done : ∀ c', Run N M pay ln c c' → Consumed c' (s : ℤ) →
      ∀ k < s + 1, Consumed c' (k : ℤ) := by
    intro c' hrun hc k hk
    rcases Nat.lt_or_ge k s with hks | hks
    · exact consumed_run hr hrun (hall k hks)
    · have : k = s := by omega
      subst this; exact hc
  by_cases hc : Consumed c (s : ℤ)
  · exact ⟨c, .refl, done c .refl hc⟩
  -- publish `s`
  obtain ⟨c1, hrun1, hpub1⟩ := ensure_published hN hr hsM hall
  have hr1 := hr.run hrun1
  have hall1 : ∀ k < s, Consumed c1 (k : ℤ) := fun k hk => consumed_run hr hrun1 (hall k hk)
  by_cases hc1 : Consumed c1 (s : ℤ)
  · exact ⟨c1, hrun1, done c1 hrun1 hc1⟩
  -- hand out ticket `s`
  obtain ⟨c2, r, hrun2, hheld, hss2, hnc2⟩ := ensure_ticket hN hr1 hall1 hc1
  have hr2 := hr1.run hrun2
  obtain ⟨j, hjN, hph⟩ := live_pub hN hr2 (by rw [hss2]; exact hpub1) hnc2
  -- its holder accepts the buffer
  obtain ⟨c3, hrun3, hpc3, -, -⟩ := recv_to_rel hN _ hr2 hph hjN
    ((reach_idx N M pay ln hN hr2).2 r) (RPc.ticket_of_held hheld) le_rfl
  have hr3 := hr2.run hrun3
  have hrun : Run N M pay ln c c3 := hrun1.trans (hrun2.trans hrun3)
  exact ⟨c3, hrun, done c3 hrun ⟨r, (reach_inv N M pay ln hr3).rRel r _ j hpc3⟩⟩

/-- Once every message is consumed, the sender finishes. -/
theorem finish (hN : 0 < N) {c : Cfg ρ} (hr : Reach N M pay ln c)
    (hall : ∀ k < M, Consumed c (k : ℤ)) :
    ∃ c', Run N M pay ln c c' ∧ c'.s.pc = .start M := by
  have h := reach_inv N M pay ln hr
  have hidx := (reach_idx N M pay ln hN hr).1
  have hge : M ≤ c.s.pc.npub := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · omega
    · obtain ⟨r, hr'⟩ := hall (M - 1) (by omega)
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hr'
      have := (h.rLog r e he).2.1
      rw [he1] at this; omega
  cases hpc : c.s.pc with
  | start k =>
    rw [hpc] at hidx hge; simp only [SPc.Idx] at hidx; simp only [SPc.npub, SPc.k] at hge
    have : k = M := by omega
    subst this; exact ⟨c, .refl, hpc⟩
  | spin k i =>
    rw [hpc] at hidx hge; simp only [SPc.Idx] at hidx; simp only [SPc.npub] at hge
    have hkM : k + 1 = M := by omega
    obtain ⟨c1, hrun1, hss, hfree⟩ := free_buffer hr (j := i) (by simp [hpc, SPc.fill])
      (by simp [hpc, SPc.sealing])
      (fun k' hk' => hall k' (by rw [hpc] at hk'; simp [SPc.npub] at hk'; omega))
    obtain ⟨c2, hs2, hpc2, -⟩ := sender_unspin (hr.run hrun1) (by rw [hss, hpc]) hfree
    exact ⟨c2, hrun1.tail hs2, by rw [hpc2, hkM]⟩
  | alloc k b i | chunk k b i | len k b i | own k b i | fadd k b i | pub k b i _ =>
    rw [hpc] at hidx hge; simp only [SPc.Idx] at hidx; simp only [SPc.npub, SPc.k] at hge
    omega
  | fault => exact absurd hpc h.sFault

end Deliver3

/-! ## No stranding -/

/-- **No stranding.** For at least one buffer and one receiver, from every
reachable configuration there is a continuation of latest steps (every load
reads the latest write, every store goes last) after which the sender has
sent all `M` messages and every message `k < M` has been accepted by some
receiver, with its payload and length. -/
theorem progress (hN : 0 < N) [Nonempty ρ] {c : Cfg ρ} (hr : Reach N M pay ln c) :
    ∃ c' : Cfg ρ, Relation.ReflTransGen (StepL (prog N M pay ln)) c c' ∧
      c'.s.pc = .start M ∧ ∀ k < M, ∃ r, ((k : ℤ), pay k, ln k) ∈ (c'.r r).log := by
  have key : ∀ s ≤ M, ∃ c', Run N M pay ln c c' ∧ ∀ k < s, Consumed c' (k : ℤ) := by
    intro s
    induction s with
    | zero => exact fun _ => ⟨c, .refl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ s ih =>
      intro hs
      obtain ⟨c1, hrun1, hall1⟩ := ih (by omega)
      obtain ⟨c2, hrun2, hall2⟩ := deliver hN (hr.run hrun1) (by omega) hall1
      exact ⟨c2, hrun1.trans hrun2, hall2⟩
  obtain ⟨c1, hrun1, hall1⟩ := key M le_rfl
  have hr1 := hr.run hrun1
  obtain ⟨c2, hrun2, hpc2⟩ := finish hN hr1 hall1
  have hr2 := hr1.run hrun2
  have h2 := reach_inv N M pay ln hr2
  refine ⟨c2, hrun1.trans hrun2, hpc2, fun k hk => ?_⟩
  obtain ⟨r, hr'⟩ := consumed_run hr1 hrun2 (hall1 k hk)
  obtain ⟨e, he, he1⟩ := List.mem_map.1 hr'
  obtain ⟨-, -, e3, e4⟩ := h2.rLog r e he
  refine ⟨r, ?_⟩
  obtain ⟨a, b, d⟩ := e
  simp only at he1 e3 e4
  subst he1
  simp only [Int.toNat_natCast] at e3 e4
  rw [e3, e4] at he; exact he

end Mempipe
