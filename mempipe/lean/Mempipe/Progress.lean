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

end Mempipe
