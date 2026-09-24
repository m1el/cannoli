import Mempipe.Program
import ORC11.Lemmas

/-!
# The safety invariant

Each buffer is in one of four phases:

* `free`: the latest `client_owned[i]` message is `false`; any message the
  sender can still read as `false` is that one, and every non-atomic read of
  the chunk is in the sender's view or in that message's view.
* `fill`: the sender acquired the buffer and is writing the chunk, the length
  and `client_owned = true`.
* `sealing`: `client_owned[i] = true` is written; the sender takes a sequence
  number and publishes it.
* `pub s`: sequence number `s` is the latest `client_seq[i]`; its message view
  covers the chunk, the length and `client_owned`. Only the holder of ticket
  `s` works on the buffer, and every non-atomic read of the chunk is in the
  sender's view or in the view of that ticket's holder. Once `s` is consumed,
  its holder is about to release the buffer.

Around that, global facts: the sender is the only writer of chunks, lengths
and sequence numbers; the two counters (`cur_seq`, the ticket counter) are
contiguous chains of updates; tickets are unique; logs are correct.
-/

namespace Mempipe

open ORC11

variable {ρ : Type} [DecidableEq ρ]

abbrev Mem := Memory Loc ℤ
abbrev MsgT := Msg Loc ℤ

/-! ## Accessors -/

namespace Cfg

def s (c : Cfg ρ) : SState := (c.th .sender).1
/-- The sender's current view. -/
def vs (c : Cfg ρ) : View Loc := (c.th .sender).2.cur
def r (c : Cfg ρ) (r : ρ) : RState := (c.th (.recv r)).1
/-- A receiver's current view. -/
def vr (c : Cfg ρ) (r : ρ) : View Loc := (c.th (.recv r)).2.cur

/-- The configuration after a sender step. -/
def setS (c : Cfg ρ) (σ : SState) (𝓥 : TView Loc) (M : Mem) (𝓝 : View Loc) : Cfg ρ :=
  ⟨Function.update c.th .sender (σ, 𝓥), M, 𝓝⟩

/-- The configuration after a step of receiver `r0`. -/
def setR (c : Cfg ρ) (r0 : ρ) (σ : RState) (𝓥 : TView Loc) (M : Mem) (𝓝 : View Loc) :
    Cfg ρ :=
  ⟨Function.update c.th (.recv r0) (σ, 𝓥), M, 𝓝⟩

variable (c : Cfg ρ) (σ : SState) (σr : RState) (𝓥 : TView Loc) (M : Mem) (𝓝 : View Loc)

@[simp] theorem setS_s : (c.setS σ 𝓥 M 𝓝).s = σ := by simp [setS, s]
@[simp] theorem setS_vs : (c.setS σ 𝓥 M 𝓝).vs = 𝓥.cur := by simp [setS, vs]
@[simp] theorem setS_r (r : ρ) : (c.setS σ 𝓥 M 𝓝).r r = c.r r := by
  simp [setS, Cfg.r, Function.update_of_ne (show TId.recv r ≠ TId.sender by simp)]
@[simp] theorem setS_vr (r : ρ) : (c.setS σ 𝓥 M 𝓝).vr r = c.vr r := by
  simp [setS, vr, Function.update_of_ne (show TId.recv r ≠ TId.sender by simp)]
@[simp] theorem setS_mem : (c.setS σ 𝓥 M 𝓝).mem = M := rfl
@[simp] theorem setS_na : (c.setS σ 𝓥 M 𝓝).na = 𝓝 := rfl

@[simp] theorem setR_s (r0 : ρ) : (c.setR r0 σr 𝓥 M 𝓝).s = c.s := by
  simp [setR, s, Function.update_of_ne (show TId.sender ≠ TId.recv r0 by simp)]
@[simp] theorem setR_vs (r0 : ρ) : (c.setR r0 σr 𝓥 M 𝓝).vs = c.vs := by
  simp [setR, vs, Function.update_of_ne (show TId.sender ≠ TId.recv r0 by simp)]
@[simp] theorem setR_r_self (r0 : ρ) : (c.setR r0 σr 𝓥 M 𝓝).r r0 = σr := by
  simp [setR, Cfg.r]
@[simp] theorem setR_vr_self (r0 : ρ) : (c.setR r0 σr 𝓥 M 𝓝).vr r0 = 𝓥.cur := by
  simp [setR, vr]
theorem setR_r_ne {r0 r : ρ} (h : r ≠ r0) : (c.setR r0 σr 𝓥 M 𝓝).r r = c.r r := by
  simp [setR, Cfg.r, Function.update_of_ne (show TId.recv r ≠ TId.recv r0 by simp [h])]
theorem setR_vr_ne {r0 r : ρ} (h : r ≠ r0) : (c.setR r0 σr 𝓥 M 𝓝).vr r = c.vr r := by
  simp [setR, vr, Function.update_of_ne (show TId.recv r ≠ TId.recv r0 by simp [h])]
@[simp] theorem setR_mem (r0 : ρ) : (c.setR r0 σr 𝓥 M 𝓝).mem = M := rfl
@[simp] theorem setR_na (r0 : ρ) : (c.setR r0 σr 𝓥 M 𝓝).na = 𝓝 := rfl

end Cfg

variable (N M : ℕ) (pay ln : ℕ → ℤ)

/-- A pool step is a sender step or a receiver step. -/
theorem step_cases {c c' : Cfg ρ} (h : Step (prog N M pay ln) c c') :
    (∃ σ 𝓥 M' 𝓝', TStep (sprog N M pay ln) c.s (c.th .sender).2 c.mem c.na σ 𝓥 M' 𝓝' ∧
      c' = c.setS σ 𝓥 M' 𝓝') ∨
    (∃ r σ 𝓥 M' 𝓝', TStep (rprog N) (c.r r) (c.th (.recv r)).2 c.mem c.na σ 𝓥 M' 𝓝' ∧
      c' = c.setR r σ 𝓥 M' 𝓝') := by
  cases h with
  | mk i hst =>
    cases i with
    | sender => exact Or.inl ⟨_, _, _, _, hst, rfl⟩
    | recv r => exact Or.inr ⟨r, _, _, _, _, hst, rfl⟩

/-! ## Program-counter helpers -/

namespace SPc

/-- The buffer the sender is filling. -/
def fill : SPc → Option ℕ
  | .chunk _ _ i | .len _ _ i | .own _ _ i => some i
  | _ => none

/-- The buffer the sender is sealing. -/
def sealing : SPc → Option ℕ
  | .fadd _ _ i | .pub _ _ i _ => some i
  | _ => none

/-- The index of the message being sent. -/
def k : SPc → ℕ
  | .start k | .alloc k _ _ | .chunk k _ _ | .len k _ _ | .own k _ _ | .fadd k _ _
  | .pub k _ _ _ | .spin k _ => k
  | .fault => 0

/-- Messages published so far. -/
def npub : SPc → ℕ
  | .spin k _ => k + 1
  | pc => pc.k

/-- `cur_seq.fetch_add`s done so far. -/
def nfa : SPc → ℕ
  | .pub k _ _ _ | .spin k _ => k + 1
  | pc => pc.k

end SPc

namespace RPc

/-- The ticket a receiver works with. -/
def ticket : RPc → Option ℤ
  | .scan t _ | .own t _ | .len t _ | .chunk t _ _ | .cb t _ _ _ | .rel t _ => some t
  | .init | .fault => none

/-- The ticket a receiver holds and has not logged yet. -/
def held : RPc → List ℤ
  | .scan t _ | .own t _ | .len t _ | .chunk t _ _ | .cb t _ _ _ => [t]
  | _ => []

/-- The buffer a receiver is processing. -/
def onBuf : RPc → Option ℕ
  | .own _ i | .len _ i | .chunk _ i _ | .cb _ i _ _ | .rel _ i => some i
  | _ => none

end RPc

/-- All tickets of a receiver: the one it holds and the ones it logged. -/
def tix (σ : RState) : List ℤ := σ.pc.held ++ σ.log.map Prod.fst

/-- What the sender has published after `k` messages. -/
def sentLog : ℕ → List Entry
  | 0 => []
  | k + 1 => ((k : ℤ), pay k, ln k) :: sentLog k

/-! ## Memory predicates -/


/-- Every message of the cell is at most `t`. -/
def Below (C : List MsgT) (t : ℕ) : Prop := ∀ m ∈ C, m.time ≤ t

/-- The latest message of the cell has value `v`. -/
def LatestIs (C : List MsgT) (v : ℤ) : Prop := ∃ m, IsLatest C m ∧ m.val = some v

/-- Ticket `v` was consumed: some receiver logged it. -/
def Consumed (c : Cfg ρ) (v : ℤ) : Prop := ∃ r, v ∈ (c.r r).log.map Prod.fst

/-- No receiver works on buffer `i`. -/
def NoRecv (c : Cfg ρ) (i : ℕ) : Prop := ∀ r, (c.r r).pc.onBuf ≠ some i

/-- No sequence number of `client_seq[i]` is waiting to be received. -/
def NoLive (c : Cfg ρ) (i : ℕ) : Prop :=
  ∀ m ∈ c.mem (.cseq i), ∀ v, m.val = some v → v = NO_SEQ ∨ Consumed c v

/-- A receiver working on buffer `i`, published with sequence number `s`
(`client_owned[i] = true` being message `o`), holds ticket `s` and has seen
the whole publication. -/
def RecvOK (c : Cfg ρ) (i s : ℕ) (o : MsgT) (r : ρ) : Prop :=
  (c.r r).pc.ticket = some (s : ℤ) ∧ o.time ≤ (c.vr r (.own i)).w ∧
  Below (c.mem (.chunk i)) (c.vr r (.chunk i)).w ∧
  Below (c.mem (.len i)) (c.vr r (.len i)).w ∧
  (∀ t n, (c.r r).pc = .chunk t i n → n = ln s) ∧
  (∀ t n p, (c.r r).pc = .cb t i n p → n = ln s ∧ p = pay s)

inductive Phase where
  | free
  | fill
  | sealing
  | pub (s : ℕ)

/-- The per-buffer invariant. -/
def PhaseOK (c : Cfg ρ) (i : ℕ) : Phase → Prop
  | .free =>
    c.s.pc.fill ≠ some i ∧ c.s.pc.sealing ≠ some i ∧ NoRecv c i ∧ NoLive c i ∧
    ∃ f, IsLatest (c.mem (.own i)) f ∧ f.val = some 0 ∧
      (∀ m ∈ c.mem (.own i), (c.vs (.own i)).w ≤ m.time → m.val = some 0 →
        m.time = f.time) ∧
      (c.na (.chunk i)).nr ⊆ (c.vs (.chunk i)).nr ∪ ((f.view.getD ⊥) (.chunk i)).nr
  | .fill =>
    c.s.pc.fill = some i ∧ NoRecv c i ∧ NoLive c i ∧
    Below (c.mem (.own i)) (c.vs (.own i)).w ∧
    (c.na (.chunk i)).nr ⊆ (c.vs (.chunk i)).nr ∧
    (∀ k b, c.s.pc = .len k b i → LatestIs (c.mem (.chunk i)) (pay k)) ∧
    (∀ k b, c.s.pc = .own k b i →
      LatestIs (c.mem (.chunk i)) (pay k) ∧ LatestIs (c.mem (.len i)) (ln k))
  | .sealing =>
    c.s.pc.sealing = some i ∧ NoRecv c i ∧ NoLive c i ∧
    (c.na (.chunk i)).nr ⊆ (c.vs (.chunk i)).nr ∧
    LatestIs (c.mem (.chunk i)) (pay c.s.pc.k) ∧ LatestIs (c.mem (.len i)) (ln c.s.pc.k) ∧
    ∃ o, IsLatest (c.mem (.own i)) o ∧ o.val = some 1 ∧ o.time ≤ (c.vs (.own i)).w
  | .pub s =>
    c.s.pc.fill ≠ some i ∧ c.s.pc.sealing ≠ some i ∧ s < c.s.pc.npub ∧
    LatestIs (c.mem (.chunk i)) (pay s) ∧ LatestIs (c.mem (.len i)) (ln s) ∧
    ∃ o q, IsLatest (c.mem (.own i)) o ∧ o.val = some 1 ∧ o.time ≤ (c.vs (.own i)).w ∧
      IsLatest (c.mem (.cseq i)) q ∧ q.val = some (s : ℤ) ∧
      Below (c.mem (.chunk i)) ((q.view.getD ⊥) (.chunk i)).w ∧
      Below (c.mem (.len i)) ((q.view.getD ⊥) (.len i)).w ∧
      o.time ≤ ((q.view.getD ⊥) (.own i)).w ∧
      (∀ m ∈ c.mem (.cseq i), ∀ v, m.val = some v →
        v = NO_SEQ ∨ Consumed c v ∨ m.time = q.time) ∧
      (∀ r, (c.r r).pc.onBuf = some i → RecvOK pay ln c i s o r) ∧
      (∀ id ∈ (c.na (.chunk i)).nr, id ∈ (c.vs (.chunk i)).nr ∨
        ∃ r, (c.r r).pc.ticket = some (s : ℤ) ∧ id ∈ (c.vr r (.chunk i)).nr) ∧
      (Consumed c (s : ℤ) → ∃ r, (c.r r).pc = .rel (s : ℤ) i)

/-- Chunks are the only non-atomic locations. -/
def Loc.IsChunk : Loc → Prop
  | .chunk _ => True
  | _ => False

/-- The safety invariant. -/
structure Inv (c : Cfg ρ) : Prop where
  gen : GenInv c
  phase : ∀ i, ∃ ph, PhaseOK pay ln c i ph
  -- chunks: the sender is the only writer, only non-atomic accesses
  chunkS : ∀ i, Below (c.mem (.chunk i)) (c.vs (.chunk i)).w
  chunkNa : ∀ i, ∃ m ∈ c.mem (.chunk i), m.time = (c.na (.chunk i)).w
  chunkAt : ∀ i, (c.na (.chunk i)).aw = ∅ ∧ (c.na (.chunk i)).ar = ∅
  -- atomic locations: only atomic accesses, always initialized
  atomNa : ∀ l, ¬ l.IsChunk → (c.na l).w = 1 ∧ (c.na l).nr = ∅
  atomVal : ∀ l, ¬ l.IsChunk → ∀ m ∈ c.mem l, m.val.isSome
  -- lengths and sequence numbers: the sender is the only writer
  lenS : ∀ i, Below (c.mem (.len i)) (c.vs (.len i)).w
  cseqS : ∀ i, Below (c.mem (.cseq i)) (c.vs (.cseq i)).w
  cseqVal : ∀ i, ∀ m ∈ c.mem (.cseq i), ∀ v, m.val = some v →
    v = NO_SEQ ∨ (0 ≤ v ∧ v < c.s.pc.npub)
  cseqUniq : ∀ i j, ∀ m ∈ c.mem (.cseq i), ∀ m' ∈ c.mem (.cseq j), ∀ v,
    m.val = some v → m'.val = some v → v ≠ NO_SEQ → i = j
  -- `cur_seq`: a contiguous chain of `fetch_add`s by the sender
  curSeqVal : ∀ m ∈ c.mem .curSeq, m.val = some ((m.time : ℤ) - 1)
  curSeqDown : ∀ m ∈ c.mem .curSeq, ∀ t, 1 ≤ t → t ≤ m.time →
    ∃ m' ∈ c.mem .curSeq, m'.time = t
  curSeqTop : Below (c.mem .curSeq) (c.s.pc.nfa + 1)
  curSeqHas : ∃ m ∈ c.mem .curSeq, m.time = c.s.pc.nfa + 1
  -- the ticket counter: a contiguous chain of `fetch_add`s
  tickVal : ∀ m ∈ c.mem .tick, m.val = some ((m.time : ℤ) - 1)
  tickDown : ∀ m ∈ c.mem .tick, ∀ t, 1 ≤ t → t ≤ m.time →
    ∃ m' ∈ c.mem .tick, m'.time = t
  -- the sender
  sFault : c.s.pc ≠ .fault
  sPub : ∀ k b i s, c.s.pc = .pub k b i s → s = k
  sLog : c.s.log = sentLog pay ln c.s.pc.npub
  -- receivers
  rFault : ∀ r, (c.r r).pc ≠ .fault
  rRel : ∀ r t i, (c.r r).pc = .rel t i → t ∈ (c.r r).log.map Prod.fst
  rTix : ∀ r, ∀ τ ∈ tix (c.r r), 0 ≤ τ ∧ ∃ m ∈ c.mem .tick, m.val = some (τ + 1)
  rLog : ∀ r, ∀ e ∈ (c.r r).log, 0 ≤ e.1 ∧ e.1 < c.s.pc.npub ∧
    e.2.1 = pay e.1.toNat ∧ e.2.2 = ln e.1.toNat
  tixNodup : ∀ r, (tix (c.r r)).Nodup
  tixDisj : ∀ r r', r ≠ r' → ∀ τ ∈ tix (c.r r), τ ∉ tix (c.r r')

/-! ## Basic lemmas -/

theorem below_cons {m : MsgT} {C : List MsgT} {t : ℕ} :
    Below (m :: C) t ↔ m.time ≤ t ∧ Below C t := by
  simp [Below]

theorem Below.mono {C : List MsgT} {t t' : ℕ} (h : Below C t) (ht : t ≤ t') : Below C t' :=
  fun m hm => (h m hm).trans ht

theorem isLatest_cons_new {m : MsgT} {C : List MsgT} {t : ℕ} (h : Below C t)
    (ht : t < m.time) : IsLatest (m :: C) m :=
  ⟨List.mem_cons_self, fun m' hm' => by
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact le_rfl
    · exact ((h m' hm').trans ht.le)⟩

theorem latestIs_cons_new {m : MsgT} {C : List MsgT} {t : ℕ} {v : ℤ} (h : Below C t)
    (ht : t < m.time) (hv : m.val = some v) : LatestIs (m :: C) v :=
  ⟨m, isLatest_cons_new h ht, hv⟩

theorem _root_.ORC11.IsLatest.below {C : List MsgT} {m : MsgT} (h : IsLatest C m) : Below C m.time := h.2

/-- A message at least as late as the latest one is the latest one. -/
theorem _root_.ORC11.IsLatest.eq_of_le {C : List MsgT} {m m' : MsgT}
    (uniq : ∀ a ∈ C, ∀ b ∈ C, a.time = b.time → a = b)
    (h : IsLatest C m) (hm' : m' ∈ C) (ht : m.time ≤ m'.time) : m' = m :=
  uniq m' hm' m h.1 (le_antisymm (h.2 m' hm') ht)

/-- Reading `l` at or after the latest message reads the latest message. -/
theorem LatestIs.read {C : List MsgT} {v : ℤ} {m' : MsgT} {t : ℕ}
    (uniq : ∀ a ∈ C, ∀ b ∈ C, a.time = b.time → a = b)
    (h : LatestIs C v) (hb : Below C t) (hm' : m' ∈ C) (ht : t ≤ m'.time) :
    m'.val = some v := by
  obtain ⟨m, hl, hv⟩ := h
  rw [hl.eq_of_le uniq hm' ((hb m hl.1).trans ht), hv]

theorem tix_held {σ : RState} {t : ℤ} (h : t ∈ σ.pc.held) : t ∈ tix σ :=
  List.mem_append_left _ h

theorem tix_log {σ : RState} {t : ℤ} (h : t ∈ σ.log.map Prod.fst) : t ∈ tix σ :=
  List.mem_append_right _ h

theorem RPc.ticket_mem_held {pc : RPc} {t : ℤ} (h : pc.ticket = some t) :
    t ∈ pc.held ∨ ∃ i, pc = .rel t i := by
  cases pc <;> simp_all [ticket, held]

/-- Two receivers with the same ticket are the same receiver. -/
theorem Inv.ticket_unique {c : Cfg ρ} (h : Inv pay ln c) {r r' : ρ} {t : ℤ}
    (hr : (c.r r).pc.ticket = some t) (hr' : (c.r r').pc.ticket = some t) : r = r' := by
  have mem : ∀ r, (c.r r).pc.ticket = some t → t ∈ tix (c.r r) := by
    intro r hr
    rcases RPc.ticket_mem_held hr with h1 | ⟨i, h1⟩
    · exact tix_held h1
    · exact tix_log (h.rRel r t i h1)
  by_contra hne
  exact h.tixDisj r r' hne t (mem r hr) (mem r' hr')

/-- A held ticket is not consumed. -/
theorem Inv.held_not_consumed {c : Cfg ρ} (h : Inv pay ln c) {r : ρ} {t : ℤ}
    (hr : t ∈ (c.r r).pc.held) : ¬ Consumed c t := by
  rintro ⟨r', hr'⟩
  by_cases hrr : r = r'
  · subst hrr
    have := h.tixNodup r
    simp only [tix, List.nodup_append] at this
    exact this.2.2 t hr t hr' rfl
  · exact h.tixDisj r r' hrr t (tix_held hr) (tix_log hr')

/-! ## The initial state -/

@[simp] theorem init_s : Cfg.s (initConfig init0 initVal : Cfg ρ) = ⟨.start 0, []⟩ := rfl
@[simp] theorem init_vs : Cfg.vs (initConfig init0 initVal : Cfg ρ) = fun _ => initTime := rfl
@[simp] theorem init_r (r : ρ) : Cfg.r (initConfig init0 initVal : Cfg ρ) r = ⟨.init, []⟩ :=
  rfl
@[simp] theorem init_vr (r : ρ) :
    Cfg.vr (initConfig init0 initVal : Cfg ρ) r = fun _ => initTime := rfl
omit [DecidableEq ρ] in
@[simp] theorem init_mem (l : Loc) :
    (initConfig init0 initVal : Cfg ρ).mem l = [⟨1, initVal l, none⟩] := rfl
omit [DecidableEq ρ] in
@[simp] theorem init_na : (initConfig init0 initVal : Cfg ρ).na = fun _ => initTime := rfl

theorem inv_init : Inv pay ln (initConfig init0 initVal : Cfg ρ) where
  gen := genInv_init _ _
  phase i := ⟨.free, by
    refine ⟨by simp [SPc.fill], by simp [SPc.sealing], fun r => by simp [RPc.onBuf], ?_, ?_⟩
    · intro m hm v hv
      simp only [init_mem, List.mem_singleton] at hm; subst hm
      simp [initVal] at hv; exact Or.inl hv.symm
    · refine ⟨⟨1, some 0, none⟩, ⟨by simp [initVal], by simp⟩, rfl, ?_, by simp [initTime]⟩
      intro m hm _ _
      simp only [init_mem, List.mem_singleton] at hm; subst hm; rfl⟩
  chunkS i := by simp [Below, initTime]
  chunkNa i := by simp [initTime]
  chunkAt i := by simp [initTime]
  atomNa l _ := by simp [initTime]
  atomVal l hl m hm := by
    simp only [init_mem, List.mem_singleton] at hm; subst hm
    cases l <;> simp_all [initVal, Loc.IsChunk]
  lenS i := by simp [Below, initTime]
  cseqS i := by simp [Below, initTime]
  cseqVal i m hm v hv := by
    simp only [init_mem, List.mem_singleton] at hm; subst hm
    simp [initVal] at hv; exact Or.inl hv.symm
  cseqUniq i j m hm m' hm' v hv hv' hne := by
    simp only [init_mem, List.mem_singleton] at hm; subst hm
    simp [initVal] at hv; exact absurd hv.symm hne
  curSeqVal m hm := by
    simp only [init_mem, List.mem_singleton] at hm; subst hm; simp [initVal]
  curSeqDown m hm t h1 h2 := by
    simp only [init_mem, List.mem_singleton] at hm; subst hm
    exact ⟨_, List.mem_singleton_self _, by simp at h2 ⊢; omega⟩
  curSeqTop := by simp [Below, SPc.nfa, SPc.k]
  curSeqHas := by simp [SPc.nfa, SPc.k]
  tickVal m hm := by
    simp only [init_mem, List.mem_singleton] at hm; subst hm; simp [initVal]
  tickDown m hm t h1 h2 := by
    simp only [init_mem, List.mem_singleton] at hm; subst hm
    exact ⟨_, List.mem_singleton_self _, by simp at h2 ⊢; omega⟩
  sFault := by simp
  sPub := by simp
  sLog := by simp [SPc.npub, SPc.k, sentLog]
  rFault r := by simp
  rRel r t i := by simp
  rTix r := by simp [tix, RPc.held]
  rLog r := by simp
  tixNodup r := by simp [tix, RPc.held]
  tixDisj r r' _ := by simp [tix, RPc.held]

end Mempipe
