import ORC11.RC11
import ORC11.Wf
import Mathlib.Tactic.IntervalCases

/-!
# Mixed-mode locations: RC11-racy but ORC11-safe

The ORC11 appendix's Theorem 1 (§2) claims that a program which is racy under
RC11 gets stuck on a race in ORC11. For the Coq-faithful ORC11 of this
development that fails once a location is accessed both atomically and
non-atomically. This file gives a counterexample, which is why
`Replay.lean` assumes the programs are location-disciplined
(`RC11.Disciplined`).

The program has one location `x` (`Loc := Unit`) and two threads:

* `T1` (thread `true`): `x.store(1, rlx)`.
* `T2` (thread `false`): `v := x.load(acq)`; if `v = 1` then `x.load(na)`.

In RC11 the execution where both loads of `T2` read `T1`'s store is consistent
and racy: the store is relaxed, so it does not synchronize with the acquire
load, and nothing orders it in `hb` before the non-atomic load
(`mixed_rc11_racy`).

In ORC11 no reachable configuration is racy (`mixed_orc11_safe`). A relaxed
write's message view contains the write's own atomic-write id (`writeRw`,
`writeView` with `rlx ≤ o`). `T2`'s acquire load of that message joins the
message view into its current view, so at the non-atomic load `T2` has seen
`x ↦ {w := t, aw := {t}}`, which is exactly what the race detector demands
(`DrfPreRead.allW`: every message time `≤ cur(x).w` and `𝓝(x).aw ⊆ cur(x).aw`).

The gap in the appendix is Lemma 7, case (2)(b): it assumes a thread view's
`aw` component contains only ids of atomic writes that `hb`-precede the
thread's events. An acquire of a relaxed write also brings that write's own
`aw` entry, although the write is only `rf`-before, not `hb`-before, the
acquire.
-/

namespace ORC11

namespace Mixed

/-- The program. Thread `true` (T1): pc 0 stores `1` relaxed, then halts at
pc 1. Thread `false` (T2): pc 0 is the acquire load, going to pc 1 if it read
`1` and to pc 2 (halt) otherwise; pc 1 is the non-atomic load, going to pc 3
(halt). -/
def prog : (i : Bool) → ℕ → Instr Unit ℕ ℕ
  | true, 0 => .write () .rlx 1 1
  | true, _ => .halt
  | false, 0 => .read () .acqrel (fun v => if v = some 1 then 1 else 2)
  | false, 1 => .read () .na (fun _ => 3)
  | false, _ => .halt

/-- Configurations of the program. -/
abbrev Cfg := Config Bool (fun _ : Bool => ℕ) Unit ℕ

/-- The initialization message of `x`. -/
def initMsg : Msg Unit ℕ := ⟨1, some 0, none⟩

/-! ## ORC11: an invariant of reachable configurations -/

/-- The invariant. -/
structure Inv (c : Cfg) : Prop where
  t1 : (c.th true).1 = 0 ∨ (c.th true).1 = 1
  init : (c.th true).1 = 0 →
    c.mem () = [initMsg] ∧ (c.na ()).aw = ∅ ∧ (c.na ()).nr = ∅
  wr : (c.th true).1 = 1 → ∃ t V, c.mem () = [⟨t, some 1, some V⟩, initMsg] ∧
    t ∈ (V ()).aw ∧ (c.na ()).aw = {t} ∧
    ((c.th false).1 = 1 → t ≤ ((c.th false).2.cur ()).w ∧ t ∈ ((c.th false).2.cur ()).aw)
  naw : (c.na ()).w = 1
  t2 : (c.th false).1 = 1 → (c.th true).1 = 1

theorem inv_init : Inv (initConfig (S := fun _ : Bool => ℕ) (fun _ => 0) (fun _ => some 0)) where
  t1 := Or.inl rfl
  init _ := ⟨rfl, rfl, rfl⟩
  wr h := absurd h (by simp [initConfig])
  naw := rfl
  t2 h := absurd h (by simp [initConfig])

@[simp] theorem upd_tf (f : (i : Bool) → ℕ × TView Unit) (x : ℕ × TView Unit) :
    Function.update f true x false = f false :=
  Function.update_of_ne (by decide) _ _

@[simp] theorem upd_ft (f : (i : Bool) → ℕ × TView Unit) (x : ℕ × TView Unit) :
    Function.update f false x true = f true :=
  Function.update_of_ne (by decide) _ _

theorem inv_step {c c' : Cfg} (h : Inv c) (hs : Step prog c c') : Inv c' := by
  obtain ⟨t1, init, wr, naw, t2⟩ := h
  cases hs with
  | mk i hst =>
  cases i with
  | true =>
    rcases t1 with h0 | h1
    · rw [h0] at hst
      obtain ⟨t, -, -, -, rfl, rfl, rfl, -, hpost⟩ :=
        TStep.write_inv (prog := prog true) (s := 0) rfl hst
      simp only [DrfPostWrite, MemOrder.rlx_le_rlx, ite_true] at hpost
      subst hpost
      obtain ⟨hmem, haw, -⟩ := init h0
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro _
        refine ⟨t, writeView .rlx () t ⊔ (c.th true).2.rel ⊔ ⊥, ?_, ?_, ?_, ?_⟩
        · simp [hmem, writeRw]
        · simp [writeView_aw]
        · simp [haw]
        · intro h; simp only [upd_tf] at h
          have := t2 h; omega
      · simpa using naw
      · intro _; simp
    · rw [h1] at hst; exact (TStep.halt_inv rfl hst).elim
  | false =>
    generalize hs2 : (c.th false).1 = s2 at hst t2 wr
    rcases s2 with _ | _ | s2
    · obtain ⟨m, hm, tr, -, -, -, rfl, rfl, rfl, hpost⟩ :=
        TStep.read_inv (prog := prog false) (s := 0) rfl hst
      simp only [DrfPostRead, MemOrder.rlx_le_acqrel, ite_true] at hpost
      obtain ⟨rfl, -⟩ := hpost
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa using t1
      · intro h; simp only [upd_ft] at h
        obtain ⟨a, b, d⟩ := init h
        simp [a, b, d]
      · intro h; simp only [upd_ft] at h
        obtain ⟨t, V, hmem, htV, haw, -⟩ := wr h
        refine ⟨t, V, hmem, htV, by simp [haw], ?_⟩
        intro hpc
        simp only [Function.update_self] at hpc ⊢
        split_ifs at hpc with hv
        · rw [hmem] at hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · have hR := readTView_R_le (c.th false).2 (o := .acqrel)
              (some V |>.getD ⊥) (readView .acqrel () t tr) MemOrder.acqrel_le_acqrel ()
            have hVv := readTView_V_le (c.th false).2 .acqrel
              (some V |>.getD ⊥) (readView .acqrel () t tr) ()
            refine ⟨?_, TimeInfo.aw_mono hR htV⟩
            have := TimeInfo.w_mono hVv
            simpa using this
          · simp [initMsg] at hv
        · exact absurd hpc (by decide)
      · simpa using naw
      · intro hpc
        simp only [Function.update_self, upd_ft] at hpc ⊢
        split_ifs at hpc with hv
        swap; · exact absurd hpc (by decide)
        rcases t1 with h0 | h1
        · rw [(init h0).1] at hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          subst hm; simp [initMsg] at hv
        · exact h1
    · obtain ⟨m, -, tr, -, -, -, rfl, rfl, rfl, hpost⟩ :=
        TStep.read_inv (prog := prog false) (s := 1) rfl hst
      simp only [DrfPostRead, MemOrder.rlx_le_na, ite_false] at hpost
      obtain ⟨rfl, -⟩ := hpost
      have h1 := t2 rfl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa using t1
      · intro h; simp only [upd_ft] at h; omega
      · intro h; simp only [upd_ft] at h
        obtain ⟨t, V, hmem, htV, haw, -⟩ := wr h
        refine ⟨t, V, hmem, htV, by simp [haw], ?_⟩
        intro hpc; simp at hpc
      · simpa using naw
      · intro hpc; simp at hpc
    · exact (TStep.halt_inv (prog := prog false) (s := s2 + 2) rfl hst).elim

theorem reach_inv {c : Cfg} (h : Reachable prog (fun _ => 0) (fun _ => some 0) c) :
    Inv c := by
  induction h with
  | refl => exact inv_init
  | tail _ hs ih => exact inv_step ih hs

/-- **ORC11 side.** No reachable configuration of the program is racy. -/
theorem mixed_orc11_safe :
    ∀ c, Reachable prog (fun _ => 0) (fun _ => some 0) c → ¬ Racy prog c := by
  intro c hr
  obtain ⟨t1, init, wr, naw, t2⟩ := reach_inv hr
  have hg := Reachable.genInv hr
  rintro ⟨i, hi⟩
  apply hi
  cases i with
  | true =>
    rcases t1 with h0 | h1
    · rw [h0]
      exact ⟨by simp [(init h0).2.2], by rw [naw]; exact hg.cur true (),
        fun h => absurd MemOrder.rlx_le_rlx h⟩
    · rw [h1]; trivial
  | false =>
    generalize hs2 : (c.th false).1 = s2 at t2 wr
    rcases s2 with _ | _ | s2
    · exact ⟨by rw [naw]; exact hg.cur false (), fun h => absurd MemOrder.rlx_le_acqrel h⟩
    · obtain ⟨t, V, hmem, -, haw, hcur⟩ := wr (t2 rfl)
      obtain ⟨hw, hin⟩ := hcur rfl
      refine ⟨by rw [naw]; exact hg.cur false (), fun _ => ⟨?_, ?_⟩⟩
      · intro m hm
        rw [hmem] at hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact hw
        · exact hg.cur false ()
      · rw [haw]; simpa using hin
    · trivial

/-! ## RC11: a consistent, racy execution -/

/-- Labels: event 0 is T1's store, events 1 and 2 are T2's loads. -/
def lab : ℕ → RC11.Label Unit ℕ
  | 0 => .W () .rlx 1
  | 1 => .R () .acqrel (some 1)
  | _ => .R () .na (some 1)

/-- The execution graph: both loads read the store. -/
def G : RC11.Exec prog (fun _ => 0) (fun _ => some 0) where
  n := 3
  tid e := e == 0
  lab := lab
  rf _ := some 0
  ts _ := 2
  active := {true, false}
  items
    | true => [.inl 0]
    | false => [.inl 1, .inl 2]
  final
    | true => 1
    | false => 3
  run i := by cases i <;> rfl
  inactive i h := by cases i <;> simp at h
  itemsEv i := by cases i <;> decide

open RC11 RC11.Exec

theorem G_wf : G.WF where
  rfSrc e he hr := by
    change e < 3 at he
    interval_cases e
    · simp [G, lab, Label.IsRead] at hr
    · simp [G, lab, Label.IsWrite, Label.loc, Label.rval, Label.wval]
    · simp [G, lab, Label.IsWrite, Label.loc, Label.rval, Label.wval]
  tsW _ _ _ := le_rfl
  tsInj a ha b hb hwa hwb _ _ := by
    have : ∀ e < 3, (lab e).IsWrite → e = 0 := by
      intro e he hw
      interval_cases e
      · rfl
      all_goals simp [lab, Label.IsWrite] at hw
    rw [this a ha hwa, this b hb hwb]
  tsDense e he hw t h1 h2 := ⟨e, he, hw, rfl, by simp [G] at h2 ⊢; omega⟩

theorem G_not_sw (a b : Ev Unit) : ¬ G.sw a b := by
  rintro ⟨hrel, -⟩
  cases a with
  | init => exact hrel
  | ev e =>
    obtain ⟨he, hr⟩ := hrel
    change e < 3 at he
    interval_cases e <;> simp [G, lab, Label.RelW] at hr

theorem G_sb_trans {a b c : Ev Unit} (h1 : G.sb a b) (h2 : G.sb b c) : G.sb a c := by
  cases a <;> cases b <;> cases c
  all_goals first
    | exact absurd h1 id
    | exact absurd h2 id
    | skip
  · exact h2.2.1
  · exact ⟨h1.1.trans h2.1, h2.2.1, h1.2.2.trans h2.2.2⟩

theorem G_hb_sb {a b : Ev Unit} (h : G.hb a b) : G.sb a b := by
  induction h with
  | single hs => exact hs.resolve_right (G_not_sw _ _)
  | tail _ hs ih => exact G_sb_trans ih (hs.resolve_right (G_not_sw _ _))

/-- The only `rf` source is event 0. -/
theorem G_rfE_src {w r : Ev Unit} (h : G.rfE w r) : w = .ev 0 := by
  cases r with
  | init => exact absurd h not_rfE_init
  | ev e => exact h.2.2

/-- Writes: the initialization and event 0. -/
theorem G_isWrite {w : Ev Unit} (h : G.IsWrite w) : w = .init () ∨ w = .ev 0 := by
  cases w with
  | init l => exact Or.inl rfl
  | ev e =>
    obtain ⟨he, hw⟩ := h
    change e < 3 at he
    interval_cases e
    · exact Or.inr rfl
    all_goals simp [G, lab, Label.IsWrite] at hw

theorem G_mo {a b : Ev Unit} (h : G.mo a b) : a = .init () ∧ b = .ev 0 := by
  obtain ⟨ha, hb, -, hlt⟩ := h
  rcases G_isWrite ha with rfl | rfl <;> rcases G_isWrite hb with rfl | rfl <;>
    simp_all [tsE, G]

theorem G_no_rb {a b : Ev Unit} : ¬ G.rb a b := by
  rintro ⟨w, hrf, hmo⟩
  have := (G_mo hmo).1
  rw [G_rfE_src hrf] at this
  cases this

/-- No `eco` edge enters the initialization. -/
theorem G_eco_tgt {a b : Ev Unit} (h : G.eco a b) : b ≠ .init () := by
  have step : ∀ x y, (G.rfE x y ∨ G.mo x y ∨ G.rb x y) → y ≠ .init () := by
    rintro x y (h | h | h) rfl
    · exact not_rfE_init h
    · exact absurd (G_mo h).2 (by simp)
    · exact G_no_rb h
  induction h with
  | single hs => exact step _ _ hs
  | tail _ hs _ => exact step _ _ hs

/-- No `eco` edge leaves event 2. -/
theorem G_eco_src {a b : Ev Unit} (h : G.eco a b) : a ≠ .ev 2 := by
  have step : ∀ x y, (G.rfE x y ∨ G.mo x y ∨ G.rb x y) → x ≠ .ev 2 := by
    rintro x y (h | h | h) rfl
    · simpa using G_rfE_src h
    · simpa using (G_mo h).1
    · exact G_no_rb h
  induction h with
  | single hs => exact step _ _ hs
  | tail _ _ ih => exact ih

theorem G_consistent : G.Consistent where
  wf := G_wf
  hbIrrefl a h := by
    obtain ⟨e, rfl, -, hlt⟩ := hb_tgt G_wf h
    exact lt_irrefl _ (hlt e rfl)
  coherence a b hab heco := by
    have hsb := G_hb_sb hab
    cases a with
    | init l => exact G_eco_tgt heco rfl
    | ev x =>
      cases b with
      | init l => exact hsb
      | ev y =>
        obtain ⟨hxy, hy, ht⟩ := hsb
        change y < 3 at hy
        simp only [G] at ht
        have : y = 2 := by
          interval_cases y <;> interval_cases x <;> simp_all
        subst this
        exact G_eco_src heco rfl
  atomicity e he hu := by
    change e < 3 at he
    interval_cases e <;> simp [G, lab, Label.IsUpdate] at hu

/-- **RC11 side.** The execution is consistent and racy: T1's relaxed store
and T2's non-atomic load are unordered by `hb`. -/
theorem mixed_rc11_racy :
    ∃ G : RC11.Exec prog (fun _ => 0) (fun _ => some 0), G.Consistent ∧ G.Racy := by
  refine ⟨G, G_consistent, .ev 0, .ev 2, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine ⟨show 0 < 3 by omega, show 2 < 3 by omega, by simp, rfl, Or.inl ?_⟩
    exact ⟨show 0 < 3 by omega, trivial⟩
  · intro h
    have := (G_hb_sb h).2.2
    simp [G] at this
  · intro h
    have := hb_lt G_wf h
    omega
  · exact Or.inr rfl

end Mixed

end ORC11
