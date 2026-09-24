import ORC11.RC11
import ORC11.Replay
import Mathlib.Tactic.IntervalCases

/-!
# Cross-check: our RC11 against IMM's RC11

This file checks the RC11 model of `RC11.lean` against an established,
independent formalization: the RC11 of IMM (Podkopaev, Lahav, Vafeiadis,
<https://github.com/weakmemory/imm>, `src/rc11/RC11.v`).

## Transcription

The first part transcribes IMM's definitions, each with the Coq source line
(file and line number) in its docstring: `actid`, `tid`, `index`, `is_init`,
`mode`, `mode_le`, `label`, the label predicates (`Events.v`); `execution`,
`sb`, `Wf`, `fr`, `complete`, `rmw_atomicity` (`Execution.v`); `eco`
(`Execution_eco.v`); `rs`, `release`, `sw`, `hb`, `coherence`
(`imm/imm_s_hb.v`); `scb`, `psc_base`, `psc_f` (`imm/imm_s.v`); and
`rc11_consistent` (`rc11/RC11.v`). It uses a small copy of `hahn`'s relation
algebra (`seq` `⨾`, `eqv_rel` `⦗d⦘`, `clos_refl` `^?`, `clos_trans` `^+`,
`clos_refl_trans` `＊`, `transp` `⁻¹ᵣ`, and `∪ᵣ`, `∩ᵣ`, `\ᵣ` for hahn's `∪`, `∩`,
`\`). Precedences follow hahn's: `⨾` binds tighter than `\`, then `∩`, then `∪`.
Labels are Booleans as in Coq, and IMM's sets `R`, `W`, `Rel`, … are
`fun a => is_r lab a = true`, and so on.

The transcription is generic over locations, values and thread ids. The
execution record keeps all the Coq fields, including `threads_set` and the
dependencies `data`, `addr`, `ctrl`, `rmw_dep`, and `Wf` has all 28 Coq
fields. Only two things are generalized, both forced by genericity:

* `wf_init_lab` says `lab (InitEvent l) = Astore Xpln Opln l (init_val l)`
  for a parameter `init_val`, where Coq has `0` (values are `nat` in Coq);
* `tid` takes the initial thread id `tid_init` as a parameter (Coq: `xH`).

## Translation (`toIMM`)

IMM thread ids are `Option ι` with `tid_init := none`, so that no real thread
can collide with the initialization thread in `wf_index`. Our event `e` of
thread `π` becomes `ThreadEvent (some π) (2 e)` (`rdA`). An update becomes a
read `ThreadEvent (some π) (2 e)` and a write `ThreadEvent (some π) (2 e + 1)`
(`wrA`), related by `rmw`. `init l` becomes `InitEvent l`, for every location.
IMM values are our `Option Val`, because our reads may read an uninitialized
location, and `init_val := v0`. `rf` and `co` are our `rf` and `mo` on the
halves that read and write. There are no dependencies (`data`, `addr`,
`ctrl`, `rmw_dep` are empty), and `threads_set` is everything.

Modes are translated as follows: `na ↦ Opln`, `rlx ↦ Orlx`, `sc ↦ Osc`.
`acqrel ↦ Oacq` on reads and on the read half of an update, and
`acqrel ↦ Orel` on writes and on the write half of an update. This matches how
IMM itself labels an RMW (`ProgToExecution.v` L226-233: `Aload rexmod ordr`,
then `Astore xmod ordw`), with `R_ex` set on the read half. Labelling both
halves `Oacqrel` instead would change nothing in `rc11_consistent`, which only
asks `Rel` of writes and `Acq` of reads (there are no fences).

## Results

* `wf_toIMM`: `G.WF → (toIMM G).Wf v0 none`. All 28 fields are proved.
* `consistent_of_rc11`: `G.WF → (toIMM G).rc11_consistent → G.Consistent`,
  with no further hypotheses. This direction needs only IMM's `coherence` and
  `rmw_atomicity`. Our ATOMICITY follows because `rmw ⊆ sb`: an update reading a
  `co`-later write gives an `hb ⨾ eco` cycle, and IMM's `\ sb` restrictions in
  `rmw_atomicity` are discharged the same way. Our coherence follows through a
  normal form `rf ∪ mo;rf? ∪ rb;rf?` of our `eco = (rf ∪ mo ∪ rb)⁺`. The
  normal form is proved with atomicity, which IMM's split updates need for
  steps such as `rf ; rf` through an update (compare `eco_alt3` in
  `Execution_eco.v`). IMM's `hb` contains ours between any halves (`hb_of_G`),
  because our `rs` is contained in IMM's.
* `rc11_of_consistent`: `G.Consistent → G.LabDisc A →
  (toIMM G).rc11_consistent`. Here IMM's `hb` is ours up to the internal
  `rmw` step (`hb_to_G`). The `psc` condition holds because the discipline
  rules out SC events. `acyclic (sb ∪ rf)` follows from our numbering.
* `consistent_iff`: for `G.WF` and `G.LabDisc A`,
  `G.Consistent ↔ (toIMM G).rc11_consistent`.

## Discrepancy: IMM's release sequences

IMM's `rs` is `⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊`, but the RC11 paper
and `RC11.Exec.rs` require the write after `(sb ∩ same_loc)^?` to be atomic
(`[W ⊒ rlx]`). With a non-atomic write sb-after a release write to the same
location, IMM's `hb` is strictly larger. The two models then disagree even
without SC accesses. `Counterexample.consistent_not_imm` gives a well-formed
graph with no SC orders that is consistent (and racy) for us but not
`rc11_consistent` in IMM. The threads are
`T1: y :=na 1; x :=rel 1; x :=na 2` and `T2: x.acq = 2; y.na = 0`.
The discipline, under which every write to a location accessed with a release
write is atomic, removes exactly this difference. The converse direction
(`consistent_of_rc11`) needs no discipline. Whether race-freedom alone
(instead of the discipline) would suffice is not investigated here.
-/

namespace ORC11

namespace IMM

/-! ## Relation algebra (the fragment of `hahn` that IMM's definitions use) -/

section Hahn

variable {α : Type}

/-- hahn `relation`. -/
abbrev relation (α : Type) := α → α → Prop

/-- hahn `seq`, written `r ⨾ s`. -/
def seq (r s : relation α) : relation α := fun x z => ∃ y, r x y ∧ s y z

/-- hahn `eqv_rel`, written `⦗d⦘`. -/
def eqv_rel (d : α → Prop) : relation α := fun x y => x = y ∧ d x

/-- hahn `union`, written `r ∪ s` (here `r ∪ᵣ s`). -/
def union (r s : relation α) : relation α := fun x y => r x y ∨ s x y

/-- hahn `inter_rel`, written `r ∩ s` (here `r ∩ᵣ s`). -/
def inter_rel (r s : relation α) : relation α := fun x y => r x y ∧ s x y

/-- hahn `minus_rel`, written `r \ s` (here `r \ᵣ s`). -/
def minus_rel (r s : relation α) : relation α := fun x y => r x y ∧ ¬ s x y

/-- hahn `transp`, written `r⁻¹` (here `r⁻¹ᵣ`). -/
def transp (r : relation α) : relation α := fun x y => r y x

/-- hahn `clos_refl`, written `r^?`. -/
def clos_refl (r : relation α) : relation α := fun x y => x = y ∨ r x y

/-- Coq `clos_trans`, written `r⁺` (here `r^+`). -/
def clos_trans (r : relation α) : relation α := Relation.TransGen r

/-- Coq `clos_refl_trans`, written `r＊`. -/
def clos_refl_trans (r : relation α) : relation α := Relation.ReflTransGen r

/-- hahn `∅₂`. -/
def empty_rel : relation α := fun _ _ => False

/-- hahn `inclusion`, written `r ⊆ s` (here `r ⊆ᵣ s`). -/
def inclusion (r s : relation α) : Prop := ∀ x y, r x y → s x y

/-- hahn `same_relation`, written `r ≡ s` (here `r ≡ᵣ s`). -/
def same_relation (r s : relation α) : Prop := inclusion r s ∧ inclusion s r

/-- hahn `set_union`, written `s ∪₁ t`. -/
def set_union (s t : α → Prop) : α → Prop := fun x => s x ∨ t x

/-- hahn `set_inter`, written `s ∩₁ t`. -/
def set_inter (s t : α → Prop) : α → Prop := fun x => s x ∧ t x

/-- hahn `set_subset`, written `s ⊆₁ t`. -/
def set_subset (s t : α → Prop) : Prop := ∀ x, s x → t x

/-- hahn `codom_rel`. -/
def codom_rel (r : relation α) : α → Prop := fun y => ∃ x, r x y

/-- hahn `irreflexive`. -/
def irreflexive (r : relation α) : Prop := ∀ x, r x x → False

/-- hahn `acyclic`. -/
def acyclic (r : relation α) : Prop := irreflexive (clos_trans r)

/-- Coq `transitive`. -/
def transitive (r : relation α) : Prop := ∀ x y z, r x y → r y z → r x z

/-- hahn `functional`. -/
def functional (r : relation α) : Prop := ∀ x y z, r x y → r x z → y = z

/-- hahn `funeq`. -/
def funeq {β : Type} (f : α → β) (r : relation α) : Prop := ∀ a b, r a b → f a = f b

/-- hahn `is_total`. -/
def is_total (cond : α → Prop) (r : relation α) : Prop :=
  ∀ a, cond a → ∀ b, cond b → a ≠ b → r a b ∨ r b a

/-- hahn `immediate`. -/
def immediate (r : relation α) : relation α := fun a b => r a b ∧ ∀ c, r a c → r c b → False

scoped infixr:75 " ⨾ " => seq
scoped notation "⦗" d "⦘" => eqv_rel d
scoped infixl:65 " ∪ᵣ " => union
scoped infixl:70 " ∩ᵣ " => inter_rel
scoped infixl:72 " \\ᵣ " => minus_rel
scoped postfix:max "⁻¹ᵣ" => transp
scoped postfix:max "^?" => clos_refl
scoped postfix:max "^+" => clos_trans
scoped postfix:max "＊" => clos_refl_trans
scoped infix:50 " ⊆ᵣ " => inclusion
scoped infix:50 " ≡ᵣ " => same_relation
scoped infixl:65 " ∪₁ " => set_union
scoped infixl:70 " ∩₁ " => set_inter
scoped infix:50 " ⊆₁ " => set_subset

@[simp] theorem seq_eqv_l {d : α → Prop} {r : relation α} {x y : α} :
    (⦗d⦘ ⨾ r) x y ↔ d x ∧ r x y := by
  constructor
  · rintro ⟨z, ⟨rfl, hd⟩, hr⟩; exact ⟨hd, hr⟩
  · rintro ⟨hd, hr⟩; exact ⟨x, ⟨rfl, hd⟩, hr⟩

@[simp] theorem seq_eqv_r {d : α → Prop} {r : relation α} {x y : α} :
    (r ⨾ ⦗d⦘) x y ↔ r x y ∧ d y := by
  constructor
  · rintro ⟨z, hr, rfl, hd⟩; exact ⟨hr, hd⟩
  · rintro ⟨hr, hd⟩; exact ⟨y, hr, rfl, hd⟩

end Hahn

open scoped IMM

/-! ## `src/basic/Events.v` -/

section Transcription

variable {T Loc V : Type}

/-- Events.v L22: `Inductive actid := InitEvent (l : location) | ThreadEvent
(thread : thread_id) (index : nat).` -/
inductive actid (T Loc : Type) where
  | InitEvent (l : Loc)
  | ThreadEvent (thread : T) (index : ℕ)
  deriving DecidableEq

open actid

/-- Events.v L26: `Definition tid a := match a with InitEvent l => tid_init |
ThreadEvent i _ => i end.` Coq fixes `tid_init := xH` (L13); being generic
over the thread type we take it as a parameter. -/
def tid (tid_init : T) : actid T Loc → T
  | InitEvent _ => tid_init
  | ThreadEvent i _ => i

/-- Events.v L34: `Definition index a := match a with InitEvent l => 0 |
ThreadEvent _ n => n end.` -/
def index : actid T Loc → ℕ
  | InitEvent _ => 0
  | ThreadEvent _ n => n

/-- Events.v L40: `Definition is_init a := match a with InitEvent _ => true |
ThreadEvent _ _ => false end.` -/
def is_init : actid T Loc → Bool
  | InitEvent _ => true
  | ThreadEvent _ _ => false

/-- Events.v L85: `Inductive mode := Opln | Orlx | Oacq | Orel | Oacqrel | Osc.` -/
inductive mode where
  | Opln | Orlx | Oacq | Orel | Oacqrel | Osc
  deriving DecidableEq

open mode

/-- Events.v L93: `Definition mode_le lhs rhs := match lhs, rhs with | Opln, _ =>
true | _, Opln => false | Orlx, _ => true | _, Orlx => false | Oacq, Oacq |
Oacq, Oacqrel | Orel, Orel | Orel, Oacqrel | Oacqrel, Oacqrel | _, Osc => true
| _ , _ => false end.` -/
def mode_le : mode → mode → Bool
  | Opln, _ => true
  | _, Opln => false
  | Orlx, _ => true
  | _, Orlx => false
  | Oacq, Oacq | Oacq, Oacqrel | Orel, Orel | Orel, Oacqrel | Oacqrel, Oacqrel => true
  | _, Osc => true
  | _, _ => false

/-- Events.v L108: `Inductive x_mode := Xpln | Xacq.` -/
inductive x_mode where
  | Xpln | Xacq
  deriving DecidableEq

open x_mode

/-- Events.v L112: `Inductive label := Aload (ex:bool) (o:mode) (l:location)
(v:value) | Astore (s:x_mode) (o:mode) (l:location) (v:value) | Afence (o:mode).`
Generic over `location` and `value` (Coq: `Loc.t` and `nat`). -/
inductive label (Loc V : Type) where
  | Aload (ex : Bool) (o : mode) (l : Loc) (v : V)
  | Astore (s : x_mode) (o : mode) (l : Loc) (v : V)
  | Afence (o : mode)

open label

section Labels

variable {A : Type} (lab : A → label Loc V)

/-- Events.v L152: `Definition loc a := match lab a with Aload _ _ l _ |
Astore _ _ l _ => Some l | _ => None end.` -/
def loc (a : A) : Option Loc :=
  match lab a with
  | Aload _ _ l _ | Astore _ _ l _ => some l
  | _ => none

/-- Events.v L159: `Definition val a := match lab a with Aload _ _ _ v |
Astore _ _ _ v => Some v | _ => None end.` -/
def val (a : A) : Option V :=
  match lab a with
  | Aload _ _ _ v | Astore _ _ _ v => some v
  | _ => none

/-- Events.v L166: `Definition mod a := match lab a with Aload _ o _ _ |
Astore _ o _ _ | Afence o => o end.` -/
def mod (a : A) : mode :=
  match lab a with
  | Aload _ o _ _ | Astore _ o _ _ | Afence o => o

/-- Events.v L179: `Definition is_r a := match lab a with Aload _ _ _ _ => true
| _ => false end.` -/
def is_r (a : A) : Bool :=
  match lab a with
  | Aload _ _ _ _ => true
  | _ => false

/-- Events.v L185: `Definition is_w a := match lab a with Astore _ _ _ _ =>
true | _ => false end.` -/
def is_w (a : A) : Bool :=
  match lab a with
  | Astore _ _ _ _ => true
  | _ => false

/-- Events.v L191: `Definition is_f a := match lab a with Afence _ => true | _
=> false end.` -/
def is_f (a : A) : Bool :=
  match lab a with
  | Afence _ => true
  | _ => false

/-- Events.v L209: `Definition is_rlx a : bool := mode_le Orlx (mod a).` -/
def is_rlx (a : A) : Bool := mode_le Orlx (mod lab a)
/-- Events.v L210: `Definition is_acq a : bool := mode_le Oacq (mod a).` -/
def is_acq (a : A) : Bool := mode_le Oacq (mod lab a)
/-- Events.v L211: `Definition is_rel a : bool := mode_le Orel (mod a).` -/
def is_rel (a : A) : Bool := mode_le Orel (mod lab a)
/-- Events.v L213: `Definition is_sc a : bool := match mod a with Osc => true |
_ => false end.` -/
def is_sc (a : A) : Bool :=
  match mod lab a with
  | Osc => true
  | _ => false

/-- Events.v L230: `Definition R_ex a := match lab a with Aload r _ _ _ => r |
_ => false end.` -/
def R_ex (a : A) : Bool :=
  match lab a with
  | Aload r _ _ _ => r
  | _ => false

/-- Events.v L252: `Definition same_loc := (fun x y => loc x = loc y).` -/
def same_loc : relation A := fun x y => loc lab x = loc lab y

end Labels

/-- Events.v L573: `Definition ext_sb a b := match a, b with | _, InitEvent _
=> False | InitEvent _, ThreadEvent _ _ => True | ThreadEvent t i,
ThreadEvent t' i' => t = t' /\ i < i' end.` -/
def ext_sb : relation (actid T Loc)
  | _, InitEvent _ => False
  | InitEvent _, ThreadEvent _ _ => True
  | ThreadEvent t i, ThreadEvent t' i' => t = t' ∧ i < i'

/-! ## `src/basic/Execution.v` -/

/-- Execution.v L10: `Record execution := { acts_set : actid -> Prop ;
threads_set : thread_id -> Prop; lab : actid -> label ; rmw : actid -> actid ->
Prop ; data : ... ; addr : ... ; ctrl : ... ; rmw_dep : ... ; rf : actid ->
actid -> Prop ; co : actid -> actid -> Prop ; }.` -/
structure execution (T Loc V : Type) where
  acts_set : actid T Loc → Prop
  threads_set : T → Prop
  lab : actid T Loc → label Loc V
  rmw : relation (actid T Loc)
  /-- data dependency -/
  data : relation (actid T Loc)
  /-- address dependency -/
  addr : relation (actid T Loc)
  /-- control dependency -/
  ctrl : relation (actid T Loc)
  /-- a data dependency to a CAS -/
  rmw_dep : relation (actid T Loc)
  rf : relation (actid T Loc)
  co : relation (actid T Loc)

namespace execution

variable (G : execution T Loc V)

/-- Execution.v L42 `Notation "'E'" := (acts_set G).` -/
def E : actid T Loc → Prop := G.acts_set
/-- Execution.v L58 `Notation "'R'" := (fun a => is_true (is_r lab a)).` -/
def R : actid T Loc → Prop := fun a => is_r G.lab a = true
/-- Execution.v L59 `Notation "'W'" := (fun a => is_true (is_w lab a)).` -/
def W : actid T Loc → Prop := fun a => is_w G.lab a = true
/-- Execution.v L60 `Notation "'F'" := (fun a => is_true (is_f lab a)).` -/
def F : actid T Loc → Prop := fun a => is_f G.lab a = true
/-- Execution.v L61 `Notation "'RW'" := (R ∪₁ W).` -/
def RW : actid T Loc → Prop := G.R ∪₁ G.W
/-- Execution.v L64 `Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).` -/
def Rex : actid T Loc → Prop := fun a => R_ex G.lab a = true
/-- imm_s_hb.v L51 `Notation "'Rel'" := (fun a => is_true (is_rel lab a)).` -/
def Rel : actid T Loc → Prop := fun a => is_rel G.lab a = true
/-- imm_s_hb.v L52 `Notation "'Acq'" := (fun a => is_true (is_acq lab a)).` -/
def Acq : actid T Loc → Prop := fun a => is_acq G.lab a = true
/-- imm_s_hb.v L54 `Notation "'Sc'" := (fun a => is_true (is_sc lab a)).` -/
def Sc : actid T Loc → Prop := fun a => is_sc G.lab a = true
/-- Execution.v L56 `Notation "'same_loc'" := (same_loc lab).` -/
def sl : relation (actid T Loc) := same_loc G.lab

/-- Execution.v L74: `Definition sb := ⦗E⦘ ⨾ ext_sb ⨾ ⦗E⦘.` -/
def sb : relation (actid T Loc) := ⦗G.E⦘ ⨾ ext_sb ⨾ ⦗G.E⦘

/-- Execution.v L76 `Record Wf`, all 28 fields. Two generalizations, both
forced by being generic over the thread and value types: the initial thread id
`tid_init` (Coq: `xH`) and the initial values `init_val` (Coq: `0` in
`wf_init_lab`) are parameters. -/
structure Wf (init_val : Loc → V) (tid_init : T) : Prop where
  /-- L77 `wf_index : forall a b, E a /\ E b /\ a <> b /\ tid a = tid b /\ ~ is_init a -> index a <> index b` -/
  wf_index : ∀ a b, G.E a ∧ G.E b ∧ a ≠ b ∧ tid tid_init a = tid tid_init b ∧
    is_init a = false → index a ≠ index b
  /-- L79 `data_in_sb : data ⊆ sb` -/
  data_in_sb : G.data ⊆ᵣ G.sb
  /-- L80 `wf_dataD : data ≡ ⦗R⦘ ⨾ data ⨾ ⦗W⦘` -/
  wf_dataD : G.data ≡ᵣ ⦗G.R⦘ ⨾ G.data ⨾ ⦗G.W⦘
  /-- L81 `addr_in_sb : addr ⊆ sb` -/
  addr_in_sb : G.addr ⊆ᵣ G.sb
  /-- L82 `wf_addrD : addr ≡ ⦗R⦘ ⨾ addr ⨾ ⦗RW⦘` -/
  wf_addrD : G.addr ≡ᵣ ⦗G.R⦘ ⨾ G.addr ⨾ ⦗G.RW⦘
  /-- L83 `ctrl_in_sb : ctrl ⊆ sb` -/
  ctrl_in_sb : G.ctrl ⊆ᵣ G.sb
  /-- L84 `wf_ctrlD : ctrl ≡ ⦗R⦘ ⨾ ctrl` -/
  wf_ctrlD : G.ctrl ≡ᵣ ⦗G.R⦘ ⨾ G.ctrl
  /-- L85 `ctrl_sb : ctrl ⨾ sb ⊆ ctrl` -/
  ctrl_sb : G.ctrl ⨾ G.sb ⊆ᵣ G.ctrl
  /-- L86 `wf_rmwD : rmw ≡ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘` -/
  wf_rmwD : G.rmw ≡ᵣ ⦗G.R⦘ ⨾ G.rmw ⨾ ⦗G.W⦘
  /-- L87 `wf_rmwl : rmw ⊆ same_loc` -/
  wf_rmwl : G.rmw ⊆ᵣ G.sl
  /-- L88 `wf_rmwi : rmw ⊆ immediate sb` -/
  wf_rmwi : G.rmw ⊆ᵣ immediate G.sb
  /-- L89 `wf_rfE : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘` -/
  wf_rfE : G.rf ≡ᵣ ⦗G.E⦘ ⨾ G.rf ⨾ ⦗G.E⦘
  /-- L90 `wf_rfD : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘` -/
  wf_rfD : G.rf ≡ᵣ ⦗G.W⦘ ⨾ G.rf ⨾ ⦗G.R⦘
  /-- L91 `wf_rfl : rf ⊆ same_loc` -/
  wf_rfl : G.rf ⊆ᵣ G.sl
  /-- L92 `wf_rfv : funeq val rf` -/
  wf_rfv : funeq (val G.lab) G.rf
  /-- L93 `wf_rff : functional rf⁻¹` -/
  wf_rff : functional G.rf⁻¹ᵣ
  /-- L94 `wf_coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘` -/
  wf_coE : G.co ≡ᵣ ⦗G.E⦘ ⨾ G.co ⨾ ⦗G.E⦘
  /-- L95 `wf_coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘` -/
  wf_coD : G.co ≡ᵣ ⦗G.W⦘ ⨾ G.co ⨾ ⦗G.W⦘
  /-- L96 `wf_col : co ⊆ same_loc` -/
  wf_col : G.co ⊆ᵣ G.sl
  /-- L97 `co_trans : transitive co` -/
  co_trans : transitive G.co
  /-- L98 `wf_co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co` -/
  wf_co_total : ∀ ol, is_total (G.E ∩₁ G.W ∩₁ (fun x => loc G.lab x = ol)) G.co
  /-- L99 `co_irr : irreflexive co` -/
  co_irr : irreflexive G.co
  /-- L100 `wf_init : forall l, (exists b, E b /\ loc b = Some l) -> E (InitEvent l)` -/
  wf_init : ∀ l, (∃ b, G.E b ∧ loc G.lab b = some l) → G.E (InitEvent l)
  /-- L101 `wf_init_lab : forall l, lab (InitEvent l) = Astore Xpln Opln l 0` -/
  wf_init_lab : ∀ l, G.lab (InitEvent l) = Astore Xpln Opln l (init_val l)
  /-- L103 `rmw_dep_in_sb : rmw_dep ⊆ sb` -/
  rmw_dep_in_sb : G.rmw_dep ⊆ᵣ G.sb
  /-- L104 `wf_rmw_depD : rmw_dep ≡ ⦗R⦘ ⨾ rmw_dep ⨾ ⦗R_ex⦘` -/
  wf_rmw_depD : G.rmw_dep ≡ᵣ ⦗G.R⦘ ⨾ G.rmw_dep ⨾ ⦗G.Rex⦘
  /-- L107 `wf_threads : forall e (EE : E e), threads_set (tid e)` -/
  wf_threads : ∀ e, G.E e → G.threads_set (tid tid_init e)

/-- Execution.v L119: `Definition fr := rf⁻¹ ⨾ co.` -/
def fr : relation (actid T Loc) := G.rf⁻¹ᵣ ⨾ G.co

/-- Execution.v L127: `Definition complete := E ∩₁ R ⊆₁ codom_rel rf.` -/
def complete : Prop := G.E ∩₁ G.R ⊆₁ codom_rel G.rf

/-- Execution.v L128: `Definition rmw_atomicity := rmw ∩ ((fr \ sb) ⨾ (co \ sb)) ⊆ ∅₂.` -/
def rmw_atomicity : Prop := G.rmw ∩ᵣ ((G.fr \ᵣ G.sb) ⨾ (G.co \ᵣ G.sb)) ⊆ᵣ empty_rel

/-! ## `src/basic/Execution_eco.v` -/

/-- Execution_eco.v L59: `Definition eco := rf ∪ co ⨾ rf^? ∪ fr ⨾ rf^?.` -/
def eco : relation (actid T Loc) := G.rf ∪ᵣ G.co ⨾ G.rf^? ∪ᵣ G.fr ⨾ G.rf^?

/-! ## `src/imm/imm_s_hb.v` -/

/-- imm_s_hb.v L66: `Definition rs := ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊.` -/
def rs : relation (actid T Loc) := ⦗G.W⦘ ⨾ (G.sb ∩ᵣ G.sl)^? ⨾ ⦗G.W⦘ ⨾ (G.rf ⨾ G.rmw)＊

/-- imm_s_hb.v L68: `Definition release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs.` -/
def release : relation (actid T Loc) := ⦗G.Rel⦘ ⨾ (⦗G.F⦘ ⨾ G.sb)^? ⨾ G.rs

/-- imm_s_hb.v L71: `Definition sw := release ⨾ rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.` -/
def sw : relation (actid T Loc) := G.release ⨾ G.rf ⨾ (G.sb ⨾ ⦗G.F⦘)^? ⨾ ⦗G.Acq⦘

/-- imm_s_hb.v L74: `Definition hb := (sb ∪ sw)⁺.` -/
def hb : relation (actid T Loc) := (G.sb ∪ᵣ G.sw)^+

/-- imm_s_hb.v L332: `Definition coherence := irreflexive (hb ⨾ eco^?).` -/
def coherence : Prop := irreflexive (G.hb ⨾ G.eco^?)

/-! ## `src/imm/imm_s.v` -/

/-- imm_s.v L79: `Definition scb := sb ∪ (sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ∪
(hb ∩ same_loc) ∪ co ∪ fr.` -/
def scb : relation (actid T Loc) :=
  G.sb ∪ᵣ (G.sb \ᵣ G.sl) ⨾ G.hb ⨾ (G.sb \ᵣ G.sl) ∪ᵣ (G.hb ∩ᵣ G.sl) ∪ᵣ G.co ∪ᵣ G.fr

/-- imm_s.v L81: `Definition psc_base := ⦗ Sc ⦘ ⨾ (⦗ F ⦘ ⨾ hb)^? ⨾ scb ⨾ (hb ⨾ ⦗ F ⦘)^? ⨾ ⦗ Sc ⦘.` -/
def psc_base : relation (actid T Loc) :=
  ⦗G.Sc⦘ ⨾ (⦗G.F⦘ ⨾ G.hb)^? ⨾ G.scb ⨾ (G.hb ⨾ ⦗G.F⦘)^? ⨾ ⦗G.Sc⦘

/-- imm_s.v L82: `Definition psc_f := ⦗F∩₁Sc⦘ ⨾ hb ⨾ (eco ⨾ hb)^? ⨾ ⦗F∩₁Sc⦘.` -/
def psc_f : relation (actid T Loc) :=
  ⦗G.F ∩₁ G.Sc⦘ ⨾ G.hb ⨾ (G.eco ⨾ G.hb)^? ⨾ ⦗G.F ∩₁ G.Sc⦘

/-! ## `src/rc11/RC11.v` -/

/-- RC11.v L44: `Definition rc11_consistent := ⟪ Comp : complete G ⟫ /\ ⟪ Coh :
coherence G ⟫ /\ ⟪ Cat : rmw_atomicity G ⟫ /\ ⟪ Csc : acyclic (psc_f G ∪
psc_base G) ⟫ /\ ⟪ Csbrf : acyclic (sb ∪ rf) ⟫.` -/
def rc11_consistent : Prop :=
  G.complete ∧ G.coherence ∧ G.rmw_atomicity ∧ acyclic (G.psc_f ∪ᵣ G.psc_base) ∧
    acyclic (G.sb ∪ᵣ G.rf)

end execution

end Transcription

/-! ## The translation of our graphs into IMM executions -/

section Translation

open actid mode x_mode label execution

variable {Loc Val : Type} [DecidableEq Loc] [DecidableEq Val]
  {ι : Type} [DecidableEq ι] {S : ι → Type}
  {prog : (i : ι) → S i → Instr Loc Val (S i)} {s0 : (i : ι) → S i}
  {v0 : Loc → Option Val}

/-- Orders of reads and of the read half of an update: `acqrel ↦ Oacq`. -/
def modeR : MemOrder → mode
  | .na => Opln
  | .rlx => Orlx
  | .acqrel => Oacq
  | .sc => Osc

/-- Orders of writes and of the write half of an update: `acqrel ↦ Orel`. -/
def modeW : MemOrder → mode
  | .na => Opln
  | .rlx => Orlx
  | .acqrel => Orel
  | .sc => Osc

/-- Our updates. -/
def isU : RC11.Label Loc Val → Bool
  | .U .. => true
  | _ => false

/-- The IMM label of half `k` of one of our events: half `0` is a read, a
write, or the read half of an update, half `1` the write half of an update
(as IMM's `ProgToExecution.v` L226-233 labels an RMW: `Aload rexmod ordr l val`
then `Astore xmod ordw l nval`). IMM values are our `Option Val`: a read may
read an uninitialized location. -/
def halfLab : RC11.Label Loc Val → ℕ → label Loc (Option Val)
  | .R l o v, 0 => Aload false (modeR o) l v
  | .W l o v, 0 => Astore Xpln (modeW o) l (some v)
  | .U l or _ vr _, 0 => Aload true (modeR or) l (some vr)
  | .U l _ ow _ vw, 1 => Astore Xpln (modeW ow) l (some vw)
  | _, _ => Afence Opln

/-- IMM events for our graphs: IMM thread ids are `Option ι`, with
`tid_init := none`. -/
abbrev Act (ι Loc : Type) := actid (Option ι) Loc

variable (G : RC11.Exec prog s0 v0)

/-- The read (or only) half of our event `e`: `ThreadEvent π (2 e)`. -/
def rdA (e : ℕ) : Act ι Loc := ThreadEvent (some (G.tid e)) (2 * e)

/-- The index of the write half of our event `e`. -/
def wIdx (e : ℕ) : ℕ := if isU (G.lab e) then 2 * e + 1 else 2 * e

/-- The write (or only) half of our event: `ThreadEvent π (2 e + 1)` for an
update, `ThreadEvent π (2 e)` otherwise, `InitEvent l` for `init l`. -/
def wrA : RC11.Ev Loc → Act ι Loc
  | .init l => InitEvent l
  | .ev e => ThreadEvent (some (G.tid e)) (wIdx G e)

/-- The event of ours an IMM event comes from. -/
def dec : Act ι Loc → RC11.Ev Loc
  | InitEvent l => .init l
  | ThreadEvent _ i => .ev (i / 2)

/-- The IMM events: all initializations, and the halves of our events. -/
def actsT : Act ι Loc → Prop
  | InitEvent _ => True
  | ThreadEvent t i => i / 2 < G.n ∧ t = some (G.tid (i / 2)) ∧
      (i % 2 = 0 ∨ isU (G.lab (i / 2)) = true)

/-- IMM labels (a plain fence `Afence Opln` off the graph). -/
def labT : Act ι Loc → label Loc (Option Val)
  | InitEvent l => Astore Xpln Opln l (v0 l)
  | ThreadEvent _ i => if i / 2 < G.n then halfLab (G.lab (i / 2)) (i % 2) else Afence Opln

/-- **The translation.** `rmw` relates the halves of an update, `rf` and `co`
are our `rf` and `mo` on the halves that read and write; there are no
dependencies (RC11 consistency does not look at them). -/
def toIMM : execution (Option ι) Loc (Option Val) where
  acts_set := actsT G
  threads_set _ := True
  lab := labT G
  rmw x y := ∃ e, e < G.n ∧ isU (G.lab e) = true ∧ x = rdA G e ∧ y = wrA G (.ev e)
  data _ _ := False
  addr _ _ := False
  ctrl _ _ := False
  rmw_dep _ _ := False
  rf x y := ∃ w e, G.rfE w (.ev e) ∧ x = wrA G w ∧ y = rdA G e
  co x y := ∃ a b, G.mo a b ∧ x = wrA G a ∧ y = wrA G b

/-- The IMM events of our event `a`. -/
def Part (a : RC11.Ev Loc) (x : Act ι Loc) : Prop := (toIMM G).E x ∧ dec x = a

/-! ### Events and labels of the translation -/

variable {G}

open RC11 RC11.Exec

omit [DecidableEq Loc] [DecidableEq Val] in
theorem isU_iff {l : RC11.Label Loc Val} : isU l = true ↔ l.IsUpdate := by
  cases l <;> simp [isU, Label.IsUpdate]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.write_of_upd {l : RC11.Label Loc Val} (h : l.IsUpdate) : l.IsWrite := by
  cases l <;> simp_all [Label.IsUpdate, Label.IsWrite]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.read_of_upd {l : RC11.Label Loc Val} (h : l.IsUpdate) : l.IsRead := by
  cases l <;> simp_all [Label.IsUpdate, Label.IsRead]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.upd_of {l : RC11.Label Loc Val} (hr : l.IsRead) (hw : l.IsWrite) : l.IsUpdate := by
  cases l <;> simp_all [Label.IsUpdate, Label.IsRead, Label.IsWrite]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.write_of_relW {l : RC11.Label Loc Val} (h : l.RelW) : l.IsWrite := by
  cases l <;> simp_all [Label.RelW, Label.IsWrite]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.atomicW_of_relW {l : RC11.Label Loc Val} (h : l.RelW) : l.AtomicW := by
  cases l with
  | R => exact h.elim
  | W l o v => cases o <;> simp_all [Label.RelW, Label.AtomicW]
  | U l or ow vr vw => cases ow <;> simp_all [Label.RelW, Label.AtomicW]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.disc_relW {A : Loc → Prop} {l : RC11.Label Loc Val} (hd : l.Disc A)
    (h : l.RelW) : A l.loc := by
  cases l with
  | R => exact h.elim
  | W l o v =>
    by_contra hA
    have := hd.2 hA
    subst this; simp [Label.RelW] at h
  | U l or ow vr vw => exact hd.1

omit [DecidableEq Loc] [DecidableEq Val] in
theorem Label.disc_atomicW {A : Loc → Prop} {l : RC11.Label Loc Val} (hd : l.Disc A)
    (hA : A l.loc) (hw : l.IsWrite) : l.AtomicW := by
  cases l with
  | R => exact hw.elim
  | W l o v => rcases hd.1 hA with h | h <;> subst h <;> simp [Label.AtomicW]
  | U l or ow vr vw => rcases hd.2.2 with h | h <;> subst h <;> simp [Label.AtomicW]

@[simp] theorem dec_rdA (e : ℕ) : dec (rdA G e) = .ev e := by
  simp only [rdA, dec]; congr 1; omega

@[simp] theorem dec_wrA (w : Ev Loc) : dec (wrA G w) = w := by
  cases w with
  | init l => rfl
  | ev e => simp only [wrA, dec, wIdx]; split <;> (congr 1; omega)

theorem wrA_inj {a b : Ev Loc} (h : wrA G a = wrA G b) : a = b := by
  simpa using congrArg dec h

theorem rdA_inj {a b : ℕ} (h : rdA G a = rdA G b) : a = b := by
  simpa using congrArg dec h

theorem wIdx_U {e : ℕ} (h : isU (G.lab e) = true) : wIdx G e = 2 * e + 1 := by
  simp [wIdx, h]

theorem wIdx_nU {e : ℕ} (h : isU (G.lab e) = false) : wIdx G e = 2 * e := by
  simp [wIdx, h]

theorem wrA_nU {e : ℕ} (h : isU (G.lab e) = false) : wrA G (.ev e) = rdA G e := by
  simp [wrA, rdA, wIdx_nU h]

theorem rdA_ne_wrA {e : ℕ} (h : isU (G.lab e) = true) : rdA G e ≠ wrA G (.ev e) := by
  intro h'
  simp only [rdA, wrA, wIdx_U h, actid.ThreadEvent.injEq] at h'
  omega

theorem labT_thread (t : Option ι) (i : ℕ) :
    labT G (ThreadEvent t i) = if i / 2 < G.n then halfLab (G.lab (i / 2)) (i % 2) else Afence Opln :=
  rfl

theorem labT_rdA {e : ℕ} (he : e < G.n) : labT G (rdA G e) = halfLab (G.lab e) 0 := by
  rw [rdA, labT_thread, show 2 * e / 2 = e by omega, show 2 * e % 2 = 0 by omega]
  simp only [he, ↓reduceIte]

theorem labT_wrA {e : ℕ} (he : e < G.n) :
    labT G (wrA G (.ev e)) = halfLab (G.lab e) (if isU (G.lab e) then 1 else 0) := by
  cases h : isU (G.lab e)
  · rw [wrA_nU h, labT_rdA he]; rfl
  · rw [wrA, labT_thread, wIdx_U h, show (2 * e + 1) / 2 = e by omega,
      show (2 * e + 1) % 2 = 1 by omega]
    simp only [he, ↓reduceIte]

theorem E_thread {t : Option ι} {i : ℕ} :
    (toIMM G).E (ThreadEvent t i) ↔
      i / 2 < G.n ∧ t = some (G.tid (i / 2)) ∧ (i % 2 = 0 ∨ isU (G.lab (i / 2)) = true) :=
  Iff.rfl

theorem E_init (l : Loc) : (toIMM G).E (InitEvent l) := trivial

theorem E_rdA {e : ℕ} (he : e < G.n) : (toIMM G).E (rdA G e) := by
  rw [rdA, E_thread, show 2 * e / 2 = e by omega]
  exact ⟨he, rfl, Or.inl (by omega)⟩

theorem E_wrA_ev {e : ℕ} (he : e < G.n) : (toIMM G).E (wrA G (.ev e)) := by
  cases h : isU (G.lab e)
  · rw [wrA_nU h]; exact E_rdA he
  · rw [wrA, E_thread, wIdx_U h, show (2 * e + 1) / 2 = e by omega]
    exact ⟨he, rfl, Or.inr h⟩

theorem mem_of_isWrite {w : Ev Loc} (h : G.IsWrite w) : G.Mem w := by
  cases w with
  | init => trivial
  | ev e => exact h.1

theorem E_wrA {w : Ev Loc} (h : G.Mem w) : (toIMM G).E (wrA G w) := by
  cases w with
  | init l => trivial
  | ev e => exact E_wrA_ev h

theorem E_cases {x : Act ι Loc} (h : (toIMM G).E x) :
    (∃ l, x = InitEvent l) ∨ (∃ e, e < G.n ∧ x = rdA G e) ∨
      (∃ e, e < G.n ∧ isU (G.lab e) = true ∧ x = wrA G (.ev e)) := by
  cases x with
  | InitEvent l => exact Or.inl ⟨l, rfl⟩
  | ThreadEvent t i =>
    obtain ⟨hn, rfl, hpar⟩ := E_thread.1 h
    obtain ⟨e, rfl | rfl⟩ : ∃ e, i = 2 * e ∨ i = 2 * e + 1 := ⟨i / 2, by omega⟩
    · rw [show 2 * e / 2 = e by omega] at hn ⊢
      exact Or.inr (Or.inl ⟨e, hn, rfl⟩)
    · rw [show (2 * e + 1) / 2 = e by omega] at hn hpar ⊢
      have hU : isU (G.lab e) = true := hpar.resolve_left (by omega)
      exact Or.inr (Or.inr ⟨e, hn, hU, by rw [wrA, wIdx_U hU]⟩)

theorem part_rdA {e : ℕ} (he : e < G.n) : Part G (.ev e) (rdA G e) := ⟨E_rdA he, dec_rdA e⟩

theorem part_wrA {w : Ev Loc} (h : G.Mem w) : Part G w (wrA G w) := ⟨E_wrA h, dec_wrA w⟩

theorem part_ev {e : ℕ} {x : Act ι Loc} (h : Part G (.ev e) x) :
    e < G.n ∧ (x = rdA G e ∨ (isU (G.lab e) = true ∧ x = wrA G (.ev e))) := by
  obtain ⟨hE, hd⟩ := h
  rcases E_cases hE with ⟨l, rfl⟩ | ⟨e', he', rfl⟩ | ⟨e', he', hU, rfl⟩
  · cases hd
  · simp only [dec_rdA, Ev.ev.injEq] at hd; subst hd; exact ⟨he', Or.inl rfl⟩
  · simp only [dec_wrA, Ev.ev.injEq] at hd; subst hd; exact ⟨he', Or.inr ⟨hU, rfl⟩⟩

theorem part_init {l : Loc} {x : Act ι Loc} (h : Part G (.init l) x) : x = InitEvent l := by
  obtain ⟨hE, hd⟩ := h
  rcases E_cases hE with ⟨l', rfl⟩ | ⟨e', he', rfl⟩ | ⟨e', he', hU, rfl⟩
  · cases hd; rfl
  · simp at hd
  · simp at hd

theorem E_notF {x : Act ι Loc} (h : (toIMM G).E x) : ¬ (toIMM G).F x := by
  rcases E_cases h with ⟨l, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, hU, rfl⟩
  · simp [execution.F, toIMM, is_f, labT]
  · simp only [execution.F, toIMM, is_f, labT_rdA he]
    cases G.lab e <;> simp [halfLab]
  · simp only [execution.F, toIMM, is_f, labT_wrA he, hU, ite_true]
    cases hl : G.lab e <;> simp_all [halfLab, isU]

theorem W_E {x : Act ι Loc} (hE : (toIMM G).E x) (hW : (toIMM G).W x) :
    x = wrA G (dec x) ∧ G.IsWrite (dec x) := by
  rcases E_cases hE with ⟨l, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, hU, rfl⟩
  · exact ⟨rfl, trivial⟩
  · simp only [execution.W, toIMM, is_w, labT_rdA he] at hW
    rw [dec_rdA]
    cases hl : G.lab e <;> rw [hl] at hW <;> simp [halfLab] at hW
    exact ⟨(wrA_nU (by simp [hl, isU])).symm, he, by simp [hl, Label.IsWrite]⟩
  · rw [dec_wrA]
    exact ⟨rfl, he, Label.write_of_upd (isU_iff.1 hU)⟩

theorem R_E {x : Act ι Loc} (hE : (toIMM G).E x) (hR : (toIMM G).R x) :
    ∃ e, x = rdA G e ∧ e < G.n ∧ (G.lab e).IsRead := by
  rcases E_cases hE with ⟨l, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, hU, rfl⟩
  · simp [execution.R, toIMM, is_r, labT] at hR
  · refine ⟨e, rfl, he, ?_⟩
    simp only [execution.R, toIMM, is_r, labT_rdA he] at hR
    cases hl : G.lab e <;> rw [hl] at hR <;> simp_all [halfLab, Label.IsRead]
  · simp only [execution.R, toIMM, is_r, labT_wrA he, hU, ite_true] at hR
    cases hl : G.lab e <;> simp_all [halfLab, isU]

theorem W_wrA {w : Ev Loc} (h : G.IsWrite w) : (toIMM G).W (wrA G w) := by
  cases w with
  | init l => rfl
  | ev e =>
    obtain ⟨he, hw⟩ := h
    simp only [execution.W, toIMM, is_w, labT_wrA he]
    cases hl : G.lab e <;> simp_all [halfLab, isU, Label.IsWrite]

theorem R_rdA {e : ℕ} (he : e < G.n) (h : (G.lab e).IsRead) : (toIMM G).R (rdA G e) := by
  simp only [execution.R, toIMM, is_r, labT_rdA he]
  cases hl : G.lab e <;> simp_all [halfLab, Label.IsRead]

theorem loc_wrA {w : Ev Loc} (h : G.IsWrite w) :
    loc (toIMM G).lab (wrA G w) = some (G.loc w) := by
  cases w with
  | init l => rfl
  | ev e =>
    obtain ⟨he, hw⟩ := h
    simp only [loc, toIMM, labT_wrA he, Exec.loc]
    cases hl : G.lab e <;> simp_all [halfLab, isU, Label.IsWrite, Label.loc]

theorem loc_rdA {e : ℕ} (he : e < G.n) : loc (toIMM G).lab (rdA G e) = some (G.lab e).loc := by
  simp only [loc, toIMM, labT_rdA he]
  cases G.lab e <;> simp [halfLab, Label.loc]

theorem val_wrA_ev {e : ℕ} (he : e < G.n) (hw : (G.lab e).IsWrite) :
    val (toIMM G).lab (wrA G (.ev e)) = some (G.lab e).wval := by
  simp only [val, toIMM, labT_wrA he]
  cases hl : G.lab e <;> simp_all [halfLab, isU, Label.IsWrite, Label.wval]

theorem val_rdA {e : ℕ} (he : e < G.n) (hr : (G.lab e).IsRead) :
    val (toIMM G).lab (rdA G e) = (G.lab e).rval := by
  simp only [val, toIMM, labT_rdA he]
  cases hl : G.lab e <;> simp_all [halfLab, Label.IsRead, Label.rval]

theorem rel_wrA {w : Ev Loc} (h : G.IsWrite w) : (toIMM G).Rel (wrA G w) ↔ G.RelW w := by
  cases w with
  | init l => simp [execution.Rel, toIMM, is_rel, wrA, labT, mod, mode_le, RelW]
  | ev e =>
    obtain ⟨he, hw⟩ := h
    simp only [execution.Rel, toIMM, is_rel, mod, labT_wrA he, RelW, he, true_and]
    cases hl : G.lab e with
    | R => simp [hl, Label.IsWrite] at hw
    | W l o v => cases o <;> simp [halfLab, isU, modeW, mode_le, Label.RelW]
    | U l or ow vr vw => cases ow <;> simp [halfLab, isU, modeW, mode_le, Label.RelW]

theorem acq_rdA {e : ℕ} (he : e < G.n) (hr : (G.lab e).IsRead) :
    (toIMM G).Acq (rdA G e) ↔ G.AcqR (.ev e) := by
  simp only [execution.Acq, toIMM, is_acq, mod, labT_rdA he, AcqR, he, true_and]
  cases hl : G.lab e with
  | W => simp [hl, Label.IsRead] at hr
  | R l o v => cases o <;> simp [halfLab, modeR, mode_le, Label.AcqR]
  | U l or ow vr vw => cases or <;> simp [halfLab, modeR, mode_le, Label.AcqR]

omit [DecidableEq Loc] [DecidableEq Val] in
theorem is_sc_eq {A : Type} (lab : A → label Loc (Option Val)) (a : A) :
    is_sc lab a = is_sc (fun _ : Unit => lab a) () := rfl

omit [DecidableEq Loc] [DecidableEq Val] in
theorem halfLab_not_sc {A : Loc → Prop} {l : RC11.Label Loc Val} (hd : l.Disc A) (k : ℕ) :
    is_sc (fun _ : Unit => halfLab l k) () = false := by
  cases l with
  | R l o v =>
    have : o ≠ .sc := by
      by_cases hA : A l
      · rcases hd.1 hA with h | h <;> simp [h]
      · simp [hd.2 hA]
    rcases k with _ | k <;> cases o <;> simp_all [halfLab, is_sc, mod, modeR]
  | W l o v =>
    have : o ≠ .sc := by
      by_cases hA : A l
      · rcases hd.1 hA with h | h <;> simp [h]
      · simp [hd.2 hA]
    rcases k with _ | k <;> cases o <;> simp_all [halfLab, is_sc, mod, modeW]
  | U l or ow vr vw =>
    obtain ⟨-, h1, h2⟩ := hd
    rcases k with _ | _ | k <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
      simp [halfLab, is_sc, mod, modeR, modeW]

theorem not_sc {A : Loc → Prop} (hA : G.LabDisc A) (x : Act ι Loc) : ¬ (toIMM G).Sc x := by
  cases x with
  | InitEvent l => simp [execution.Sc, toIMM, is_sc, mod, labT]
  | ThreadEvent t i =>
    simp only [execution.Sc, toIMM]
    rw [is_sc_eq, labT_thread]
    split_ifs with h
    · rw [halfLab_not_sc (hA _ h)]; simp
    · simp [is_sc, mod]

/-! ### Relations of the translation -/

theorem sb_iff {x y : Act ι Loc} :
    (toIMM G).sb x y ↔ (toIMM G).E x ∧ ext_sb x y ∧ (toIMM G).E y := by
  unfold execution.sb; simp only [seq_eqv_l, seq_eqv_r]

theorem sb_of_G {x y : Act ι Loc} (h : G.sb (dec x) (dec y)) (hx : (toIMM G).E x)
    (hy : (toIMM G).E y) : (toIMM G).sb x y := by
  refine sb_iff.2 ⟨hx, ?_, hy⟩
  cases x with
  | InitEvent l =>
    cases y with
    | InitEvent => exact h
    | ThreadEvent => trivial
  | ThreadEvent t i =>
    cases y with
    | InitEvent => exact h
    | ThreadEvent t' i' =>
      obtain ⟨-, rfl, -⟩ := E_thread.1 hx
      obtain ⟨-, rfl, -⟩ := E_thread.1 hy
      obtain ⟨hlt, -, ht⟩ := h
      exact ⟨by rw [ht], by omega⟩

theorem rmw_sb {x y : Act ι Loc} (h : (toIMM G).rmw x y) : (toIMM G).sb x y := by
  obtain ⟨e, he, hU, rfl, rfl⟩ := h
  refine sb_iff.2 ⟨E_rdA he, ?_, E_wrA_ev he⟩
  simp [rdA, wrA, wIdx_U hU, ext_sb]

theorem rmw_dec {x y : Act ι Loc} (h : (toIMM G).rmw x y) : dec x = dec y := by
  obtain ⟨e, he, hU, rfl, rfl⟩ := h
  simp

theorem sb_to_G {x y : Act ι Loc} (h : (toIMM G).sb x y) :
    G.sb (dec x) (dec y) ∨ (toIMM G).rmw x y := by
  obtain ⟨hx, hxy, hy⟩ := sb_iff.1 h
  cases x with
  | InitEvent l =>
    cases y with
    | InitEvent => exact hxy.elim
    | ThreadEvent t i => exact Or.inl (E_thread.1 hy).1
  | ThreadEvent t i =>
    cases y with
    | InitEvent => exact hxy.elim
    | ThreadEvent t' i' =>
      obtain ⟨hn, rfl, -⟩ := E_thread.1 hx
      obtain ⟨hn', ht, hpar⟩ := E_thread.1 hy
      obtain ⟨ht', hlt⟩ := hxy
      by_cases hd : i / 2 < i' / 2
      · refine Or.inl ⟨hd, hn', ?_⟩
        rw [ht] at ht'; exact Option.some.inj ht'
      · right
        have he : i' / 2 = i / 2 := by omega
        have hi : i = 2 * (i / 2) := by omega
        have hi' : i' = 2 * (i / 2) + 1 := by omega
        rw [he] at hpar ht
        have hU : isU (G.lab (i / 2)) = true := hpar.resolve_left (by omega)
        refine ⟨i / 2, hn, hU, ?_, ?_⟩
        · rw [rdA, ← hi]
        · rw [wrA, wIdx_U hU, ← hi', ht]

theorem rf_E_l {x y : Act ι Loc} (hwf : G.WF) (h : (toIMM G).rf x y) : (toIMM G).E x := by
  obtain ⟨w, e, hrf, rfl, rfl⟩ := h
  exact E_wrA (mem_of_isWrite (rfE_src hwf hrf).1)

theorem rf_E_r {x y : Act ι Loc} (h : (toIMM G).rf x y) : (toIMM G).E y := by
  obtain ⟨w, e, hrf, rfl, rfl⟩ := h
  exact E_rdA hrf.1

/-! ### Facts about our graphs -/

theorem rfE_src_write (hwf : G.WF) {w r : Ev Loc} (h : G.rfE w r) : G.IsWrite w := by
  obtain ⟨e, rfl, -, -⟩ := rfE_tgt h
  exact (rfE_src hwf h).1

theorem mo_trans {a b c : Ev Loc} (h1 : G.mo a b) (h2 : G.mo b c) : G.mo a c :=
  ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem mo_irrefl {a : Ev Loc} : ¬ G.mo a a := fun h => lt_irrefl _ h.2.2.2

theorem mo_total (hwf : G.WF) {a b : Ev Loc} (ha : G.IsWrite a) (hb : G.IsWrite b)
    (hl : G.loc a = G.loc b) (hne : a ≠ b) : G.mo a b ∨ G.mo b a := by
  have hts : G.tsE a ≠ G.tsE b := by
    intro heq
    cases a with
    | init l =>
      cases b with
      | init l' => exact hne (by simp only [Exec.loc] at hl; rw [hl])
      | ev e => have := hwf.tsW e hb.1 hb.2; simp [tsE] at heq; omega
    | ev e =>
      cases b with
      | init l' => have := hwf.tsW e ha.1 ha.2; simp [tsE] at heq; omega
      | ev e' => exact hne (congrArg _ (hwf.tsInj e ha.1 e' hb.1 ha.2 hb.2 hl heq))
  rcases lt_or_gt_of_ne hts with h | h
  · exact Or.inl ⟨ha, hb, hl, h⟩
  · exact Or.inr ⟨hb, ha, hl.symm, h⟩

theorem rf_func {w w' : Ev Loc} {e : ℕ} (h : G.rfE w (.ev e)) (h' : G.rfE w' (.ev e)) :
    w = w' := by
  obtain ⟨-, -, h⟩ := h
  obtain ⟨-, -, h'⟩ := h'
  cases hrf : G.rf e <;> simp only [hrf] at h h' <;> rw [h, h']

theorem upd_of_rf_write {a b : Ev Loc} (h : G.rfE a b) (hw : G.IsWrite b) :
    ∃ e, b = .ev e ∧ e < G.n ∧ (G.lab e).IsUpdate := by
  obtain ⟨e, rfl, he, hr⟩ := rfE_tgt h
  exact ⟨e, rfl, he, Label.upd_of hr hw.2⟩

theorem rf_exists {e : ℕ} (he : e < G.n) (hr : (G.lab e).IsRead) : ∃ w, G.rfE w (.ev e) := by
  cases hrf : G.rf e with
  | none => exact ⟨.init (G.lab e).loc, he, hr, by rw [hrf]⟩
  | some a => exact ⟨.ev a, he, hr, by rw [hrf]⟩

theorem relW_isWrite {w : Ev Loc} (h : G.RelW w) : G.IsWrite w := by
  cases w with
  | init => exact h.elim
  | ev e => exact ⟨h.1, Label.write_of_relW h.2⟩

/-! ### `eco`: a normal form of ours, given atomicity -/

section EcoNF

variable (hwf : G.WF)
  (hat : ∀ e < G.n, (G.lab e).IsUpdate → ∀ w, G.rfE w (.ev e) →
    G.mo w (.ev e) ∧ ∀ x, ¬ (G.mo w x ∧ G.mo x (.ev e)))
include hwf hat

/-- `mo; rf?` -/
def MoRf (G : RC11.Exec prog s0 v0) (a b : Ev Loc) : Prop := ∃ c, G.mo a c ∧ (c = b ∨ G.rfE c b)

/-- `rf ∪ mo; rf? ∪ rb; rf?` -/
def EcoNF (G : RC11.Exec prog s0 v0) (a b : Ev Loc) : Prop :=
  G.rfE a b ∨ MoRf G a b ∨ ∃ w, G.rfE w a ∧ MoRf G w b

omit hwf in
theorem mo_of_rf_upd {w b : Ev Loc} (h : G.rfE w b) (hw : G.IsWrite b) : G.mo w b := by
  obtain ⟨e, rfl, he, hu⟩ := upd_of_rf_write h hw
  exact (hat e he hu w h).1

theorem moRf_step {a b d : Ev Loc} (h : MoRf G a b)
    (hs : G.rfE b d ∨ G.mo b d ∨ G.rb b d) : MoRf G a d := by
  obtain ⟨c, hac, hcb⟩ := h
  rcases hcb with rfl | hcb
  · rcases hs with hs | hs | ⟨w, hwb, hwd⟩
    · exact ⟨c, hac, Or.inr hs⟩
    · exact ⟨d, mo_trans hac hs, Or.inl rfl⟩
    · obtain ⟨e, rfl, he, hu⟩ := upd_of_rf_write hwb hac.2.1
      obtain ⟨hwmo, himm⟩ := hat e he hu w hwb
      by_cases haw : a = w
      · subst haw; exact ⟨d, hwd, Or.inl rfl⟩
      · rcases mo_total hwf hac.1 hwmo.1 (hac.2.2.1.trans hwmo.2.2.1.symm) haw with h | h
        · exact ⟨d, mo_trans h hwd, Or.inl rfl⟩
        · exact absurd ⟨h, hac⟩ (himm a)
  · rcases hs with hs | hs | ⟨w, hwb, hwd⟩
    · have := mo_of_rf_upd hat hcb (rfE_src_write hwf hs)
      exact ⟨b, mo_trans hac this, Or.inr hs⟩
    · have := mo_of_rf_upd hat hcb hs.1
      exact ⟨d, mo_trans (mo_trans hac this) hs, Or.inl rfl⟩
    · obtain ⟨e, rfl, -⟩ := rfE_tgt hcb
      rw [rf_func hcb hwb] at hac
      exact ⟨d, mo_trans hac hwd, Or.inl rfl⟩

theorem ecoNF_step {a b d : Ev Loc} (h : EcoNF G a b)
    (hs : G.rfE b d ∨ G.mo b d ∨ G.rb b d) : EcoNF G a d := by
  rcases h with h | h | ⟨w, hwa, h⟩
  · rcases hs with hs | hs | ⟨w, hwb, hwd⟩
    · exact Or.inr (Or.inl ⟨b, mo_of_rf_upd hat h (rfE_src_write hwf hs), Or.inr hs⟩)
    · exact Or.inr (Or.inl ⟨d, mo_trans (mo_of_rf_upd hat h hs.1) hs, Or.inl rfl⟩)
    · obtain ⟨e, rfl, -⟩ := rfE_tgt h
      rw [← rf_func h hwb] at hwd
      exact Or.inr (Or.inl ⟨d, hwd, Or.inl rfl⟩)
  · exact Or.inr (Or.inl (moRf_step hwf hat h hs))
  · exact Or.inr (Or.inr ⟨w, hwa, moRf_step hwf hat h hs⟩)

theorem ecoNF_of_eco {a b : Ev Loc} (h : G.eco a b) : EcoNF G a b := by
  induction h with
  | single hs =>
    rcases hs with hs | hs | ⟨w, hwa, hwb⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inl ⟨_, hs, Or.inl rfl⟩)
    · exact Or.inr (Or.inr ⟨w, hwa, _, hwb, Or.inl rfl⟩)
  | tail _ hs ih => exact ecoNF_step hwf hat ih hs

end EcoNF

theorem mem_of_rfE_src (hwf : G.WF) {w r : Ev Loc} (h : G.rfE w r) : G.Mem w := by
  exact mem_of_isWrite (rfE_src_write hwf h)

theorem ecoNF_I (hwf : G.WF) {a b : Ev Loc} (h : EcoNF G a b) :
    ∃ x y, Part G a x ∧ Part G b y ∧ (toIMM G).eco x y := by
  rcases h with h | ⟨c, hac, hcb⟩ | ⟨w, hwa, c, hwc, hcb⟩
  · obtain ⟨e, rfl, he, -⟩ := rfE_tgt h
    exact ⟨_, _, part_wrA (mem_of_rfE_src hwf h), part_rdA he,
      Or.inl (Or.inl ⟨a, e, h, rfl, rfl⟩)⟩
  · rcases hcb with rfl | hcb
    · exact ⟨_, _, part_wrA (mem_of_isWrite hac.1), part_wrA (mem_of_isWrite hac.2.1),
        Or.inl (Or.inr ⟨_, ⟨a, c, hac, rfl, rfl⟩, Or.inl rfl⟩)⟩
    · obtain ⟨e, rfl, he, -⟩ := rfE_tgt hcb
      exact ⟨_, _, part_wrA (mem_of_isWrite hac.1), part_rdA he,
        Or.inl (Or.inr ⟨_, ⟨a, c, hac, rfl, rfl⟩, Or.inr ⟨c, e, hcb, rfl, rfl⟩⟩)⟩
  · obtain ⟨ea, rfl, hea, -⟩ := rfE_tgt hwa
    have hfr : (toIMM G).fr (rdA G ea) (wrA G c) :=
      ⟨wrA G w, ⟨w, ea, hwa, rfl, rfl⟩, ⟨w, c, hwc, rfl, rfl⟩⟩
    rcases hcb with rfl | hcb
    · exact ⟨_, _, part_rdA hea, part_wrA (mem_of_isWrite hwc.2.1), Or.inr ⟨_, hfr, Or.inl rfl⟩⟩
    · obtain ⟨e, rfl, he, -⟩ := rfE_tgt hcb
      exact ⟨_, _, part_rdA hea, part_rdA he, Or.inr ⟨_, hfr, Or.inr ⟨c, e, hcb, rfl, rfl⟩⟩⟩

theorem eco_to_G {x y : Act ι Loc} (h : (toIMM G).eco x y) : G.eco (dec x) (dec y) := by
  have tailRf : ∀ {a : Ev Loc} {z y : Act ι Loc}, G.eco a (dec z) → (toIMM G).rf^? z y →
      G.eco a (dec y) := by
    intro a z y h hz
    rcases hz with rfl | ⟨w, e, hrf, rfl, rfl⟩
    · exact h
    · rw [dec_wrA] at h; rw [dec_rdA]; exact h.tail (Or.inl hrf)
  rcases h with (⟨w, e, hrf, rfl, rfl⟩ | ⟨z, ⟨a, b, hmo, rfl, rfl⟩, hz⟩) | ⟨z, ⟨w, hrfw, hco⟩, hz⟩
  · rw [dec_wrA, dec_rdA]; exact .single (Or.inl hrf)
  · exact tailRf (by rw [dec_wrA, dec_wrA]; exact .single (Or.inr (Or.inl hmo))) hz
  · obtain ⟨w', e, hrf, rfl, rfl⟩ := hrfw
    obtain ⟨a, b, hmo, ha, rfl⟩ := hco
    rw [wrA_inj ha] at hrf
    exact tailRf (by rw [dec_rdA, dec_wrA]; exact .single (Or.inr (Or.inr ⟨a, hrf, hmo⟩))) hz

/-! ### `hb` -/

theorem to_wr {a : Ev Loc} {x : Act ι Loc} (hp : Part G a x) (hw : G.IsWrite a) :
    (toIMM G).sb^? x (wrA G a) := by
  cases a with
  | init l => rw [part_init hp]; exact Or.inl rfl
  | ev e =>
    obtain ⟨he, rfl | ⟨-, rfl⟩⟩ := part_ev hp
    · cases hU : isU (G.lab e)
      · exact Or.inl (wrA_nU hU).symm
      · exact Or.inr (rmw_sb ⟨e, he, hU, rfl, rfl⟩)
    · exact Or.inl rfl

theorem from_rd {e : ℕ} {y : Act ι Loc} (hp : Part G (.ev e) y) : (toIMM G).sb^? (rdA G e) y := by
  obtain ⟨he, rfl | ⟨hU, rfl⟩⟩ := part_ev hp
  · exact Or.inl rfl
  · exact Or.inr (rmw_sb ⟨e, he, hU, rfl, rfl⟩)

theorem rs_of_G {a w : Ev Loc} (h : G.rs a w) : (toIMM G).rs (wrA G a) (wrA G w) := by
  obtain ⟨hwa, c, hc, hwc, -, hch⟩ := h
  refine ⟨_, ⟨rfl, W_wrA hwa⟩, wrA G c, ?_, _, ⟨rfl, W_wrA hwc⟩, ?_⟩
  · rcases hc with rfl | ⟨hsb, hl⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨sb_of_G (by rw [dec_wrA, dec_wrA]; exact hsb) (E_wrA (mem_of_isWrite hwa))
        (E_wrA (mem_of_isWrite hwc)), ?_⟩
      show loc _ _ = loc _ _
      rw [loc_wrA hwa, loc_wrA hwc, hl]
  · induction hch with
    | refl => exact .refl
    | tail _ hs ih =>
      obtain ⟨hr, e, rfl, hu⟩ := hs
      exact Relation.ReflTransGen.tail ih ⟨rdA G e, ⟨_, e, hr, rfl, rfl⟩,
        ⟨e, hr.1, isU_iff.2 hu, rfl, rfl⟩⟩

theorem sw_of_G {a : Ev Loc} {e : ℕ} (h : G.sw a (.ev e)) : (toIMM G).sw (wrA G a) (rdA G e) := by
  obtain ⟨hrel, w, hrs, hrf, hacq⟩ := h
  refine ⟨wrA G w, ⟨_, ⟨rfl, (rel_wrA (relW_isWrite hrel)).2 hrel⟩, _, Or.inl rfl, rs_of_G hrs⟩,
    rdA G e, ⟨w, e, hrf, rfl, rfl⟩, rdA G e, Or.inl rfl, rfl, ?_⟩
  exact (acq_rdA hrf.1 hrf.2.1).2 hacq

theorem hb_step (hwf : G.WF) {a b : Ev Loc} {x y : Act ι Loc} (h : G.sb a b ∨ G.sw a b)
    (hx : Part G a x) (hy : Part G b y) : (toIMM G).hb x y := by
  rcases h with h | h
  · exact .single (Or.inl (sb_of_G (by rw [hx.2, hy.2]; exact h) hx.1 hy.1))
  · obtain ⟨xa, e, rfl, rfl, -, -⟩ := sw_tgt hwf h
    have hsw : (toIMM G).hb (wrA G (.ev xa)) (rdA G e) := .single (Or.inr (sw_of_G h))
    have h1 := to_wr hx (relW_isWrite h.1)
    have h2 := from_rd hy
    have h' : (toIMM G).hb x (rdA G e) := by
      rcases h1 with h1 | h1
      · rw [h1]; exact hsw
      · exact Relation.TransGen.head (Or.inl h1) hsw
    rcases h2 with h2 | h2
    · rw [← h2]; exact h'
    · exact Relation.TransGen.tail h' (Or.inl h2)

/-- Our `hb` is contained in IMM's, between any halves. -/
theorem hb_of_G (hwf : G.WF) {a b : Ev Loc} (h : G.hb a b) :
    ∀ x y, Part G a x → Part G b y → (toIMM G).hb x y := by
  induction h with
  | single hs => intro x y hx hy; exact hb_step hwf hs hx hy
  | tail hac hcb ih =>
    intro x y hx hy
    obtain ⟨e, rfl, he, -⟩ := hb_tgt hwf hac
    exact Relation.TransGen.trans (ih x _ hx (part_rdA he)) (hb_step hwf hcb (part_rdA he) hy)

theorem rs_E (hwf : G.WF) {x z : Act ι Loc} (h : (toIMM G).rs x z) (hz : (toIMM G).E z) :
    (toIMM G).E x := by
  obtain ⟨_, ⟨rfl, -⟩, c, hopt, _, ⟨rfl, -⟩, hch⟩ := h
  have hc : (toIMM G).E c := by
    rcases Relation.ReflTransGen.cases_head hch with rfl | ⟨c', ⟨r, hrf, -⟩, -⟩
    · exact hz
    · exact rf_E_l hwf hrf
  rcases hopt with rfl | ⟨hsb, -⟩
  · exact hc
  · exact (sb_iff.1 hsb).1

theorem relW_of {x : Act ι Loc} (hE : (toIMM G).E x) (hW : (toIMM G).W x)
    (hR : (toIMM G).Rel x) : G.RelW (dec x) := by
  obtain ⟨hx, hw⟩ := W_E hE hW
  rw [hx] at hR
  exact (rel_wrA hw).1 hR

/-- IMM's release sequences are ours, for disciplined graphs. -/
theorem rs_to_G {A : Loc → Prop} (hA : G.LabDisc A) {x z : Act ι Loc}
    (h : (toIMM G).rs x z) (hE : (toIMM G).E x) (hR : (toIMM G).Rel x) :
    G.rs (dec x) (dec z) := by
  obtain ⟨_, ⟨rfl, hWx⟩, c, hopt, _, ⟨rfl, hWc⟩, hch⟩ := h
  have hrel := relW_of hE hWx hR
  obtain ⟨hxw, hdx⟩ := W_E hE hWx
  obtain ⟨ex, hex⟩ : ∃ ex, dec x = .ev ex := by
    cases h : dec x with
    | init => rw [h] at hrel; exact hrel.elim
    | ev ex => exact ⟨ex, rfl⟩
  rw [hex] at hrel hdx
  have hcE : (toIMM G).E c := by
    rcases hopt with rfl | ⟨hsb, -⟩
    · exact hE
    · exact (sb_iff.1 hsb).2.2
  obtain ⟨hcw, hdc⟩ := W_E hcE hWc
  refine ⟨hex ▸ hdx, dec c, ?_, hdc, ?_, ?_⟩
  · rcases hopt with rfl | ⟨hsb, hl⟩
    · exact Or.inl rfl
    · rcases sb_to_G hsb with h | h
      · refine Or.inr ⟨h, ?_⟩
        have hl' : loc (toIMM G).lab x = loc (toIMM G).lab c := hl
        rw [hxw, hcw, loc_wrA (hex ▸ hdx), loc_wrA hdc] at hl'
        exact Option.some.inj hl'
      · exact Or.inl (rmw_dec h).symm
  · rcases hopt with rfl | ⟨hsb, hl⟩
    · rw [hex]; exact Label.atomicW_of_relW hrel.2
    · have hl' : loc (toIMM G).lab x = loc (toIMM G).lab c := hl
      rw [hxw, hcw, loc_wrA (hex ▸ hdx), loc_wrA hdc, hex] at hl'
      rcases sb_to_G hsb with h | h
      · obtain ⟨ec, hec, -, -⟩ := sb_tgt h
        rw [hec] at hl' hdc ⊢
        have hAl := Label.disc_relW (hA ex hrel.1) hrel.2
        simp only [Exec.loc, Option.some.injEq] at hl'
        exact Label.disc_atomicW (hA ec hdc.1) (hl' ▸ hAl) hdc.2
      · rw [← rmw_dec h, hex]; exact Label.atomicW_of_relW hrel.2
  · clear hopt hcw hdc hcE
    induction hch with
    | refl => exact .refl
    | tail _ hs ih =>
      obtain ⟨r, ⟨w, e, hrf, rfl, rfl⟩, ⟨e', he', hU, hr, rfl⟩⟩ := hs
      rw [rdA_inj hr] at hrf
      rw [dec_wrA] at ih
      exact Relation.ReflTransGen.tail ih ⟨by rw [dec_wrA]; exact hrf, e', by rw [dec_wrA],
        isU_iff.1 hU⟩

/-- IMM's `sw` is ours, for disciplined graphs. -/
theorem sw_to_G (hwf : G.WF) {A : Loc → Prop} (hA : G.LabDisc A) {x y : Act ι Loc}
    (h : (toIMM G).sw x y) : G.sw (dec x) (dec y) := by
  obtain ⟨z, ⟨_, ⟨rfl, hRel⟩, x2, hopt2, hrs⟩, y1, hrf, y2, hopt, ⟨rfl, hacq⟩⟩ := h
  have hy : y1 = y2 := by
    rcases hopt with h | h
    · exact h
    · rw [seq_eqv_r] at h
      exact absurd h.2 (E_notF (sb_iff.1 h.1).2.2)
  subst hy
  have hx : x = x2 := by
    rcases hopt2 with h | h
    · exact h
    · rw [seq_eqv_l] at h
      exact absurd h.1 (E_notF (sb_iff.1 h.2).1)
  subst hx
  have hzE := rf_E_l hwf hrf
  obtain ⟨w, e, hrfE, rfl, rfl⟩ := hrf
  have hxE := rs_E hwf hrs hzE
  have hrsG := rs_to_G hA hrs hxE hRel
  rw [dec_wrA] at hrsG
  rw [dec_rdA]
  refine ⟨relW_of hxE ?_ hRel, w, hrsG, hrfE, (acq_rdA hrfE.1 hrfE.2.1).1 hacq⟩
  obtain ⟨_, ⟨rfl, hW⟩, -⟩ := hrs
  exact hW

/-- IMM's `hb` is ours, up to the step between the halves of an update. -/
theorem hb_to_G (hwf : G.WF) {A : Loc → Prop} (hA : G.LabDisc A) {x y : Act ι Loc}
    (h : (toIMM G).hb x y) : G.hb (dec x) (dec y) ∨ (toIMM G).rmw x y := by
  have step : ∀ {x y}, ((toIMM G).sb ∪ᵣ (toIMM G).sw) x y →
      G.hb (dec x) (dec y) ∨ (toIMM G).rmw x y := by
    intro x y h
    rcases h with h | h
    · exact (sb_to_G h).imp_left hb_of_sb
    · exact Or.inl (hb_of_sw (sw_to_G hwf hA h))
  induction h with
  | single hs => exact step hs
  | tail _ hs ih =>
    rcases ih with h1 | h1 <;> rcases step hs with h2 | h2
    · exact Or.inl (hb_trans h1 h2)
    · rw [← rmw_dec h2]; exact Or.inl h1
    · rw [rmw_dec h1]; exact Or.inl h2
    · obtain ⟨e, -, hU, rfl, rfl⟩ := h1
      obtain ⟨e', -, -, h, rfl⟩ := h2
      have := congrArg dec h
      simp only [dec_wrA, dec_rdA, Ev.ev.injEq] at this
      subst this
      exact absurd h.symm (rdA_ne_wrA hU)

/-! ### The main results -/

/-- **Well-formedness.** The translation of a well-formed graph is a
well-formed IMM execution (all 28 fields of `Wf`), with initial values `v0`. -/
theorem wf_toIMM (hwf : G.WF) : (toIMM G).Wf v0 none where
  wf_index := by
    rintro a b ⟨ha, hbE, hne, htid, hinit⟩ hidx
    cases a with
    | InitEvent => exact absurd hinit (by simp [is_init])
    | ThreadEvent t i =>
      cases b with
      | InitEvent =>
        obtain ⟨-, rfl, -⟩ := E_thread.1 ha
        exact absurd htid (by simp [tid])
      | ThreadEvent t' i' =>
        simp only [tid] at htid; simp only [index] at hidx
        exact hne (by rw [htid, hidx])
  data_in_sb _ _ h := False.elim h
  wf_dataD := ⟨fun _ _ h => False.elim h, fun _ _ ⟨_, _, _, h, _⟩ => False.elim h⟩
  addr_in_sb _ _ h := False.elim h
  wf_addrD := ⟨fun _ _ h => False.elim h, fun _ _ ⟨_, _, _, h, _⟩ => False.elim h⟩
  ctrl_in_sb _ _ h := False.elim h
  wf_ctrlD := ⟨fun _ _ h => False.elim h, fun _ _ ⟨_, _, h⟩ => False.elim h⟩
  ctrl_sb _ _ := fun ⟨_, h, _⟩ => False.elim h
  wf_rmwD := by
    refine ⟨?_, fun x y ⟨_, ⟨rfl, _⟩, _, h, rfl, _⟩ => h⟩
    intro x y h
    obtain ⟨e, he, hU, rfl, rfl⟩ := h
    have hu := isU_iff.1 hU
    rw [seq_eqv_l, seq_eqv_r]
    exact ⟨R_rdA he (Label.read_of_upd hu), ⟨e, he, hU, rfl, rfl⟩,
      W_wrA (w := .ev e) ⟨he, Label.write_of_upd hu⟩⟩
  wf_rmwl := by
    intro x y h
    obtain ⟨e, he, hU, rfl, rfl⟩ := h
    show loc _ _ = loc _ _
    rw [loc_rdA he, loc_wrA (w := .ev e) ⟨he, Label.write_of_upd (isU_iff.1 hU)⟩]; rfl
  wf_rmwi := by
    intro x y h
    refine ⟨rmw_sb h, fun c h1 h2 => ?_⟩
    obtain ⟨e, he, hU, rfl, rfl⟩ := h
    have h1 := (sb_iff.1 h1).2.1
    have h2 := (sb_iff.1 h2).2.1
    cases c with
    | InitEvent => exact h1
    | ThreadEvent t i =>
      simp only [rdA, wrA, wIdx_U hU, ext_sb] at h1 h2
      omega
  wf_rfE := by
    refine ⟨fun x y h => ?_, fun x y ⟨_, ⟨rfl, _⟩, _, h, rfl, _⟩ => h⟩
    rw [seq_eqv_l, seq_eqv_r]
    exact ⟨rf_E_l hwf h, h, rf_E_r h⟩
  wf_rfD := by
    refine ⟨fun x y h => ?_, fun x y ⟨_, ⟨rfl, _⟩, _, h, rfl, _⟩ => h⟩
    rw [seq_eqv_l, seq_eqv_r]
    refine ⟨?_, h, ?_⟩
    · obtain ⟨w, e, hrf, rfl, rfl⟩ := h
      exact W_wrA (rfE_src hwf hrf).1
    · obtain ⟨w, e, hrf, rfl, rfl⟩ := h
      exact R_rdA hrf.1 hrf.2.1
  wf_rfl := by
    intro x y h
    obtain ⟨w, e, hrf, rfl, rfl⟩ := h
    obtain ⟨hw, hl, -⟩ := rfE_src hwf hrf
    show loc _ _ = loc _ _
    rw [loc_wrA hw, loc_rdA hrf.1, hl]
  wf_rfv := by
    intro x y h
    obtain ⟨w, e, hrf, rfl, rfl⟩ := h
    obtain ⟨he, hr, hw⟩ := hrf
    have hsrc := hwf.rfSrc e he hr
    rw [val_rdA he hr]
    cases hrfe : G.rf e with
    | none =>
      rw [hrfe] at hw hsrc; subst hw
      rw [hsrc]; rfl
    | some a =>
      rw [hrfe] at hw hsrc; subst hw
      obtain ⟨hlt, hwa, -, hv⟩ := hsrc
      rw [hv, val_wrA_ev (by omega) hwa]
  wf_rff := by
    intro x y z h1 h2
    obtain ⟨w, e, hrf, rfl, rfl⟩ := h1
    obtain ⟨w', e', hrf', rfl, he⟩ := h2
    rw [rdA_inj he] at hrf
    rw [rf_func hrf hrf']
  wf_coE := by
    refine ⟨fun x y h => ?_, fun x y ⟨_, ⟨rfl, _⟩, _, h, rfl, _⟩ => h⟩
    rw [seq_eqv_l, seq_eqv_r]
    refine ⟨?_, h, ?_⟩
    · obtain ⟨a, b, hmo, rfl, rfl⟩ := h; exact E_wrA (mem_of_isWrite hmo.1)
    · obtain ⟨a, b, hmo, rfl, rfl⟩ := h; exact E_wrA (mem_of_isWrite hmo.2.1)
  wf_coD := by
    refine ⟨fun x y h => ?_, fun x y ⟨_, ⟨rfl, _⟩, _, h, rfl, _⟩ => h⟩
    rw [seq_eqv_l, seq_eqv_r]
    refine ⟨?_, h, ?_⟩
    · obtain ⟨a, b, hmo, rfl, rfl⟩ := h; exact W_wrA hmo.1
    · obtain ⟨a, b, hmo, rfl, rfl⟩ := h; exact W_wrA hmo.2.1
  wf_col := by
    intro x y h
    obtain ⟨a, b, hmo, rfl, rfl⟩ := h
    show loc _ _ = loc _ _
    rw [loc_wrA hmo.1, loc_wrA hmo.2.1, hmo.2.2.1]
  co_trans := by
    intro x y z h1 h2
    obtain ⟨a, b, hab, rfl, rfl⟩ := h1
    obtain ⟨b', c, hbc, hbb, rfl⟩ := h2
    rw [← wrA_inj hbb] at hbc
    exact ⟨a, c, mo_trans hab hbc, rfl, rfl⟩
  wf_co_total := by
    intro ol a ⟨⟨ha, hwa⟩, hla⟩ b ⟨⟨hbE, hwb⟩, hlb⟩ hne
    obtain ⟨ha', hda⟩ := W_E ha hwa
    obtain ⟨hb', hdb⟩ := W_E hbE hwb
    have hl : G.loc (dec a) = G.loc (dec b) := by
      have h1 : loc (toIMM G).lab a = loc (toIMM G).lab b := hla.trans hlb.symm
      rw [ha', hb', loc_wrA hda, loc_wrA hdb] at h1
      exact Option.some.inj h1
    have hne' : dec a ≠ dec b := fun h => hne (by rw [ha', hb', h])
    rcases mo_total hwf hda hdb hl hne' with h | h
    · exact Or.inl ⟨_, _, h, ha', hb'⟩
    · exact Or.inr ⟨_, _, h, hb', ha'⟩
  co_irr := by
    intro x h
    obtain ⟨a, b, hmo, rfl, hbb⟩ := h
    rw [wrA_inj hbb] at hmo
    exact mo_irrefl hmo
  wf_init _ _ := trivial
  wf_init_lab _ := rfl
  rmw_dep_in_sb _ _ h := False.elim h
  wf_rmw_depD := ⟨fun _ _ h => False.elim h, fun _ _ ⟨_, _, _, h, _⟩ => False.elim h⟩
  wf_threads _ _ := trivial

/-- **IMM-consistent ⇒ consistent**, for every well-formed graph (no
discipline needed: IMM's `hb` contains ours). -/
theorem consistent_of_rc11 (hwf : G.WF) (h : (toIMM G).rc11_consistent) : G.Consistent := by
  obtain ⟨-, hcoh, hcat, -, -⟩ := h
  have hat : ∀ e < G.n, (G.lab e).IsUpdate → ∀ w, G.rfE w (.ev e) →
      G.mo w (.ev e) ∧ ∀ x, ¬ (G.mo w x ∧ G.mo x (.ev e)) := by
    intro e he hu w hrf
    obtain ⟨hww, hloc, hlt⟩ := rfE_src hwf hrf
    have hwe : G.IsWrite (.ev e) := ⟨he, Label.write_of_upd hu⟩
    have hU : isU (G.lab e) = true := isU_iff.2 hu
    have hsb : (toIMM G).sb (rdA G e) (wrA G (.ev e)) := rmw_sb ⟨e, he, hU, rfl, rfl⟩
    have hrfI : (toIMM G).rf (wrA G w) (rdA G e) := ⟨w, e, hrf, rfl, rfl⟩
    constructor
    · have hne : w ≠ .ev e := by rintro rfl; exact lt_irrefl _ (hlt e rfl)
      rcases mo_total hwf hww hwe hloc hne with h | h
      · exact h
      · exact (hcoh (rdA G e) ⟨wrA G (.ev e), .single (Or.inl hsb),
          Or.inr (Or.inl (Or.inr ⟨_, ⟨_, _, h, rfl, rfl⟩, Or.inr hrfI⟩))⟩).elim
    · rintro x ⟨hwx, hxe⟩
      have hfr : (toIMM G).fr (rdA G e) (wrA G x) := ⟨_, hrfI, ⟨w, x, hwx, rfl, rfl⟩⟩
      have hco : (toIMM G).co (wrA G x) (wrA G (.ev e)) := ⟨x, _, hxe, rfl, rfl⟩
      have hxne : x ≠ .ev e := by rintro rfl; exact mo_irrefl hxe
      refine hcat (rdA G e) (wrA G (.ev e)) ⟨⟨e, he, hU, rfl, rfl⟩, wrA G x, ⟨hfr, ?_⟩, ⟨hco, ?_⟩⟩
      · intro hs
        rcases sb_to_G hs with h | h
        · rw [dec_rdA, dec_wrA] at h
          have := hb_of_G hwf (hb_of_sb h) _ _ (part_wrA hwe.1) (part_wrA (mem_of_isWrite hwx.2.1))
          exact hcoh _ ⟨_, this, Or.inr (Or.inl (Or.inr ⟨_, hco, Or.inl rfl⟩))⟩
        · have := rmw_dec h; rw [dec_rdA, dec_wrA] at this; exact hxne this.symm
      · intro hs
        rcases sb_to_G hs with h | h
        · rw [dec_wrA, dec_wrA] at h
          have := hb_of_G hwf (hb_of_sb h) _ _ (part_wrA (mem_of_isWrite hwx.2.1)) (part_rdA he)
          exact hcoh _ ⟨_, this, Or.inr (Or.inr ⟨_, hfr, Or.inl rfl⟩)⟩
        · have := rmw_dec h; rw [dec_wrA, dec_wrA] at this; exact hxne this
  refine ⟨hwf, ?_, ?_, hat⟩
  · intro a h
    obtain ⟨e, rfl, -, hlt⟩ := hb_tgt hwf h
    exact lt_irrefl _ (hlt e rfl)
  · intro a b hab heco
    obtain ⟨x, y, hx, hy, he⟩ := ecoNF_I hwf (ecoNF_of_eco hwf hat heco)
    exact hcoh y ⟨x, hb_of_G hwf hab y x hy hx, Or.inr he⟩

/-- The measure showing `acyclic (sb ∪ rf)`. -/
def meas : Act ι Loc → ℕ
  | InitEvent _ => 0
  | ThreadEvent _ i => i + 1

/-- **Consistent ⇒ IMM-consistent**, for location-disciplined graphs. -/
theorem rc11_of_consistent (hc : G.Consistent) {A : Loc → Prop} (hA : G.LabDisc A) :
    (toIMM G).rc11_consistent := by
  have hwf := hc.wf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- complete
    rintro x ⟨hE, hR⟩
    obtain ⟨e, rfl, he, hr⟩ := R_E hE hR
    obtain ⟨w, hw⟩ := rf_exists he hr
    exact ⟨_, w, e, hw, rfl, rfl⟩
  · -- coherence
    rintro x ⟨y, hxy, hyx⟩
    rcases hb_to_G hwf hA hxy with h | ⟨e, he, hU, rfl, rfl⟩
    · rcases hyx with rfl | heco
      · exact hc.hbIrrefl _ h
      · exact hc.coherence _ _ h (eco_to_G heco)
    · rcases hyx with h | (hrf | ⟨z, hco, hz⟩) | ⟨z, ⟨w, hrfw, -⟩, -⟩
      · exact rdA_ne_wrA hU h.symm
      · obtain ⟨w, e', hrf, hw, he'⟩ := hrf
        rw [← wrA_inj hw, ← rdA_inj he'] at hrf
        exact lt_irrefl _ ((rfE_src hwf hrf).2.2 e rfl)
      · obtain ⟨a, b, hmo, ha, rfl⟩ := hco
        rw [← wrA_inj ha] at hmo
        rcases hz with hz | ⟨w, e', hrf, hw, he'⟩
        · have := congrArg dec hz
          rw [dec_wrA, dec_rdA] at this
          rw [this] at hmo
          exact mo_irrefl hmo
        · rw [← wrA_inj hw, ← rdA_inj he'] at hrf
          have := (hc.atomicity e he (isU_iff.1 hU) b hrf).1
          exact mo_irrefl (mo_trans hmo this)
      · obtain ⟨w', e', -, -, hy⟩ := hrfw
        have := congrArg dec hy
        rw [dec_wrA, dec_rdA] at this
        cases this
        exact rdA_ne_wrA hU hy.symm
  · -- rmw_atomicity
    rintro x y ⟨⟨e, he, hU, rfl, rfl⟩, z, ⟨hfr, -⟩, ⟨hco, -⟩⟩
    obtain ⟨_, ⟨w, e', hrf, rfl, he'⟩, ⟨a, b, hmo, ha, rfl⟩⟩ := hfr
    obtain ⟨b', c, hmo2, hbb, hc'⟩ := hco
    rw [← rdA_inj he'] at hrf
    rw [← wrA_inj ha] at hmo
    rw [← wrA_inj hbb] at hmo2
    rw [← wrA_inj hc'] at hmo2
    exact (hc.atomicity e he (isU_iff.1 hU) w hrf).2 b ⟨hmo, hmo2⟩
  · -- acyclic (psc_f ∪ psc_base): there are no SC events
    intro x hx
    obtain ⟨y, hxy, -⟩ := Relation.TransGen.head'_iff.1 hx
    rcases hxy with ⟨_, ⟨rfl, -, hsc⟩, -⟩ | ⟨_, ⟨rfl, hsc⟩, -⟩
    · exact not_sc hA x hsc
    · exact not_sc hA x hsc
  · -- acyclic (sb ∪ rf): the numbering
    have step : ∀ x y, ((toIMM G).sb ∪ᵣ (toIMM G).rf) x y → meas x < meas y := by
      rintro x y (h | ⟨w, e, hrf, rfl, rfl⟩)
      · have := (sb_iff.1 h).2.1
        cases x <;> cases y <;> simp_all [ext_sb, meas]
      · cases w with
        | init l => simp [wrA, rdA, meas]
        | ev a =>
          have := (rfE_src hwf hrf).2.2 a rfl
          simp only [wrA, rdA, meas, wIdx]
          split <;> omega
    have key : ∀ x y, Relation.TransGen ((toIMM G).sb ∪ᵣ (toIMM G).rf) x y → meas x < meas y := by
      intro x y h
      induction h with
      | single h => exact step _ _ h
      | tail _ h ih => exact ih.trans (step _ _ h)
    intro x hx
    exact lt_irrefl _ (key x x hx)

/-- **The equivalence.** A well-formed, location-disciplined graph is
consistent in our RC11 iff its translation is `rc11_consistent` in IMM. -/
theorem consistent_iff (hwf : G.WF) {A : Loc → Prop} (hA : G.LabDisc A) :
    G.Consistent ↔ (toIMM G).rc11_consistent :=
  ⟨fun hc => rc11_of_consistent hc hA, consistent_of_rc11 hwf⟩

end Translation

/-! ## The discipline is needed: a counterexample

IMM's `rs` (imm_s_hb.v L66) is `⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊`,
while RC11 (and `RC11.Exec.rs`) require the write after `(sb ∩ same_loc)^?`
to be atomic. With a non-atomic write sb-after a release write to the same
location, IMM's `hb` is larger. Locations `x = true`, `y = false`:

* `T1` (thread `true`): `y.store(1, na)` (event 0); `x.store(1, rel)` (event
  1); `x.store(2, na)` (event 2).
* `T2` (thread `false`): `x.load(acq)` reading `2` from event 2 (event 3);
  `y.load(na)` reading the initial `0` (event 4).

For us there is no `sw` (the release sequence of event 1 cannot continue to
the non-atomic event 2), so the graph is consistent (and racy: events 2 and 3
are unordered by `hb`). In IMM, event 2 is in the release sequence of event 1,
so `0 →sb 1 →sw 3 →sb 4`, and event 4 reads the initialization of `y`, which
is `co`-before event 0: `hb ⨾ fr` is reflexive and coherence fails. There are
no SC accesses, so this is not about `psc`. -/

namespace Counterexample

open RC11 RC11.Exec actid

/-- The program: thread `true` is `T1`, thread `false` is `T2`. -/
def prog : (i : Bool) → ℕ → Instr Bool ℕ ℕ
  | true, 0 => .write false .na 1 1
  | true, 1 => .write true .acqrel 1 2
  | true, 2 => .write true .na 2 3
  | true, _ => .halt
  | false, 0 => .read true .acqrel (fun _ => 1)
  | false, 1 => .read false .na (fun _ => 2)
  | false, _ => .halt

def lab : ℕ → RC11.Label Bool ℕ
  | 0 => .W false .na 1
  | 1 => .W true .acqrel 1
  | 2 => .W true .na 2
  | 3 => .R true .acqrel (some 2)
  | _ => .R false .na (some 0)

/-- The execution graph. -/
def G : RC11.Exec prog (fun _ => 0) (fun _ => some 0) where
  n := 5
  tid e := decide (e < 3)
  lab := lab
  rf e := if e = 3 then some 2 else none
  ts
    | 0 => 2
    | 1 => 2
    | 2 => 3
    | _ => 0
  active := {true, false}
  items
    | true => [.inl 0, .inl 1, .inl 2]
    | false => [.inl 3, .inl 4]
  final
    | true => 3
    | false => 2
  run i := by cases i <;> rfl
  inactive i h := by cases i <;> simp at h
  itemsEv i := by cases i <;> decide

theorem G_wf : G.WF where
  rfSrc e he hr := by
    change e < 5 at he
    interval_cases e <;> simp_all [G, lab, Label.IsRead, Label.IsWrite, Label.loc, Label.rval,
      Label.wval]
  tsW e he hw := by
    change e < 5 at he
    interval_cases e <;> simp_all [G, lab, Label.IsWrite]
  tsInj a ha b hb hwa hwb hl ht := by
    change a < 5 at ha; change b < 5 at hb
    interval_cases a <;> interval_cases b <;> simp_all [G, lab, Label.IsWrite, Label.loc]
  tsDense e he hw t h1 h2 := by
    change e < 5 at he
    interval_cases e
    · exact ⟨0, by decide, by simp [G, lab, Label.IsWrite], rfl, by simp [G] at h2 ⊢; omega⟩
    · exact ⟨1, by decide, by simp [G, lab, Label.IsWrite], rfl, by simp [G] at h2 ⊢; omega⟩
    · simp only [G] at h2
      by_cases ht : t = 2
      · exact ⟨1, by decide, by simp [G, lab, Label.IsWrite], rfl, by simp [G, ht]⟩
      · exact ⟨2, by decide, by simp [G, lab, Label.IsWrite], rfl, by simp [G]; omega⟩
    all_goals simp [G, lab, Label.IsWrite] at hw

/-- The only reads-from edges: `2 → 3` and `init y → 4`. -/
theorem G_rfE {w r : Ev Bool} (h : G.rfE w r) :
    (w = .ev 2 ∧ r = .ev 3) ∨ (w = .init false ∧ r = .ev 4) := by
  obtain ⟨e, rfl, he, hr⟩ := rfE_tgt h
  change e < 5 at he
  have hw := h.2.2
  interval_cases e <;> simp_all [G, lab, Label.IsRead, Label.loc]

theorem G_isWrite {w : Ev Bool} (h : G.IsWrite w) :
    (∃ l, w = .init l) ∨ w = .ev 0 ∨ w = .ev 1 ∨ w = .ev 2 := by
  cases w with
  | init l => exact Or.inl ⟨l, rfl⟩
  | ev e =>
    obtain ⟨he, hw⟩ := h
    change e < 5 at he
    interval_cases e <;> simp_all [G, lab, Label.IsWrite]

theorem G_not_sw (a b : Ev Bool) : ¬ G.sw a b := by
  rintro ⟨-, w, ⟨-, c, -, -, hca, hch⟩, hrf, -⟩
  have hcw : c = w := by
    rcases Relation.ReflTransGen.cases_tail hch with h | ⟨_, -, -, e, -, hu⟩
    · exact h.symm
    · exact absurd hu (by simp only [G]; unfold lab; split <;> simp [Label.IsUpdate])
  subst hcw
  rcases G_rfE hrf with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact absurd hca (by simp [G, lab, Label.AtomicW])
  · exact hca

theorem G_sb_trans {a b c : Ev Bool} (h1 : G.sb a b) (h2 : G.sb b c) : G.sb a c := by
  cases a <;> cases b <;> cases c
  all_goals first
    | exact absurd h1 id
    | exact absurd h2 id
    | skip
  · exact h2.2.1
  · exact ⟨h1.1.trans h2.1, h2.2.1, h1.2.2.trans h2.2.2⟩

theorem G_hb_sb {a b : Ev Bool} (h : G.hb a b) : G.sb a b := by
  induction h with
  | single hs => exact hs.resolve_right (G_not_sw _ _)
  | tail _ hs ih => exact G_sb_trans ih (hs.resolve_right (G_not_sw _ _))

/-- All `eco` edges. -/
def ok (a b : Ev Bool) : Prop :=
  (a, b) ∈ [(.init true, .ev 1), (.init true, .ev 2), (.init true, .ev 3), (.ev 1, .ev 2),
    (.ev 1, .ev 3), (.ev 2, .ev 3), (.init false, .ev 4), (.init false, .ev 0), (.ev 4, .ev 0)]

theorem G_mo {a b : Ev Bool} (h : G.mo a b) : ok a b := by
  obtain ⟨ha, hb, hl, ht⟩ := h
  rcases G_isWrite ha with ⟨l, rfl⟩ | rfl | rfl | rfl <;>
    rcases G_isWrite hb with ⟨l', rfl⟩ | rfl | rfl | rfl <;>
    (try cases l) <;> (try cases l') <;>
    simp_all [ok, G, lab, tsE, Exec.loc, Label.loc]

theorem ok_step {a b : Ev Bool} (h : G.rfE a b ∨ G.mo a b ∨ G.rb a b) : ok a b := by
  rcases h with h | h | ⟨w, hwa, hwb⟩
  · rcases G_rfE h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ok]
  · exact G_mo h
  · have hbw := hwb.2.1
    have := G_mo hwb
    rcases G_rfE hwa with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ok] at this ⊢
    · subst this; simp [G, IsWrite, lab, Label.IsWrite] at hbw
    · rcases this with rfl | rfl
      · simp [G, IsWrite, lab, Label.IsWrite] at hbw
      · rfl

theorem ok_trans {a b c : Ev Bool} (h1 : ok a b) (h2 : ok b c) : ok a c := by
  simp only [ok, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h1 h2 ⊢
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

theorem G_eco {a b : Ev Bool} (h : G.eco a b) : ok a b := by
  induction h with
  | single hs => exact ok_step hs
  | tail _ hs ih => exact ok_trans ih (ok_step hs)

theorem G_consistent : G.Consistent where
  wf := G_wf
  hbIrrefl a h := by
    obtain ⟨e, rfl, -, hlt⟩ := hb_tgt G_wf h
    exact lt_irrefl _ (hlt e rfl)
  coherence a b hab heco := by
    have hsb := G_hb_sb hab
    have hok := G_eco heco
    simp only [ok, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hok
    rcases hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [G, Exec.sb]
  atomicity e he hu := by
    change e < 5 at he
    interval_cases e <;> simp [G, lab, Label.IsUpdate] at hu

/-- The graph is racy: T1's non-atomic store to `x` and T2's acquire load of it. -/
theorem G_racy : G.Racy := by
  refine ⟨.ev 2, .ev 3, ⟨⟨show 2 < 5 by omega, show 3 < 5 by omega, by simp, rfl,
    Or.inl ⟨show 2 < 5 by omega, trivial⟩⟩, ?_, ?_, Or.inl rfl⟩⟩
  · intro h; have := (G_hb_sb h).2.2; simp [G] at this
  · intro h; have := hb_lt G_wf h; omega

/-- No label uses the SC order. -/
def noSC : RC11.Label Bool ℕ → Prop
  | .R _ o _ | .W _ o _ => o ≠ .sc
  | .U _ or ow _ _ => or ≠ .sc ∧ ow ≠ .sc

theorem G_no_sc (e : ℕ) : noSC (G.lab e) := by
  simp only [G]; unfold lab; split <;> simp [noSC]

/-- In IMM, coherence fails. -/
theorem G_not_imm : ¬ (toIMM G).rc11_consistent := by
  rintro ⟨-, hcoh, -⟩
  have hw : ∀ e, e < 3 → G.IsWrite (.ev e) := by
    intro e he; refine ⟨by show e < 5; omega, ?_⟩
    interval_cases e <;> simp [G, lab, Label.IsWrite]
  have hsb01 : (toIMM G).sb (wrA G (.ev 0)) (wrA G (.ev 1)) :=
    sb_of_G (by simp [G, Exec.sb]) (E_wrA (by show _ < 5; omega)) (E_wrA (by show _ < 5; omega))
  have hsb12 : (toIMM G).sb (wrA G (.ev 1)) (wrA G (.ev 2)) :=
    sb_of_G (by simp [G, Exec.sb]) (E_wrA (by show _ < 5; omega)) (E_wrA (by show _ < 5; omega))
  have hsb34 : (toIMM G).sb (rdA G 3) (rdA G 4) :=
    sb_of_G (by simp [G, Exec.sb]) (E_rdA (by decide)) (E_rdA (by decide))
  have hrf23 : G.rfE (.ev 2) (.ev 3) := ⟨by decide, by simp [G, lab, Label.IsRead], by simp [G]⟩
  have hrf4 : G.rfE (.init false) (.ev 4) :=
    ⟨by decide, by simp [G, lab, Label.IsRead], by simp [G, lab, Label.loc]⟩
  have hrs : (toIMM G).rs (wrA G (.ev 1)) (wrA G (.ev 2)) := by
    refine ⟨_, ⟨rfl, W_wrA (hw 1 (by omega))⟩, _, Or.inr ⟨hsb12, ?_⟩, _,
      ⟨rfl, W_wrA (hw 2 (by omega))⟩, .refl⟩
    show loc _ _ = loc _ _
    rw [loc_wrA (hw 1 (by omega)), loc_wrA (hw 2 (by omega))]; rfl
  have hrel : (toIMM G).Rel (wrA G (.ev 1)) :=
    (rel_wrA (hw 1 (by omega))).2 ⟨by decide, by simp [G, lab, Label.RelW]⟩
  have hacq : (toIMM G).Acq (rdA G 3) :=
    (acq_rdA (by decide) (by simp [G, lab, Label.IsRead])).2
      ⟨by decide, by simp [G, lab, Label.AcqR]⟩
  have hsw : (toIMM G).sw (wrA G (.ev 1)) (rdA G 3) :=
    ⟨_, ⟨_, ⟨rfl, hrel⟩, _, Or.inl rfl, hrs⟩, _, ⟨_, _, hrf23, rfl, rfl⟩, _, Or.inl rfl, rfl, hacq⟩
  have h1 : Relation.TransGen ((toIMM G).sb ∪ᵣ (toIMM G).sw) (wrA G (.ev 0)) (rdA G 3) :=
    Relation.TransGen.tail (.single (Or.inl hsb01)) (Or.inr hsw)
  have hhb : (toIMM G).hb (wrA G (.ev 0)) (rdA G 4) := Relation.TransGen.tail h1 (Or.inl hsb34)
  have hmo : G.mo (.init false) (.ev 0) :=
    ⟨trivial, hw 0 (by omega), by simp [G, lab, Exec.loc, Label.loc], by simp [G, tsE]⟩
  have hfr : (toIMM G).fr (rdA G 4) (wrA G (.ev 0)) :=
    ⟨wrA G (.init false), ⟨_, _, hrf4, rfl, rfl⟩, ⟨_, _, hmo, rfl, rfl⟩⟩
  exact hcoh _ ⟨_, hhb, Or.inr (Or.inr ⟨_, hfr, Or.inl rfl⟩)⟩

/-- **The discipline cannot be dropped** from `rc11_of_consistent`: a
well-formed, consistent (and racy) graph without SC orders, whose location `x`
is accessed both atomically and non-atomically, and whose translation is not
`rc11_consistent`. -/
theorem consistent_not_imm :
    ∃ G : RC11.Exec prog (fun _ => 0) (fun _ => some 0),
      G.WF ∧ (∀ e, noSC (G.lab e)) ∧ G.Consistent ∧ G.Racy ∧ ¬ (toIMM G).rc11_consistent :=
  ⟨G, G_wf, G_no_sc, G_consistent, G_racy, G_not_imm⟩

end Counterexample

end IMM

end ORC11
