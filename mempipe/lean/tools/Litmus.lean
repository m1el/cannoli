import ORC11.RC11Dec
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Permutation

/-!
# Litmus tests for the RC11 definitions

`lake env lean --run tools/Litmus.lean <dir>` writes each test below as a C
litmus file `<dir>/<name>.litmus` for herd7, and prints what `RC11.lean` says
about it: every consistent execution graph, with its final registers and
memory and whether it is racy. `scripts/litmus.sh` runs herd7 with `rc11.cat`
on the same files and compares.

The executions are enumerated here, but their consistency and races are
decided by `decConsistent` and `decRacy`, the proved decisions of
`Exec.Consistent` and `Exec.Racy`. A test is straight-line code. The
enumeration picks a source for every read and a modification order for every
location, and discards choices where `sb ∪ rf` is cyclic, since RC11 forbids
those (NO-THIN-AIR). The events are then numbered along a topological order
of `sb ∪ rf`.
-/

open ORC11 ORC11.RC11

namespace Litmus

/-- Instructions: loads, stores, fetch-and-add and exchange. The value read
goes to the thread's next register. -/
inductive Op (L : Type) where
  | ld (x : L) (o : MemOrder)
  | st (x : L) (o : MemOrder) (v : ℤ)
  | faa (x : L) (or ow : MemOrder) (d : ℤ)
  | xchg (x : L) (or ow : MemOrder) (v : ℤ)

instance {L : Type} [Inhabited L] : Inhabited (Op L) := ⟨.ld default .na⟩

structure Test where
  name : String
  nlocs : ℕ
  threads : List (List (Op (Fin nlocs)))

namespace Op

variable {L : Type}

def loc : Op L → L
  | ld x _ | st x _ _ | faa x _ _ _ | xchg x _ _ _ => x

def isRead : Op L → Bool
  | st .. => false
  | _ => true

def isWrite : Op L → Bool
  | ld .. => false
  | _ => true

/-- The value written, from the value read. -/
def map {L' : Type} (f : L → L') : Op L → Op L'
  | ld x o => ld (f x) o
  | st x o v => st (f x) o v
  | faa x or ow d => faa (f x) or ow d
  | xchg x or ow v => xchg (f x) or ow v

def wval : Op L → ℤ → ℤ
  | st _ _ v, _ => v
  | faa _ _ _ d, r => r + d
  | xchg _ _ _ v, _ => v
  | ld .., r => r

end Op

/-- Thread states: the program counter and the registers, newest first. -/
abbrev St := ℕ × List (Option ℤ)

variable (T : Test)

namespace Test

abbrev Loc := Fin T.nlocs
abbrev Tid := Fin T.threads.length

def ops (i : Tid T) : List (Op (Loc T)) := T.threads[i]

/-- The program of each thread. -/
def prog (i : Tid T) (s : St) : Instr (Loc T) ℤ St :=
  match (T.ops i)[s.1]? with
  | none => .halt
  | some (.ld x o) => .read x o fun v => (s.1 + 1, v :: s.2)
  | some (.st x o v) => .write x o v (s.1 + 1, s.2)
  | some (.faa x or ow d) => .update x or ow (· + d) fun v => (s.1 + 1, some v :: s.2)
  | some (.xchg x or ow v) => .update x or ow (fun _ => v) fun r => (s.1 + 1, some r :: s.2)

def s0 : Tid T → St := fun _ => (0, [])

/-- Litmus locations start at `0`. -/
def v0 : Loc T → Option ℤ := fun _ => some 0

abbrev G := Exec (S := fun _ => St) (prog T) (s0 T) (v0 T)

/-- The static events: a thread and the index of an instruction. -/
def sevs : Array (ℕ × Op ℕ) :=
  (List.finRange T.threads.length).foldl
    (fun acc i => acc ++ ((T.ops i).map fun o => (i.val, o.map Fin.val)).toArray) #[]

/-- A candidate: a source for every read (`none` for the initialization)
and a rank in the modification order for every write. -/
structure Cand where
  rf : Array (Option ℕ)
  rank : Array ℕ

/-- All lists picking one element of each list. -/
def choices {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (choices xss).map (x :: ·)

def cands : List (Cand) :=
  let ev := T.sevs
  let m := ev.size
  let idx := List.range m
  -- sources for each event (reads only)
  let srcs : List (List (Option ℕ)) := idx.map fun r =>
    if (ev[r]!).2.isRead then
      none :: (idx.filter fun w => w != r && (ev[w]!).2.isWrite &&
        (ev[w]!).2.loc == (ev[r]!).2.loc).map some
    else [none]
  -- modification orders for each location
  let mos : List (List (List ℕ)) := (List.finRange T.nlocs).map fun l =>
    (idx.filter fun w => (ev[w]!).2.isWrite && (ev[w]!).2.loc == l.val).permutations
  (choices srcs).flatMap fun rf => (choices mos).map fun mo =>
    let rank := idx.map fun w =>
      (mo.findSome? fun ord => ord.idxOf? w).getD 0
    ⟨rf.toArray, rank.toArray⟩

/-- A topological order of `sb ∪ rf`, if it is acyclic. -/
def topo (c : Cand) : Option (List ℕ) := Id.run do
  let ev := T.sevs
  let m := ev.size
  let preds : ℕ → List ℕ := fun e =>
    let sbp := if e > 0 && (ev[e - 1]!).1 == (ev[e]!).1 then [e - 1] else []
    sbp ++ (c.rf[e]!).toList
  let mut placed : List ℕ := []
  for _ in [0:m] do
    match (List.range m).find? fun e => !placed.contains e && (preds e).all placed.contains with
    | some e => placed := placed ++ [e]
    | none => return none
  return some placed

def label (dl : Loc T) (o : Op ℕ) (r : ℤ) : Label (Loc T) ℤ :=
  let loc : ℕ → Loc T := fun x => if h : x < T.nlocs then ⟨x, h⟩ else dl
  match o.map loc with
  | .ld x mo => .R x mo (some r)
  | .st x mo v => .W x mo v
  | .faa x or ow d => .U x or ow r (r + d)
  | .xchg x or ow v => .U x or ow r v

/-- The graph of a candidate, numbered along `order`. -/
def mkExec (c : Cand) (order : List ℕ) (dt : Tid T) (dl : Loc T) : Option (G T) := Id.run do
  let ev := T.sevs
  let m := ev.size
  -- values read, in the topological order
  let mut rv : Array ℤ := Array.replicate m 0
  for e in order do
    let r := match c.rf[e]! with
      | none => 0
      | some w => (ev[w]!).2.wval rv[w]!
    rv := rv.set! e r
  let pos : ℕ → ℕ := fun s => order.idxOf s
  let st : ℕ → ℕ := fun e => order.getD e 0
  let tid : ℕ → Tid T := fun e =>
    let t := (ev[st e]!).1
    if h : e < m ∧ t < T.threads.length then ⟨t, h.2⟩ else dt
  let lab : ℕ → Label (Loc T) ℤ := fun e =>
    if e < m then label T dl (ev[st e]!).2 rv[st e]! else .R dl .na none
  let rf : ℕ → Option ℕ := fun e => if e < m then (c.rf[st e]!).map pos else none
  let ts : ℕ → ℕ := fun e =>
    if e < m ∧ (ev[st e]!).2.isWrite then 2 + c.rank[st e]! else 0
  let items : Tid T → List Item := fun i => ((List.range m).filter (tid · = i)).map .inl
  if hrun : ∀ i, (runItems (prog T i) lab (s0 T i) (items i)).isSome then
    return some
      { n := m, tid, lab, rf, ts, active := Finset.univ, items
        final := fun i => (runItems (prog T i) lab (s0 T i) (items i)).get (hrun i)
        run := fun i => by simp
        inactive := fun i hi => absurd (Finset.mem_univ i) hi
        itemsEv := fun i => by
          simp only [items, List.filterMap_map]
          exact List.filterMap_some }
  else return none

def locName (l : ℕ) : String := ["x", "y", "z", "w"].getD l s!"v{l}"

/-- A consistent execution: its final state, sorted, and whether it races. -/
def outcome (g : G T) (c : Cand) (order : List ℕ) : String := Id.run do
  let ev := T.sevs
  let mut out : List String := []
  for i in List.finRange T.threads.length do
    let regs := (g.final i).2.reverse
    for (v, k) in regs.zipIdx do
      out := out ++ [s!"{i.val}:r{k}={v.getD 0}"]
  for l in List.finRange T.nlocs do
    -- the value of the last write in the modification order
    let ws := (List.range ev.size).filter fun w => (ev[w]!).2.isWrite && (ev[w]!).2.loc == l.val
    let last := ws.foldl (fun acc w => match acc with
      | none => some w
      | some a => if c.rank[w]! > c.rank[a]! then some w else some a) none
    let v : ℤ := match last with
      | none => 0
      | some w => ((g.lab (order.idxOf w)).wval).getD 0
    out := out ++ [s!"{locName l}={v}"]
  return String.intercalate " " out

theorem hlocs : ∀ l : Loc T, l ∈ List.finRange T.nlocs := List.mem_finRange

/-- Run a test: the number of candidates, and the consistent executions with
their outcomes and race flags. -/
def run : IO Unit := do
  if h : 0 < T.threads.length ∧ 0 < T.nlocs then
    let dt : Tid T := ⟨0, h.1⟩
    let dl : Loc T := ⟨0, h.2⟩
    let mut ncand := 0
    let mut ncons := 0
    let mut lines : List String := []
    for c in T.cands do
      ncand := ncand + 1
      let some order := T.topo c | continue
      let some g := T.mkExec c order dt dl | throw (IO.userError s!"{T.name}: run failed")
      if hwf : g.WF then
        let cons := @decide _ (Exec.decConsistent (G := g) (hlocs T))
        if cons then
          ncons := ncons + 1
          let racy := @decide _ (Exec.decRacy (G := g) (hlocs T) hwf)
          lines := lines ++ [s!"exec {T.outcome g c order} racy={racy}"]
      else throw (IO.userError s!"{T.name}: ill-formed graph")
    IO.println s!"test {T.name} candidates={ncand} consistent={ncons}"
    for l in lines do IO.println l
  else throw (IO.userError s!"{T.name}: empty test")

/-! ## herd7 litmus files -/

def cOrd : MemOrder → String
  | .na => "memory_order_relaxed"
  | .rlx => "memory_order_relaxed"
  | .acqrel => "memory_order_acq_rel"
  | .sc => "memory_order_seq_cst"

def rmwOrd : MemOrder → MemOrder → String
  | .rlx, .rlx => "memory_order_relaxed"
  | .acqrel, .rlx => "memory_order_acquire"
  | .rlx, .acqrel => "memory_order_release"
  | .acqrel, .acqrel => "memory_order_acq_rel"
  | _, _ => "memory_order_seq_cst"

def cOp (k : ℕ) : Op (Loc T) → String × ℕ
  | .ld x .na => (s!"int r{k} = *{locName x};", k + 1)
  | .ld x .acqrel => (s!"int r{k} = atomic_load_explicit({locName x}, memory_order_acquire);", k + 1)
  | .ld x o => (s!"int r{k} = atomic_load_explicit({locName x}, {cOrd o});", k + 1)
  | .st x .na v => (s!"*{locName x} = {v};", k)
  | .st x .acqrel v => (s!"atomic_store_explicit({locName x}, {v}, memory_order_release);", k)
  | .st x o v => (s!"atomic_store_explicit({locName x}, {v}, {cOrd o});", k)
  | .faa x or ow d =>
    (s!"int r{k} = atomic_fetch_add_explicit({locName x}, {d}, {rmwOrd or ow});", k + 1)
  | .xchg x or ow v =>
    (s!"int r{k} = atomic_exchange_explicit({locName x}, {v}, {rmwOrd or ow});", k + 1)

def litmus : String := Id.run do
  let locs := (List.range T.nlocs).map locName
  let params := String.intercalate ", " (locs.map (s!"atomic_int* {·}"))
  let mut out := s!"C {T.name}\n\n\{}\n\n"
  let mut regs : List String := []
  for (th, i) in T.threads.zipIdx do
    out := out ++ s!"P{i}({params}) \{\n"
    let mut k := 0
    for o in th do
      let (line, k') := cOp T k o
      out := out ++ s!"  {line}\n"
      if k' > k then regs := regs ++ [s!"{i}:r{k}"]
      k := k'
    out := out ++ "}\n\n"
  let obs := regs ++ locs
  out := out ++ s!"locations [{String.intercalate "; " obs};]\n"
  out := out ++ s!"exists ({locs.head!}=0 \\/ ~{locs.head!}=0)\n"
  return out

end Test

end Litmus

/-! ## The tests

Locations `0, 1, 2` are `x, y, z`. `acqrel` is acquire on loads, release on
stores, and on updates read and write orders are separate. -/

namespace Litmus

open Op MemOrder

def tests : List Test := [
  -- message passing
  ⟨"MP+na+rel+acq", 2, [[st 0 na 1, st 1 acqrel 1], [ld 1 acqrel, ld 0 na]]⟩,
  ⟨"MP+na+rlx", 2, [[st 0 na 1, st 1 rlx 1], [ld 1 rlx, ld 0 na]]⟩,
  ⟨"MP+na+rel+rlx", 2, [[st 0 na 1, st 1 acqrel 1], [ld 1 rlx, ld 0 na]]⟩,
  ⟨"MP+na+rlx+acq", 2, [[st 0 na 1, st 1 rlx 1], [ld 1 acqrel, ld 0 na]]⟩,
  ⟨"MP+rlx", 2, [[st 0 rlx 1, st 1 rlx 1], [ld 1 rlx, ld 0 rlx]]⟩,
  ⟨"MP+rel+acq", 2, [[st 0 rlx 1, st 1 acqrel 1], [ld 1 acqrel, ld 0 rlx]]⟩,
  -- store buffering, load buffering
  ⟨"SB+rlx", 2, [[st 0 rlx 1, ld 1 rlx], [st 1 rlx 1, ld 0 rlx]]⟩,
  ⟨"SB+rel+acq", 2, [[st 0 acqrel 1, ld 1 acqrel], [st 1 acqrel 1, ld 0 acqrel]]⟩,
  ⟨"LB+rlx", 2, [[ld 0 rlx, st 1 rlx 1], [ld 1 rlx, st 0 rlx 1]]⟩,
  ⟨"LB+na", 2, [[ld 0 na, st 1 na 1], [ld 1 na, st 0 na 1]]⟩,
  -- coherence
  ⟨"2+2W+rlx", 2, [[st 0 rlx 1, st 1 rlx 2], [st 1 rlx 1, st 0 rlx 2]]⟩,
  ⟨"CoRR", 1, [[st 0 rlx 1], [st 0 rlx 2], [ld 0 rlx, ld 0 rlx]]⟩,
  ⟨"CoWR", 1, [[st 0 rlx 1, ld 0 rlx], [st 0 rlx 2]]⟩,
  ⟨"CoRW", 1, [[ld 0 rlx, st 0 rlx 2], [st 0 rlx 1]]⟩,
  ⟨"R+rel+acq", 2, [[st 0 rlx 1, st 1 acqrel 1], [st 1 rlx 2, ld 0 acqrel]]⟩,
  ⟨"S+rel+acq", 2, [[st 0 rlx 2, st 1 acqrel 1], [ld 1 acqrel, st 0 rlx 1]]⟩,
  -- causality
  ⟨"WRC+rel+acq", 3, [[st 0 rlx 1], [ld 0 acqrel, st 1 acqrel 1], [ld 1 acqrel, ld 0 rlx]]⟩,
  ⟨"WRC+rlx", 3, [[st 0 rlx 1], [ld 0 rlx, st 1 rlx 1], [ld 1 rlx, ld 0 rlx]]⟩,
  ⟨"IRIW+acq", 2, [[st 0 acqrel 1], [st 1 acqrel 1], [ld 0 acqrel, ld 1 acqrel],
    [ld 1 acqrel, ld 0 acqrel]]⟩,
  ⟨"ISA2+na", 3, [[st 0 na 1, st 1 acqrel 1], [ld 1 acqrel, st 2 acqrel 1],
    [ld 2 acqrel, ld 0 na]]⟩,
  -- read-modify-writes
  ⟨"FAA+FAA", 1, [[faa 0 rlx rlx 1], [faa 0 rlx rlx 1]]⟩,
  ⟨"FAA+ST", 1, [[faa 0 rlx rlx 1], [st 0 rlx 5], [ld 0 rlx, ld 0 rlx]]⟩,
  ⟨"XCHG+XCHG", 1, [[xchg 0 acqrel acqrel 1], [xchg 0 acqrel acqrel 2]]⟩,
  ⟨"FAA+na", 1, [[faa 0 rlx rlx 1], [st 0 na 3]]⟩,
  ⟨"FAA+rel+acq", 2, [[st 0 na 1, faa 1 rlx acqrel 1], [faa 1 acqrel rlx 1, ld 0 na]]⟩,
  -- release sequences
  ⟨"RS+rmw", 2, [[st 0 na 1, st 1 acqrel 1], [faa 1 rlx rlx 1], [ld 1 acqrel, ld 0 na]]⟩,
  ⟨"RS+rmw2", 2, [[st 0 na 1, st 1 acqrel 1], [faa 1 rlx rlx 1], [xchg 1 rlx rlx 7],
    [ld 1 acqrel, ld 0 na]]⟩,
  ⟨"RS+sb", 2, [[st 0 na 1, st 1 acqrel 1, st 1 rlx 2], [ld 1 acqrel, ld 0 na]]⟩,
  ⟨"RS+sb+na", 2, [[st 0 na 1, st 1 acqrel 1, st 1 na 2], [ld 1 acqrel, ld 0 na]]⟩,
  ⟨"RS+st", 2, [[st 0 na 1, st 1 acqrel 1], [st 1 rlx 2], [ld 1 acqrel, ld 0 na]]⟩,
  ⟨"RS+sb+rmw", 2, [[st 0 na 1, st 1 acqrel 1, st 1 rlx 2], [faa 1 rlx rlx 1],
    [ld 1 acqrel, ld 0 na]]⟩,
  -- races
  ⟨"Race+na", 1, [[st 0 na 1], [ld 0 na]]⟩,
  ⟨"Race+ww", 1, [[st 0 na 1], [st 0 na 2]]⟩,
  ⟨"Race+rlx+na", 1, [[st 0 rlx 1], [ld 0 na]]⟩,
  ⟨"NoRace+rr", 1, [[ld 0 na], [ld 0 na]]⟩,
  ⟨"NoRace+rlx", 1, [[st 0 rlx 1], [ld 0 rlx]]⟩,
  ⟨"Race+sb+na", 1, [[st 0 na 1, ld 0 rlx], [st 0 rlx 2]]⟩,
  ⟨"Race+init", 1, [[ld 0 na], [st 0 rlx 2]]⟩
]

def main (args : List String) : IO Unit := do
  let dir := args.headD "litmus"
  IO.FS.createDirAll dir
  for t in tests do
    IO.FS.writeFile s!"{dir}/{t.name}.litmus" t.litmus
    t.run

end Litmus

def main (args : List String) : IO Unit := Litmus.main args
