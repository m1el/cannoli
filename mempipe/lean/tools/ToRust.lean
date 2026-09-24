import Mempipe.Program

/-!
# Translating the verified programs to Rust

`lake env lean tools/ToRust.lean` regenerates `rust/src/generated.rs` from the
definitions the proofs are about: the program-counter types `SPc` and `RPc`
and the programs `sprog` and `rprog`. It does not parse the Lean source.
Instead, for every program-counter constructor it builds the local state
symbolically, unfolds the program and reduces the `match` on the program
counter, and prints the instruction it gets. Continuations are applied to
fresh variables and printed the same way. Anything outside the small fragment
the programs use is an error, so the output cannot silently drift from the
Lean definitions.

Loads and stores print as the Rust atomics of `mempipe/src/lib.rs` on a
mirror of `RawMemPipe` (`rust/src/lib.rs`). The model's integer values are
converted at the boundary: `client_owned` is `false`/`true` for `0`/`1`, and
`client_seq`'s `NO_SEQ = -1` is `u64::MAX`. The chunk is one value, read and
written through `unsafe` helpers. Ghost logs become pushes to a `log` vector.
-/

open Lean Meta

namespace ToRust

/-! ## Names and types -/

def camel (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toUpper :: cs)

def rustName (n : Name) : String :=
  let s := n.eraseMacroScopes.toString
  s.toLower

def rustTy (ty : Expr) : MetaM String := do
  let ty ← whnfR ty
  if ty.isConstOf ``Nat then return "usize"
  if ty.isConstOf ``Int then return "i64"
  if ty.isConstOf ``Bool then return "bool"
  throwError "ToRust: unsupported type {ty}"

/-! ## Expressions -/

/-- Normalize a term: beta, projections of constructors, `match` on
constructors; no unfolding of definitions, so `if`, arithmetic and
applications of parameters stay as they are. -/
partial def norm (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    -- structure projections of constructors, e.g. `{ pc := p, log := l }.log`
    if let .const c _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? c then
        if !info.fromClass then
          if let some e' ← unfoldDefinition? e then
            let e'' ← whnfCore e'
            if e'' != e' then return .done e''
    return .done (← whnfCore e))

def natLit? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?
  | _ => e.rawNatLit?

partial def expr (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if e.isFVar then return rustName (← e.fvarId!.getUserName)
  if let some n := natLit? e then return toString n
  match e.getAppFnArgs with
  | (``Neg.neg, #[_, _, a]) => return s!"-{← expr a}"
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return s!"({← expr a} + {← expr b})"
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return s!"({← expr a} - {← expr b})"
  | (``HMod.hMod, #[_, _, _, _, a, b]) => return s!"({← expr a} % {← expr b})"
  | (``Prod.mk, #[_, _, a, b]) => return s!"({← expr a}, {← exprTuple b})"
  | (``ite, #[_, c, _, a, b]) =>
    return s!"(if {← prop c} \{ {← expr a} } else \{ {← expr b} })"
  | (``Bool.true, #[]) => return "true"
  | (``Bool.false, #[]) => return "false"
  | (``Mempipe.NO_SEQ, #[]) => return "-1"
  | _ =>
    let f := e.getAppFn
    if f.isFVar then
      let args ← e.getAppArgs.mapM expr
      return s!"{← expr f}({", ".intercalate args.toList})"
    if let .const c _ := f then
      if let some info := (← getEnv).find? c |>.bind (fun | .ctorInfo i => some i | _ => none) then
        if info.induct == ``Mempipe.SPc || info.induct == ``Mempipe.RPc then
          return ← ctorExpr info e.getAppArgs
    throwError "ToRust: unsupported expression {e}"
where
  exprTuple (b : Expr) : MetaM String := do
    match b.getAppFnArgs with
    | (``Prod.mk, #[_, _, x, y]) => return s!"{← expr x}, {← exprTuple y}"
    | _ => expr b
  ctorExpr (info : ConstructorVal) (args : Array Expr) : MetaM String := do
    let ty := camel info.name.getString!
    let en := info.induct.getString!
    if args.isEmpty then return s!"{en}::{ty}"
    forallTelescope info.type fun xs _ => do
      let mut fs := #[]
      for x in xs, a in args do
        fs := fs.push s!"{rustName (← x.fvarId!.getUserName)}: {← expr a}"
      return s!"{en}::{ty} \{ {", ".intercalate fs.toList} }"
  prop (c : Expr) : MetaM String := do
    match c.getAppFnArgs with
    | (``Eq, #[ty, a, b]) =>
      if (← whnfR ty).isConstOf ``Bool && b.isConstOf ``Bool.true then expr a
      else return s!"{← expr a} == {← expr b}"
    | (``LT.lt, #[_, _, a, b]) => return s!"{← expr a} < {← expr b}"
    | (``LE.le, #[_, _, a, b]) => return s!"{← expr a} <= {← expr b}"
    | (``Not, #[p]) => return s!"!({← prop p})"
    | _ => throwError "ToRust: unsupported condition {c}"

/-! ## Memory accesses -/

def order (o : Expr) (kind : String) : MetaM String := do
  match o.constName? with
  | some ``ORC11.MemOrder.rlx => return "Ordering::Relaxed"
  | some ``ORC11.MemOrder.acqrel =>
    return match kind with
      | "load" => "Ordering::Acquire"
      | "store" => "Ordering::Release"
      | _ => "Ordering::AcqRel"
  | some ``ORC11.MemOrder.sc => return "Ordering::SeqCst"
  | _ => throwError "ToRust: unsupported order {o} for {kind}"

/-- The Rust place of an atomic location. -/
def place (l : Expr) : MetaM String := do
  match l.getAppFnArgs with
  | (``Mempipe.Loc.own, #[i]) => return s!"pipe.client_owned[{← expr i}]"
  | (``Mempipe.Loc.len, #[i]) => return s!"pipe.client_len[{← expr i}]"
  | (``Mempipe.Loc.cseq, #[i]) => return s!"pipe.client_seq[{← expr i}]"
  | (``Mempipe.Loc.curSeq, #[]) => return "pipe.cur_seq"
  | (``Mempipe.Loc.tick, #[]) => return "pipe.seq"
  | _ => throwError "ToRust: unsupported atomic location {l}"

/-- The value to store, converted from the model's integers. -/
def storeVal (l v : Expr) : MetaM String := do
  match l.getAppFnArgs with
  | (``Mempipe.Loc.own, _) =>
    match natLit? v with
    | some 0 => return "false"
    | some 1 => return "true"
    | _ => return s!"{← expr v} != 0"
  | (``Mempipe.Loc.len, _) => return s!"{← expr v} as usize"
  | _ => return s!"{← expr v} as u64"

def chunkIdx? (l : Expr) : Option Expr :=
  match l.getAppFnArgs with
  | (``Mempipe.Loc.chunk, #[i]) => some i
  | _ => none

/-! ## Statements -/

def ind (n : Nat) : String := "".pushn ' ' (4 * n)

/-- The binder name of a continuation, looking through the `match` on the
value read. -/
partial def contName (k : Expr) : MetaM Name := do
  match k with
  | .lam n _ b _ =>
    -- `fun x => match x with | none => … | some v => …`
    let alt := b.getAppArgs.back?
    match alt with
    | some (.lam m _ _ _) => if b.getAppFn.isConst then return m else return n
    | _ => return n
  | _ => return `v

/-- A binder name that does not clash, in Rust, with any variable in scope. -/
def fresh (n : Name) : MetaM Name := do
  let lctx ← getLCtx
  let taken (m : Name) := lctx.any fun d => rustName d.userName == rustName m
  if !taken n then return n
  let mut i := 2
  while taken (n.appendAfter (toString i)) do i := i + 1
  return n.appendAfter (toString i)

/-- Is this local state the fault state? -/
def isFault (σ : Expr) : Bool :=
  match σ.getAppFnArgs with
  | (_, #[pc, _]) => pc.isConstOf ``Mempipe.SPc.fault || pc.isConstOf ``Mempipe.RPc.fault
  | _ => false

mutual

/-- A new local state `mk pc log` of the thread whose old log is `log0`. -/
partial def stateStmts (log0 : Expr) (σ : Expr) (d : Nat) : MetaM String := do
  let σ ← norm σ
  match σ.getAppFnArgs with
  | (``ite, #[_, c, _, a, b]) =>
    return s!"{ind d}if {← expr.prop c} \{\n{← stateStmts log0 a (d+1)}{ind d}} else \{\n" ++
      s!"{← stateStmts log0 b (d+1)}{ind d}}\n"
  | (_, #[pc, log]) =>
    let pcS ← expr pc
    let pcStmt := if isFault σ then s!"{ind d}self.pc = {pcS};\n{ind d}return Status::Fault;\n"
      else s!"{ind d}self.pc = {pcS};\n"
    if log == log0 then return pcStmt
    match log.getAppFnArgs with
    | (``List.cons, #[_, e, rest]) =>
      if rest == log0 then return s!"{ind d}self.log.push({← expr e});\n" ++ pcStmt
      throwError "ToRust: unsupported log update {log}"
    | _ => throwError "ToRust: unsupported log update {log}"
  | _ => throwError "ToRust: unsupported local state {σ}"

/-- An instruction. -/
partial def instr (log0 : Expr) (i : Expr) (d : Nat) : MetaM String := do
  let i ← norm i
  match i.getAppFnArgs with
  | (``ite, #[_, c, _, a, b]) =>
    return s!"{ind d}if {← expr.prop c} \{\n{← instr log0 a (d+1)}{ind d}} else \{\n" ++
      s!"{← instr log0 b (d+1)}{ind d}}\n"
  | (``ORC11.Instr.read, #[_, _, _, l, o, k]) =>
    let n ← fresh (← contName k)
    withLocalDeclD n (mkConst ``Int) fun v => do
      let some' ← stateStmts log0 (mkApp k (← mkAppM ``Option.some #[v])) (d+1)
      let none' ← norm (mkApp k (← mkAppOptM ``Option.none #[mkConst ``Int]))
      let x := rustName n
      if let some ci := chunkIdx? l then
        unless o.isConstOf ``ORC11.MemOrder.na do throwError "ToRust: atomic chunk access"
        return s!"{ind d}match unsafe \{ pipe.read_chunk({← expr ci}) } \{\n" ++
          s!"{ind (d+1)}// uninitialized\n{ind (d+1)}None => \{\n" ++
          s!"{← stateStmts log0 none' (d+2)}{ind (d+1)}}\n" ++
          s!"{ind (d+1)}Some({x}) => \{\n{← stateStmts log0 (mkApp k (← mkAppM ``Option.some #[v])) (d+2)}" ++
          s!"{ind (d+1)}}\n{ind d}}\n"
      -- atomic locations are always initialized: the `none` branch is dead
      unless isFault none' do throwError "ToRust: live uninitialized branch {none'}"
      return s!"{ind d}let {x} = {← place l}.load({← order o "load"}) as i64;\n" ++
        (some'.replace s!"{ind (d+1)}" (ind d))
  | (``ORC11.Instr.write, #[_, _, _, l, o, v, k]) =>
    let acc ← if let some ci := chunkIdx? l then
        pure s!"unsafe \{ pipe.write_chunk({← expr ci}, {← expr v}) }"
      else pure s!"{← place l}.store({← storeVal l v}, {← order o "store"})"
    return s!"{ind d}{acc};\n{← stateStmts log0 k d}"
  | (``ORC11.Instr.update, #[_, _, _, l, or, ow, f, k]) =>
    -- only `fetch_add(1)` with matching orders
    let one ← lambdaTelescope f fun xs b => do
      match b.getAppFnArgs with
      | (``HAdd.hAdd, #[_, _, _, _, x, c]) => return xs.size == 1 && x == xs[0]! && natLit? c == some 1
      | _ => return false
    unless one do throwError "ToRust: unsupported update {f}"
    unless or == ow do throwError "ToRust: mixed update orders"
    let n ← fresh (← contName k)
    withLocalDeclD n (mkConst ``Int) fun v => do
      return s!"{ind d}let {rustName n} = {← place l}.fetch_add(1, {← order or "rmw"}) as i64;\n" ++
        (← stateStmts log0 (mkApp k v) d)
  | (``ORC11.Instr.choose, #[_, _, _, k]) =>
    let n ← fresh (← contName k)
    withLocalDeclD n (mkConst ``Bool) fun b => do
      return s!"{ind d}let {rustName n} = choose();\n{← stateStmts log0 (mkApp k b) d}"
  | (``ORC11.Instr.halt, _) => return s!"{ind d}return Status::Halted;\n"
  | (``ORC11.Instr.fault, _) => return s!"{ind d}return Status::Fault;\n"
  | _ => throwError "ToRust: unsupported instruction {i}"

end

/-! ## Types and step functions -/

def docLines (n : Name) (d : Nat) : MetaM String := do
  match ← findDocString? (← getEnv) n with
  | none => return ""
  | some s =>
    return String.join (s.trim.splitOn "\n" |>.map fun l => s!"{ind d}/// {l.trim}\n")

/-- `enum` for a program-counter type. -/
def pcEnum (T : Name) : MetaM String := do
  let .inductInfo info ← getConstInfo T | throwError "not an inductive"
  let mut out := s!"{← docLines T 0}#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum {T.getString!} \{\n"
  for c in info.ctors do
    let ci ← getConstInfoCtor c
    out := out ++ (← docLines c 1)
    let fields ← forallTelescope ci.type fun xs _ => xs.mapM fun x => do
      return s!"{rustName (← x.fvarId!.getUserName)}: {← rustTy (← inferType x)}"
    out := out ++ if fields.isEmpty then s!"{ind 1}{camel c.getString!},\n"
      else s!"{ind 1}{camel c.getString!} \{ {", ".intercalate fields.toList} },\n"
  return out ++ "}\n"

/-- The step function of program `prog : params → State → Instr`, one arm per
program-counter constructor. -/
def stepFn (prog : Name) (state : Name) (T : Name) (params : List (String × String)) :
    MetaM String := do
  let .inductInfo info ← getConstInfo T | throwError "not an inductive"
  let pinfo ← getConstInfo prog
  -- the parameter types (closed), rebound below under their Rust names
  let tys ← forallTelescope pinfo.type fun ps0 _ => ps0.pop.mapM inferType
  withLocalDeclsDND ((params.toArray.zip tys).map fun ((n, _), t) => (Name.mkSimple n, t))
    fun ps => do
    withLocalDeclD `log (← mkAppM ``List #[mkConst ``Mempipe.Entry]) fun log0 => do
      let mut arms := ""
      for c in info.ctors do
        let ci ← getConstInfoCtor c
        let arm ← forallTelescope ci.type fun xs _ => do
          let σ := mkApp2 (mkConst (state ++ `mk)) (mkAppN (mkConst c) xs) log0
          let some e ← unfoldDefinition? (mkAppN (mkConst prog) (ps.push σ))
            | throwError "cannot unfold {prog}"
          let names ← xs.mapM fun x => return rustName (← x.fvarId!.getUserName)
          let pat := if xs.isEmpty then s!"{T.getString!}::{camel c.getString!}"
            else s!"{T.getString!}::{camel c.getString!} \{ {", ".intercalate names.toList} }"
          return s!"{ind 3}{pat} => \{\n{← instr log0 (← whnfCore e) 4}{ind 3}}\n"
        arms := arms ++ arm
      let sig := ", ".intercalate (params.map fun (n, t) => s!"{n}: {t}")
      return s!"{ind 1}/// One step of `{prog}`.\n" ++
        s!"{ind 1}#[allow(unused_variables, unused_parens, unreachable_code, clippy::all)]\n" ++
        s!"{ind 1}pub fn step(&mut self, pipe: &Pipe, {sig}, choose: &mut dyn FnMut() -> bool) -> Status \{\n" ++
        s!"{ind 2}let pc = self.pc;\n{ind 2}match pc \{\n{arms}{ind 2}}\n{ind 2}Status::Running\n{ind 1}}\n"

def generate : MetaM String := do
  let header := "// @generated by `lake env lean tools/ToRust.lean` from\n" ++
    "// `Mempipe/Program.lean` (`SPc`, `sprog`, `RPc`, `rprog`). Do not edit.\n\n" ++
    "use core::sync::atomic::Ordering;\n\nuse crate::{Pipe, Status};\n\n"
  let sEnum ← pcEnum ``Mempipe.SPc
  let rEnum ← pcEnum ``Mempipe.RPc
  let sStep ← stepFn ``Mempipe.sprog ``Mempipe.SState ``Mempipe.SPc
    [("num_buffers", "usize"), ("num_messages", "usize"), ("pay", "&dyn Fn(usize) -> i64"),
     ("ln", "&dyn Fn(usize) -> i64")]
  let rStep ← stepFn ``Mempipe.rprog ``Mempipe.RState ``Mempipe.RPc [("num_buffers", "usize")]
  return header ++ sEnum ++ "\n" ++ rEnum ++ "\n" ++
    "/// The sender: `SendPipe::alloc_buffer` and `ChunkWriter`.\n" ++
    "#[derive(Clone, Debug)]\npub struct Sender {\n    pub pc: SPc,\n" ++
    "    /// Ghost: `(seq, payload, len)` of each published buffer.\n" ++
    "    pub log: Vec<(i64, i64, i64)>,\n}\n\nimpl Sender {\n" ++ sStep ++ "}\n\n" ++
    "/// A receiver: `RecvPipe::request_ticket` and `RecvPipe::try_recv`.\n" ++
    "#[derive(Clone, Debug)]\npub struct Receiver {\n    pub pc: RPc,\n" ++
    "    /// Ghost: `(ticket, payload, len)` of each accepted buffer.\n" ++
    "    pub log: Vec<(i64, i64, i64)>,\n}\n\nimpl Receiver {\n" ++ rStep ++ "}\n"

end ToRust

#eval show MetaM Unit from do
  let s ← ToRust.generate
  IO.FS.writeFile "rust/src/generated.rs" s
  IO.println s!"wrote rust/src/generated.rs ({s.length} bytes)"
