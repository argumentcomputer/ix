/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.CheckIxeStep

/-! # The pin table, the Ixon prelude and the Nat-operation pins, from Ixon (untrusted)

Generates `Ix/Kernel/Ixon/PinData.lean` (the pin table and the prelude)
and `Ix/Kernel/Ixon/NatOpPinData.lean` (the pin variant of the eight
pin-certified `Nat` operations) from two compiled `.ixe` files: the compiled
Init (`.lake/envs/initstd.ixe`) and `Ix/Kernel/PinGen/Certs.lean` compiled
by the Ix compiler (`regenerate` below gives the commands). No JSON is read,
and none is generated: the optional closure rows are the environment check's JSONL
report rows.

1. **The names.** The checker's pinned names, and only those: the basis
   (`reservedBasisNames`), the prelude's `And` and `Bool`, the structural and
   pin-certified Nat operations, the string-literal support, the standard and
   compiler-trust axioms (with `Iff`, `Nonempty`, `True`), `sorryAx`.
   Recursor names (`T.rec`, `T.rec_k`) are not pinned: the reader derives
   them.
2. **Candidates.** Each name is looked up in the environment's `named`
   metadata (this host tool is the only place metadata is read), and its
   address resolved to a `ConstRef Address` exactly as the reader resolves
   references.
3. **The Nat-operation pins** (upstream con-leche's generator
   `PinGen.lean`, not vendored, over Ixon):
   - **the pins** are the operations' stored values, as the reader reads them
     from the compiled Init (in the dependency order the environment check uses). Ixon
     names a constant by its content, so the pin table's address for
     `Nat.div` already fixes `Nat.div`'s helpers: upstream's helper
     unfolding, which keeps a pin stable when an export renames a helper,
     has nothing to do here;
   - **the certificate proofs** are the values of the theorems of
     `Ix/Kernel/PinGen/Certs.lean` (`certSpecs`), compiled by the Ix compiler
     and read by the same reader, closed by upstream's rule
     (`inlineCertClosure`): every constant outside the operation's dependency
     cone (the declarations of the records its record reaches), its
     certificate ground (`natOpDeps`) and the statements' machinery
     (`stmtNames`) is replaced by its value, with beta, `let` and
     projection-of-constructor reduction, to a fixpoint; a residual outside
     those sets fails the run. Upstream also force-inlines equation-compiler
     internals inside the cone, because a lean4export stream need not
     declare them; an Ixon stream that declares the operation declares its
     whole reference closure, so nothing is forced here;
   - the two compiles must agree: each operation's address in the
     certificates' `.ixe` is its address in the Init `.ixe`.
4. **Verification by the verified fold.** The prelude records are read under the
   candidate table, and the dependency closure of every pinned constant is
   read and checked record by record (`CheckIxeStep.checkLoop`, the environment check's
   own step) with the generated pin variant. The run fails unless every
   pinned constant's record is accepted (a basis block matches its pin up to
   `canon`, the literal-support constants have their exact types, the
   structural Nat operations are certified by their recurrences and the
   pin-certified ones by these pins and certificates), both literal
   capabilities hold in the final environment, and every recursor the
   prelude names gets its derived name.
5. **Output.** `PinData.lean`: the table, sorted by name, the level names,
   and the prelude's records (the twelve declarations of the checker's
   prelude, with their projection and recursor records) as canonical bytes.
   `NatOpPinData.lean`: the pin variant as a share table (the format is in
   `Ix/Kernel/Ixon/Prelude.lean`), decoded by the committed decoder and
   compared with the generated variant before it is written.

Usage: `kernel-pin-gen <init.ixe> <certs.ixe> <PinData.lean> <NatOpPinData.lean> [closure.jsonl]`. -/

namespace Benchmarks.Kernel.PinGen

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep

def fixedNames : List CName :=
  Ix.Kernel.reservedBasisNames ++
  [Ix.Kernel.andName, Ix.Kernel.andIntroName, Ix.Kernel.boolName, Ix.Kernel.boolFalseName,
   Ix.Kernel.boolTrueName] ++
  Ix.Kernel.natOpNames ++ Ix.Kernel.natDivModNames ++
  [Ix.Kernel.stringName, Ix.Kernel.stringOfListName, Ix.Kernel.listName, Ix.Kernel.listNilName,
   Ix.Kernel.listConsName, Ix.Kernel.charName, Ix.Kernel.charOfNatName] ++
  [Ix.Kernel.propextName, Ix.Kernel.choiceName, Ix.Kernel.iffName, Ix.Kernel.iffIntroName,
   Ix.Kernel.nonemptyName, Ix.Kernel.nonemptyIntroName] ++
  [Ix.Kernel.trueName, Ix.Kernel.trueIntroName, Ix.Kernel.trustCompilerName,
   Ix.Kernel.reduceNatName, Ix.Kernel.reduceBoolName, Ix.Kernel.ofReduceNatName,
   Ix.Kernel.ofReduceBoolName, Ix.Kernel.sorryAxName]

/-- The prelude's declarations, in upstream con-leche's prelude order
(its `pins/<toolchain>.prelude.ndjson`): each group's names. -/
def preludeGroups : List (List CName) :=
  [[Ix.Kernel.eqName, Ix.Kernel.eqReflName, Ix.Kernel.eqName.str "rec"],
   [Ix.Kernel.natName, Ix.Kernel.natZeroName, Ix.Kernel.natSuccName, Ix.Kernel.natName.str "rec"],
   [Ix.Kernel.punitName, Ix.Kernel.punitUnitName, Ix.Kernel.punitRecName],
   [Ix.Kernel.emptyName, Ix.Kernel.emptyName.str "rec"],
   [Ix.Kernel.falseName, Ix.Kernel.falseName.str "rec"],
   [Ix.Kernel.quotName], [Ix.Kernel.quotMkName], [Ix.Kernel.quotLiftName], [Ix.Kernel.quotIndName],
   [Ix.Kernel.quotSoundName],
   [Ix.Kernel.andName, Ix.Kernel.andIntroName, Ix.Kernel.andName.str "rec"],
   [Ix.Kernel.boolName, Ix.Kernel.boolFalseName, Ix.Kernel.boolTrueName, Ix.Kernel.boolName.str "rec"]]

/-- Per pin-certified operation, in `NatOpPinSet` field order, the theorems
of `Ix/Kernel/PinGen/Certs.lean` that certify it, in the order of its pinned
statements (`Ix.Kernel.divModCertStmts`), as in upstream's `opSpecs`. -/
def certSpecs : List (CName × List Lean.Name) :=
  [(Ix.Kernel.natDivName, [`Ix.Kernel.PinGen.divRecCert, `Ix.Kernel.PinGen.divBaseGtCert,
     `Ix.Kernel.PinGen.divBaseZeroCert]),
   (Ix.Kernel.natModName, [`Ix.Kernel.PinGen.modRecCert, `Ix.Kernel.PinGen.modBaseGtCert,
     `Ix.Kernel.PinGen.modBaseZeroCert]),
   (Ix.Kernel.natGcdName, [`Ix.Kernel.PinGen.gcdRecCert, `Ix.Kernel.PinGen.gcdBaseCert]),
   (Ix.Kernel.natLandName, [`Ix.Kernel.PinGen.landRecCert, `Ix.Kernel.PinGen.landBaseCert]),
   (Ix.Kernel.natLorName, [`Ix.Kernel.PinGen.lorRecCert, `Ix.Kernel.PinGen.lorBaseCert]),
   (Ix.Kernel.natXorName, [`Ix.Kernel.PinGen.xorRecCert, `Ix.Kernel.PinGen.xorBaseCert]),
   (Ix.Kernel.natShiftLeftName, [`Ix.Kernel.PinGen.shiftLeftRecCert,
     `Ix.Kernel.PinGen.shiftLeftBaseCert]),
   (Ix.Kernel.natShiftRightName, [`Ix.Kernel.PinGen.shiftRightRecCert,
     `Ix.Kernel.PinGen.shiftRightBaseCert])]

/-- The certificate statements' machinery (upstream's `stmtMachineryNames`):
every certificate install requires these stored, so a proof may keep them. -/
def stmtNames : List CName :=
  [Ix.Kernel.natName, Ix.Kernel.natZeroName, Ix.Kernel.natSuccName, Ix.Kernel.natName.str "rec",
   Ix.Kernel.boolName, Ix.Kernel.boolTrueName, Ix.Kernel.boolFalseName, Ix.Kernel.boolName.str "rec",
   Ix.Kernel.eqName, Ix.Kernel.eqReflName, Ix.Kernel.eqName.str "rec"]

/-- The commands that regenerate both files, written into their headers. -/
def regenerate : List String :=
  ["lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe",
   s!"lake exe ix compile Ix/Kernel/PinGen/Certs.lean --out .lake/envs/certs.ixe --consts \\\n      \
    {",".intercalate (certSpecs.flatMap (·.2) |>.map toString)}",
   "lake exe kernel-pin-gen .lake/envs/initstd.ixe .lake/envs/certs.ixe \\\n      \
    Ix/Kernel/Ixon/PinData.lean Ix/Kernel/Ixon/NatOpPinData.lean"]

def toLeanName : CName → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (toLeanName p) s
  | .num p n => .num (toLeanName p) n

def isRecursorName : CName → Bool
  | .str _ s => s == "rec" || s.startsWith "rec_"
  | _ => false

def components : CName → List (String ⊕ Nat)
  | .anonymous => []
  | .str p s => components p ++ [.inl s]
  | .num p n => components p ++ [.inr n]

def componentLit : String ⊕ Nat → String
  | .inl s => s!".inl {s.quote}"
  | .inr n => s!".inr {n}"

def ixToC : Ix.Name → CName
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixToC p) s
  | .num p n _ => .num (ixToC p) n

/-- The level-parameter names a constant's metadata records. -/
def metaLevels (env : Ixon.Env) (named : Ixon.Named) : Option (List CName) := do
  let addrs := match named.constMeta.info with
    | .defn _ lvls .. | .axio _ lvls .. | .quot _ lvls .. | .indc _ lvls .. | .ctor _ lvls ..
    | .recr _ lvls .. => lvls
    | _ => #[]
  addrs.toList.mapM fun a => ixToC <$> env.names[a]?

def refFields : ConstRef Address → String × Nat × Nat
  | .member b i => (toString b, i, 0)
  | .ctor b i c => (toString b, i, c + 1)

def sha256 (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  return (out.stdout.splitOn " ").headD ""

/-- An `.ixe`'s records, decoded. -/
def loadStore (path : System.FilePath) : IO (Ixon.Env × RecordStore) := do
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  return (env, store)

/-! ## Reading declarations -/

/-- Read `addresses` in order, threading the reader state as the environment check does,
and return each record's declarations, with the records that do not read. -/
def readOrdered (s : Setup) (addresses : Array Address) :
    Std.HashMap Address (Array CDecl) × Array (Address × ReadError) := Id.run do
  let mut st : State := {}
  let mut out : Std.HashMap Address (Array CDecl) := {}
  let mut errors : Array (Address × ReadError) := #[]
  for a in addresses do
    let some c := s.store[a]? | continue
    match readRecord s.cx st a c with
    | .ok r =>
      st := st.commit r
      out := out.insert a r.decls
    | .error e => errors := errors.push (a, e)
  return (out, errors)

/-- The record owners `roots` reach by table references, projections replaced
by their owners: the records a dependency order puts before them. -/
def reachable (store : RecordStore) (roots : Array Address) : Std.HashSet Address := Id.run do
  let mut reach : Std.HashSet Address := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let a := todo[todo.size - 1]
    todo := todo.pop
    let some c := store[a]? | continue
    let o := owner a c
    if reach.contains o then continue
    reach := reach.insert o
    for r in ((store[o]?.map (·.refs)).getD #[]) do
      if store.contains r then todo := todo.push r
  return reach

/-- What the inliner needs about the declarations read: the values of the
definitions, theorems and opaques (with their level parameters), and the
parameter counts of the constructors. -/
structure Universe where
  values : Std.HashMap CName (List CName × CExpr) := {}
  ctorParams : Std.HashMap CName Nat := {}

def Universe.add (u : Universe) (d : CDecl) : Universe :=
  match d with
  | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
    { u with values := u.values.insert cv.name (cv.levelParams, v) }
  | .indDecl block _ => block.foldl (fun u ci => match ci with
      | .ctorInfo cv nP _ => { u with ctorParams := u.ctorParams.insert cv.name nP }
      | _ => u) u
  | _ => u

/-! ## Expression surgery (memoized over the DAG; host code) -/

abbrev Memo := Std.HashMap CExpr CExpr

/-- The level parameters `ks` instantiated by `us`. -/
partial def instLevelsGo (ks : List CName) (us : List CLevel) (e : CExpr) : StateM Memo CExpr := do
  if !e.hasLP then return e
  if let some r := (← get)[e]? then return r
  let r ← match e with
    | .sort u => pure (.sort (Ix.Kernel.Level.subst ks us u))
    | .const n ls => pure (.const n (ls.map (Ix.Kernel.Level.subst ks us)))
    | .app f a => return .app (← instLevelsGo ks us f) (← instLevelsGo ks us a)
    | .lam t b m => return .lam (← instLevelsGo ks us t) (← instLevelsGo ks us b) m
    | .forallE t b m => return .forallE (← instLevelsGo ks us t) (← instLevelsGo ks us b) m
    | .letE t v b =>
      return .letE (← instLevelsGo ks us t) (← instLevelsGo ks us v) (← instLevelsGo ks us b)
    | .proj s i x => return .proj s i (← instLevelsGo ks us x)
    | .fvar i t => return .fvar i (← instLevelsGo ks us t)
    | e => pure e
  modify (·.insert e r)
  return r

def instLevels (ks : List CName) (us : List CLevel) (e : CExpr) : CExpr :=
  if ks.isEmpty then e else (instLevelsGo ks us e |>.run {}).1

/-- No loose `bvar` at or above `d`. -/
def closedAbove (e : CExpr) (d : Nat) : Bool :=
  e.bvarBRaw < Ix.Kernel.satRange && e.bvarBRaw ≤ d

/-- `e` with loose `bvar (d + k)` replaced by `vs[n - 1 - k]` (lifted past the
`d` binders crossed) for `k < n = vs.size`, and the loose `bvar`s above
lowered by `n`: Lean's `instantiate` of the reversed `vs`, so `vs[n - 1]` is
`bvar 0`. -/
partial def instGo (vs : Array CExpr) (d : Nat) (e : CExpr) :
    StateM (Std.HashMap (CExpr × Nat) CExpr) CExpr := do
  if closedAbove e d then return e
  if let some r := (← get)[(e, d)]? then return r
  let n := vs.size
  let r ← match e with
    | .bvar i =>
      if i < d then pure (.bvar i)
      else if i - d < n then
        let v := vs[n - 1 - (i - d)]!
        pure (if d == 0 || closedAbove v 0 then v else Ix.Kernel.Expr.liftLooseBVars d 0 v)
      else pure (Ix.Kernel.Expr.mkBvar (i - n))
    | .app f a => return .app (← instGo vs d f) (← instGo vs d a)
    | .lam t b m => return .lam (← instGo vs d t) (← instGo vs (d + 1) b) m
    | .forallE t b m => return .forallE (← instGo vs d t) (← instGo vs (d + 1) b) m
    | .letE t v b => return .letE (← instGo vs d t) (← instGo vs d v) (← instGo vs (d + 1) b)
    | .proj s i x => return .proj s i (← instGo vs d x)
    | e => pure e
  modify (·.insert (e, d) r)
  return r

def instantiate (e : CExpr) (vs : Array CExpr) : CExpr :=
  if vs.isEmpty then e else (instGo vs 0 e |>.run {}).1

/-- The number of leading `fun` binders of `f`, at most `k`, and the body
under them. -/
def peelLams : Nat → CExpr → Nat × CExpr
  | k + 1, .lam _ b _ => let (m, body) := peelLams k b; (m + 1, body)
  | _, e => (0, e)

/-- `f args`, beta-reduced at the head. -/
def betaApp (f : CExpr) (args : Array CExpr) : CExpr :=
  let (m, body) := peelLams args.size f
  let head := if m == 0 then f else instantiate body (args.extract 0 m)
  (args.extract m args.size).foldl .app head

/-- One pass: every constant `inline` selects that has a value is replaced by
it (levels instantiated, beta-reduced against its arguments), and the result
is visited again (upstream's `unfoldStep` under `Core.transform`). -/
partial def unfoldGo (u : Universe) (inline : CName → Bool) (e : CExpr) : StateM Memo CExpr := do
  if let some r := (← get)[e]? then return r
  let unfolded : Option CExpr := match e.getAppFn with
    | .const c us =>
      if inline c then
        match u.values[c]? with
        | some (lps, v) =>
          if lps.length == us.length then some (betaApp (instLevels lps us v) e.getAppArgs.toArray)
          else none
        | none => none
      else none
    | _ => none
  let r ← match unfolded with
    | some e' => unfoldGo u inline e'
    | none => match e with
      | .app f a => return .app (← unfoldGo u inline f) (← unfoldGo u inline a)
      | .lam t b m => return .lam (← unfoldGo u inline t) (← unfoldGo u inline b) m
      | .forallE t b m => return .forallE (← unfoldGo u inline t) (← unfoldGo u inline b) m
      | .letE t v b =>
        return .letE (← unfoldGo u inline t) (← unfoldGo u inline v) (← unfoldGo u inline b)
      | .proj s i x => return .proj s i (← unfoldGo u inline x)
      | e => pure e
  modify (·.insert e r)
  return r

/-- A projection of a constructor application: its field. -/
def projOfCtor (u : Universe) (i : Nat) (x : CExpr) : Option CExpr :=
  match x.getAppFn with
  | .const c _ => do
    let nP ← u.ctorParams[c]?
    let args := x.getAppArgs.toArray
    if h : nP + i < args.size then some args[nP + i] else none
  | _ => none

/-- One pass of beta, `let` (zeta) and projection-of-constructor reduction
(upstream's `simpStep`, and the zeta-expansion of its `toConLeche`), each
result visited again. -/
partial def simpGo (u : Universe) (e : CExpr) : StateM Memo CExpr := do
  if let some r := (← get)[e]? then return r
  let reduced : Option CExpr := match e with
    | .letE _ v b => some (instantiate b #[v])
    | .proj _ i x => projOfCtor u i x
    | .app .. =>
      match e.getAppFn with
      | f@(.lam ..) => some (betaApp f e.getAppArgs.toArray)
      | _ => none
    | _ => none
  let r ← match reduced with
    | some e' => simpGo u e'
    | none => match e with
      | .app f a => return .app (← simpGo u f) (← simpGo u a)
      | .lam t b m => return .lam (← simpGo u t) (← simpGo u b) m
      | .forallE t b m => return .forallE (← simpGo u t) (← simpGo u b) m
      | .proj s i x => return .proj s i (← simpGo u x)
      | e => pure e
  modify (·.insert e r)
  return r

/-- Every constant (and projection structure) an expression names. -/
partial def constsGo (e : CExpr) : StateM (Std.HashSet CExpr × Std.HashSet CName) Unit := do
  if (← get).1.contains e then return
  modify fun (seen, cs) => (seen.insert e, cs)
  match e with
  | .const n _ => modify fun (seen, cs) => (seen, cs.insert n)
  | .app f a => constsGo f; constsGo a
  | .lam t b _ | .forallE t b _ => constsGo t; constsGo b
  | .letE t v b => constsGo t; constsGo v; constsGo b
  | .proj s _ x => modify (fun (seen, cs) => (seen, cs.insert s)); constsGo x
  | .fvar _ t => constsGo t
  | _ => pure ()

def constsOf (e : CExpr) : Std.HashSet CName := ((constsGo e).run ({}, {})).2.2

/-- Upstream's `inlineCertClosure`: unfold and simplify to a fixpoint, then
require every remaining constant to be `allowed`. -/
def inlineCertClosure (u : Universe) (allowed : CName → Bool) (e : CExpr) :
    Except String CExpr := do
  let mut e := e
  let mut done := false
  for _ in [0:1000] do
    let e1 := (unfoldGo u (!allowed ·) e |>.run {}).1
    let e2 := (simpGo u e1 |>.run {}).1
    if e2 == e then
      done := true
      break
    e := e2
  unless done do throw "no fixpoint after 1000 rounds"
  let bad := (constsOf e).toList.filter (!allowed ·)
  unless bad.isEmpty do
    throw s!"residual constants outside the operation's cone, ground and statement machinery \
      (name, has a value): {bad.map fun n => (n, (u.values[n]?).isSome)}"
  return e

/-! ## The share table (the format of `Ix/Kernel/Ixon/Prelude.lean`) -/

def hexByte (b : UInt8) : String :=
  let d := "0123456789ABCDEF".toList.toArray
  String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!]

/-- Percent-encode every byte outside `[A-Za-z0-9._'!?-]`. -/
def percentEncode (s : String) : String :=
  s.toUTF8.foldl (fun acc b =>
    let c := Char.ofNat b.toNat
    if b < 128 && (c.isAlphanum || "._'!?-".contains c) then acc.push c
    else acc ++ "%" ++ hexByte b) ""

structure Enc where
  lines : Array String := #[]
  names : Std.HashMap CName Nat := {}
  levels : Std.HashMap CLevel Nat := {}
  exprs : Std.HashMap CExpr Nat := {}

abbrev EncM := StateT Enc (Except String)

def emit (line : String) : EncM Nat := do
  let i := (← get).lines.size + 2
  modify fun s => { s with lines := s.lines.push line }
  return i

partial def encName (n : CName) : EncM Nat := do
  if let .anonymous := n then return 0
  if let some i := (← get).names[n]? then return i
  let i ← match n with
    | .str p s => do let a ← encName p; emit s!"n {a} {percentEncode s}"
    | .num p k => do let a ← encName p; emit s!"m {a} {k}"
    | .anonymous => pure 0
  modify fun s => { s with names := s.names.insert n i }
  return i

partial def encLevel (l : CLevel) : EncM Nat := do
  if let .zero := l then return 1
  if let some i := (← get).levels[l]? then return i
  let i ← match l with
    | .succ u => do let a ← encLevel u; emit s!"S {a}"
    | .max u v => do let a ← encLevel u; let b ← encLevel v; emit s!"M {a} {b}"
    | .imax u v => do let a ← encLevel u; let b ← encLevel v; emit s!"I {a} {b}"
    | .param n => do let a ← encName n; emit s!"P {a}"
    | .zero => pure 1
  modify fun s => { s with levels := s.levels.insert l i }
  return i

def requireNever (m : Ix.Kernel.BinderMeta) : EncM Unit :=
  unless m.pw.toList?.isNone do throw "a binder with a prop-ness annotation other than `never`"

partial def encExpr (e : CExpr) : EncM Nat := do
  if let some i := (← get).exprs[e]? then return i
  let i ← match e with
    | .bvar k => emit s!"B {k}"
    | .sort u => do let a ← encLevel u; emit s!"Y {a}"
    | .const n us => do
      let a ← encName n
      let bs ← us.mapM encLevel
      emit (" ".intercalate (["C", toString a] ++ bs.map toString))
    | .app f x => do let a ← encExpr f; let b ← encExpr x; emit s!"A {a} {b}"
    | .lam t b m => do
      requireNever m; let a ← encExpr t; let c ← encExpr b; emit s!"L {a} {c}"
    | .forallE t b m => do
      requireNever m; let a ← encExpr t; let c ← encExpr b; emit s!"F {a} {c}"
    | .letE t v b => do
      let a ← encExpr t; let c ← encExpr v; let d ← encExpr b; emit s!"E {a} {c} {d}"
    | .lit (.natVal k) => emit s!"N {k}"
    | .lit (.strVal s) => emit s!"T {percentEncode s}"
    | .proj s k x => do let a ← encName s; let c ← encExpr x; emit s!"J {a} {k} {c}"
    | .fvar .. => throw "a free variable in a pin"
  modify fun s => { s with exprs := s.exprs.insert e i }
  return i

/-- The variant as a share table and its per-operation roots. -/
def encodePins (ps : Ix.Kernel.NatOpPinSet) :
    Except String (Array String × Array (String × Nat × List Nat)) := do
  let ops : List (String × CExpr × List CExpr) :=
    [("Nat.div", ps.divPin, ps.divProofs), ("Nat.mod", ps.modPin, ps.modProofs),
     ("Nat.gcd", ps.gcdPin, ps.gcdProofs), ("Nat.land", ps.landPin, ps.landProofs),
     ("Nat.lor", ps.lorPin, ps.lorProofs), ("Nat.xor", ps.xorPin, ps.xorProofs),
     ("Nat.shiftLeft", ps.shiftLeftPin, ps.shiftLeftProofs),
     ("Nat.shiftRight", ps.shiftRightPin, ps.shiftRightProofs)]
  let act : EncM (List (String × Nat × List Nat)) := ops.mapM fun (n, pin, proofs) => do
    let p ← encExpr pin
    let qs ← proofs.mapM encExpr
    return (n, p, qs)
  let (roots, enc) ← act.run {}
  return (enc.lines, roots.toArray)

def natOpPinSetBeq (a b : Ix.Kernel.NatOpPinSet) : Bool :=
  a.toolchain == b.toolchain && a.divPin == b.divPin && a.modPin == b.modPin &&
  a.gcdPin == b.gcdPin && a.landPin == b.landPin && a.lorPin == b.lorPin && a.xorPin == b.xorPin &&
  a.shiftLeftPin == b.shiftLeftPin && a.shiftRightPin == b.shiftRightPin &&
  a.divProofs == b.divProofs && a.modProofs == b.modProofs && a.gcdProofs == b.gcdProofs &&
  a.landProofs == b.landProofs && a.lorProofs == b.lorProofs && a.xorProofs == b.xorProofs &&
  a.shiftLeftProofs == b.shiftLeftProofs && a.shiftRightProofs == b.shiftRightProofs

/-! ## The Nat-operation pins -/

/-- The pin variant: pins from the Init reading, certificate proofs from the
certificates' reading, closed by upstream's rule. -/
def natOpPins (env : Ixon.Env) (s : Setup) (pre : Prelude) (pinned : Pins)
    (byName : Std.HashMap CName (ConstRef Address)) (certPath : System.FilePath)
    (toolchain : String) : IO Ix.Kernel.NatOpPinSet := do
  let fail {α : Type} (msg : String) : IO α := throw (IO.userError s!"pin-gen: {msg}")
  let opRefs ← certSpecs.mapM fun (op, _) => do
    let some r := byName[op]? | fail s!"{op} is not pinned"
    pure (op, r)
  -- the Init reading: the prelude and the operations' closures, in order
  let initOrder := closure s.store s.extra
    (pre.records.map (·.1) ++ (opRefs.map (·.2.block)).toArray)
  let (initDecls, initErrors) := readOrdered s initOrder
  unless initErrors.isEmpty do
    fail s!"Init records that do not read: {initErrors.toList.map fun (a, e) => (toString a, toString e)}"
  -- the certificates' compile, read under the same table and prelude, over
  -- the Init's records: `--consts` compiles a closure that leaves out the
  -- recursors nothing names, and the two compiles agree on every shared
  -- address (checked below for the operations)
  let (certEnv, certRecords) ← loadStore certPath
  let mut certStore := s.store
  let mut added := 0
  for (a, c) in certRecords.toList do
    unless certStore.contains a do
      certStore := certStore.insert a c
      added := added + 1
  let initBlobs := env.blobs
  let cs := setup certStore (fun a => certEnv.blobs[a]? <|> initBlobs[a]?) pinned pre
    (Hints.ofStore certStore certEnv.anonHints).lookup
  for (op, _) in opRefs do
    let lean := Ix.Name.fromLeanName (toLeanName op)
    let some named := certEnv.named[lean]? | fail s!"{certPath} has no {op}"
    let some initNamed := env.named[lean]? | fail s!"the Init has no {op}"
    unless named.addr == initNamed.addr do
      fail s!"{op} is {named.addr} in {certPath} but {initNamed.addr} in the Init: \
        the two compiles disagree"
  let mut certRoots : Array Address := pre.records.map (·.1)
  let mut certAt : Std.HashMap Lean.Name Address := {}
  for (_, thms) in certSpecs do
    for t in thms do
      let some named := certEnv.named[Ix.Name.fromLeanName t]? | fail s!"{certPath} has no {t}"
      certRoots := certRoots.push named.addr
      certAt := certAt.insert t named.addr
  let certOrder := closure cs.store cs.extra certRoots
  let (certDecls, certErrors) := readOrdered cs certOrder
  unless certErrors.isEmpty do
    fail s!"certificate records that do not read: \
      {certErrors.toList.map fun (a, e) => (toString a, toString e)}"
  let uni : Universe := (initDecls.toList ++ certDecls.toList).foldl
    (fun u (_, ds) => ds.foldl Universe.add u) {}
  IO.eprintln s!"pin-gen: Nat-op pins: {initOrder.size} Init records read; the certificates' \
    compile adds {added} records to the Init's, {certOrder.size} read; {uni.values.size} values"
  let mut pins : Array (CExpr × List CExpr) := #[]
  for (op, r) in opRefs do
    -- the pin: the stored value
    let pinOf? : Option CExpr := (initDecls.getD r.block #[]).findSome? (fun d =>
      match d with
      | .defnDecl cv v _ => if cv.name == op then some v else none
      | _ => none)
    let some pin := pinOf? | fail s!"{op}'s record does not read as its definition"
    -- the cone: the declarations of every record the operation's record reaches
    let cone : Std.HashSet CName := (reachable s.store #[r.block]).fold (fun acc a =>
      (initDecls.getD a #[]).foldl (fun acc d => d.names.foldl (·.insert ·) acc) acc) {}
    let ground : List CName := Ix.Kernel.natOpDeps op ++ stmtNames
    let allowed : CName → Bool := fun c => c == op || ground.contains c || cone.contains c
    let thms := ((certSpecs.find? (·.1 == op)).map (·.2)).getD []
    let mut proofs : List CExpr := []
    for t in thms do
      let a := certAt.getD t default
      let some name := (resolve (cs.store[·]?) a).map cs.cx.nameOf | fail s!"{t} does not resolve"
      let valueOf? : Option CExpr := (certDecls.getD a #[]).findSome? (fun d =>
        match d with
        | .thmDecl cv v => if cv.name == name then some v else none
        | _ => none)
      let some value := valueOf? | fail s!"{t}'s record does not read as a theorem"
      match inlineCertClosure uni allowed value with
      | .ok p => proofs := proofs ++ [p]
      | .error why => fail s!"certificate {t} of {op}: {why}"
    IO.eprintln s!"pin-gen: {op}: cone {cone.size} constants, {proofs.length} certificates closed"
    pins := pins.push (pin, proofs)
  let some (divPin, divProofs) := pins[0]? | fail "no pins"
  let (modPin, modProofs) := pins[1]!
  let (gcdPin, gcdProofs) := pins[2]!
  let (landPin, landProofs) := pins[3]!
  let (lorPin, lorProofs) := pins[4]!
  let (xorPin, xorProofs) := pins[5]!
  let (shiftLeftPin, shiftLeftProofs) := pins[6]!
  let (shiftRightPin, shiftRightProofs) := pins[7]!
  return { toolchain, divPin, modPin, gcdPin, landPin, lorPin, xorPin, shiftLeftPin, shiftRightPin,
           divProofs, modProofs, gcdProofs, landProofs, lorProofs, xorProofs, shiftLeftProofs,
           shiftRightProofs }

/-! ## The run -/

def run (args : List String) : IO UInt32 := do
  let parsed : Option (String × String × String × String × Option String) := match args with
    | [i, c, o, n] => some (i, c, o, n, none)
    | [i, c, o, n, r] => some (i, c, o, n, some r)
    | _ => none
  let some (input, certInput, output, natOutput, rowsOut) := parsed
    | IO.eprintln "usage: kernel-pin-gen <init.ixe> <certs.ixe> <PinData.lean> \
        <NatOpPinData.lean> [closure.jsonl]"
      return 2
  let started ← IO.monoMsNow
  let (env, store) ← loadStore input
  IO.eprintln s!"pin-gen: {store.size} records loaded in {(← IO.monoMsNow) - started} ms"
  let lookup : Ix.Kernel.IxonReader.Store := (store[·]?)
  -- 1-2: names and candidates
  let wanted := (fixedNames ++ preludeGroups.flatten).eraseDups
  let mut pins : Array Pin := #[]
  let mut missing : Array CName := #[]
  let mut recNames : Array CName := #[]
  let mut addrOf : Std.HashMap CName Address := {}
  for n in wanted do
    let some named := env.named[Ix.Name.fromLeanName (toLeanName n)]?
      | missing := missing.push n; continue
    addrOf := addrOf.insert n named.addr
    if isRecursorName n then recNames := recNames.push n; continue
    let some c := store[named.addr]? | missing := missing.push n; continue
    let some ref := resolveSource lookup named.addr c | missing := missing.push n; continue
    pins := pins.push ⟨ref, n⟩
  unless missing.isEmpty do
    IO.eprintln s!"pin-gen: required names without a resolvable record: {missing.toList}"
    return 1
  -- aliases: two names on one reference keep the first and are reported
  let mut byRef : Std.HashMap (ConstRef Address) CName := {}
  let mut kept : Array Pin := #[]
  for p in pins do
    if let some other := byRef[p.ref]? then
      IO.eprintln s!"pin-gen: alias: {p.name} and {other} are the same constant; keeping {other}"
    else
      byRef := byRef.insert p.ref p.name
      kept := kept.push p
  let pinnedNames ← IO.ofExcept (pinMap kept)
  -- level-parameter names: every pinned constant's, and the recursors' of
  -- every pinned inductive (`matchesPin` compares them by name)
  let mut levels : Std.HashMap (ConstRef Address) (List CName) := {}
  for p in kept do
    let some named := env.named[Ix.Name.fromLeanName (toLeanName p.name)]? | continue
    if let some ns := metaLevels env named then levels := levels.insert p.ref ns
    if (inductiveAt lookup p.ref).isSome then
      for r in (List.range 8).map (fun k => if k == 0 then p.name.str "rec" else p.name.str s!"rec_{k}") do
        let some rn := env.named[Ix.Name.fromLeanName (toLeanName r)]? | continue
        let some rc := store[rn.addr]? | continue
        let some rref := resolveSource lookup rn.addr rc | continue
        if let some ns := metaLevels env rn then levels := levels.insert rref ns
  let pinned : Pins := { names := pinnedNames, levels }
  IO.eprintln s!"pin-gen: {kept.size} pins, {levels.size} level lists, {recNames.size} derived recursor names"
  -- the prelude records, in prelude order
  let mut preludeAddrs : Array Address := #[]
  for group in preludeGroups do
    for n in group do
      let a := addrOf.getD n default
      let some c := store[a]? | IO.eprintln s!"pin-gen: no prelude record for {n}"; return 1
      for x in #[owner a c, a] do
        unless preludeAddrs.contains x do preludeAddrs := preludeAddrs.push x
  let preRecords : Array (Address × Ixon.Constant) := preludeAddrs.filterMap fun a =>
    (store[a]?).map (a, ·)
  -- canonical bytes round-trip through the decoder the prelude loader uses
  for (a, c) in preRecords do
    let bytes := Ixon.serConstant c
    match Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes bytes with
    | .ok c' => unless c' == c do IO.eprintln s!"pin-gen: prelude record {a} does not round-trip"; return 1
    | .error e => IO.eprintln s!"pin-gen: prelude record {a}: {e}"; return 1
  let pre ← match readPrelude pinned preRecords with
    | .ok p => pure p
    | .error e => IO.eprintln s!"pin-gen: prelude: {e}"; return 1
  IO.eprintln s!"pin-gen: prelude: {preRecords.size} records, {pre.ix.decls.size} declarations: \
    {pre.ix.decls.toList.map Ix.Kernel.Frontend.preludeKey}"
  let s := setup store (env.blobs[·]?) pinned pre (Hints.ofStore store env.anonHints).lookup
  for n in recNames do
    let a := addrOf.getD n default
    let some c := store[a]? | continue
    let some ref := resolveSource lookup a c | continue
    unless s.cx.nameOf ref == n do
      IO.eprintln s!"pin-gen: recursor {n} is named {s.cx.nameOf ref} by the reader"
      return 1
  -- 3: the Nat-operation pins
  let toolchain := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  let byName : Std.HashMap CName (ConstRef Address) := kept.foldl (fun m p => m.insert p.name p.ref) {}
  let natPins ← natOpPins env s pre pinned byName certInput toolchain
  let (tableLines, opRoots) ← IO.ofExcept (encodePins natPins)
  let table := "\n".intercalate tableLines.toList
  let decoded ← IO.ofExcept do
    natOpPinSetOf toolchain (← decodePinTable ("\n" ++ table ++ "\n")) opRoots
  unless natOpPinSetBeq decoded natPins do
    IO.eprintln "pin-gen: the share table does not decode to the generated variant"
    return 1
  IO.eprintln s!"pin-gen: Nat-op pin variant: {tableLines.size} share-table nodes, decoded back equal"
  -- 4: verification by the verified fold over the pinned constants' closure
  let roots := (preRecords.map (·.1)) ++ (kept.map (·.ref.block))
  let ordered := closure s.store s.extra roots
  IO.eprintln s!"pin-gen: checking the closure, {ordered.size} records"
  let rows ← IO.mkRef (#[] : Array Row)
  let names := reportNames env s.store
  let out ← checkLoop s [natPins] (names.getD · #[]) ordered {}
    (emit := fun row => rows.modify (·.push row))
  let rows ← rows.get
  if let some path := rowsOut then
    IO.FS.writeFile path (String.intercalate "\n" (rows.toList.map (·.json.compress)) ++ "\n")
  IO.eprintln s!"pin-gen: closure checked in {(← IO.monoMsNow) - started} ms: {out.counts.toList}"
  let outcomeOf : Std.HashMap Address (String × String) :=
    rows.foldl (fun m r => m.insert r.address (r.outcome, r.reason)) {}
  -- every pinned constant's record must be accepted (a pin-certified
  -- operation's only when the variant matched and its certificates
  -- checked), and both literal capabilities must hold in the final environment
  let mut bad := 0
  for p in kept do
    let verdict := outcomeOf[p.ref.block]?
    match verdict with
    | some ("accept", _) => pure ()
    | _ =>
      let (o, reason) := verdict.getD ("unchecked", "")
      IO.eprintln s!"pin-gen: pinned {p.name}: {o}: {reason}"
      bad := bad + 1
  let fe := out.checker.fe
  let nat := Ix.Kernel.natLitSupportedF fe
  let str := Ix.Kernel.strLitSupportedF fe
  IO.eprintln s!"pin-gen: Nat literals {nat}, String literals {str}"
  unless bad == 0 && nat && str do return 1
  for (op, _) in certSpecs do
    let a := ((byName[op]?).map (·.block)).getD default
    let micros := ((rows.find? (·.address == a)).map (·.micros)).getD 0
    IO.eprintln s!"pin-gen: {op}: accepted with the generated variant, {micros} µs"
  -- 5: output
  let digest ← sha256 input
  let certDigest ← sha256 certInput
  let sorted := kept.qsort (fun a b => toString a.name < toString b.name)
  let pinLines := sorted.toList.map fun p =>
    let (b, i, c) := refFields p.ref
    s!"  ([{", ".intercalate ((components p.name).map componentLit)}], {b.quote}, {i}, {c})"
  let levelLines := (levels.toArray.qsort (fun a b => toString (refFields a.1) < toString (refFields b.1))).toList.map
    fun (r, ns) =>
      let (b, i, c) := refFields r
      s!"  ({b.quote}, {i}, {c}, [{", ".intercalate (ns.map fun n => s!"[{", ".intercalate ((components n).map componentLit)}]")}])"
  let preLines := preRecords.toList.map fun (a, c) =>
    s!"  ({(toString a).quote},\n   {(hexOfBytes (Ixon.serConstant c)).quote})"
  let recipe := "\n".intercalate (regenerate.map ("    " ++ ·))
  let text := s!"/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # Pinned names and prelude records (generated)

GENERATED by `kernel-pin-gen` (`Benchmarks/Kernel/PinGen.lean`),
together with `NatOpPinData.lean`; do not edit. To regenerate:

{recipe}

Every pinned constant's record, and the literal capabilities, were checked by
the verified fold through the Ixon reader when this file was
generated; see `Ix/Kernel/Ixon/Reader.lean` for what the table may affect
(coverage, never soundness). Source: sha256 {digest}.

`pins`: (name components, block address, member, constructor + 1 or 0).
`levels`: (block address, member, constructor + 1 or 0, level-parameter
names), for the pinned constants and their recursors.
`prelude`: (record address, canonical record bytes), in the checker's
prelude order. -/

namespace Ix.Kernel.IxonReader.PinData

def source : String := {s!"sha256:{digest}".quote}

def pins : Array (List (String ⊕ Nat) × String × Nat × Nat) := #[
{",\n".intercalate pinLines}]

def levels : Array (String × Nat × Nat × List (List (String ⊕ Nat))) := #[
{",\n".intercalate levelLines}]

def prelude : Array (String × String) := #[
{",\n".intercalate preLines}]

end Ix.Kernel.IxonReader.PinData
"
  IO.FS.writeFile output text
  IO.eprintln s!"pin-gen: wrote {output}: {sorted.size} pins, {preRecords.size} prelude records"
  let opLines := opRoots.toList.map fun (n, pin, proofs) =>
    s!"  ({n.quote}, {pin}, {proofs})"
  let natText := s!"/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # The pin-certified Nat operations' pins and certificates (generated)

GENERATED by `kernel-pin-gen` (`Benchmarks/Kernel/PinGen.lean`),
together with `PinData.lean`; do not edit. To regenerate:

{recipe}

One pin variant (`Ix.Kernel.NatOpPinSet`) of the eight pin-certified `Nat`
operations, from Ixon records only:

* the pins are the operations' stored values in the compiled Init (sha256
  {digest}), as the Ixon reader reads them;
* the certificate proofs are the theorems of `Ix/Kernel/PinGen/Certs.lean`,
  compiled by the Ix compiler (sha256 {certDigest}) and read by the same
  reader, with every constant outside the operation's dependency cone, its
  certificate ground and the statements' machinery inlined, and beta, `let`
  and projection-of-constructor redexes reduced (upstream's pinner's rule).

Every operation was certified by the verified fold through the Ixon
reader, with this variant, when this file was generated. The fold takes its
pin list as a parameter and `Ix.Kernel.model_exists` holds at every list, so
the data carries no trust. `table` is a share table and `ops` its roots per
operation, in `NatOpPinSet` field order; the format and the decoder are in
`Ix/Kernel/Ixon/Prelude.lean`. -/

namespace Ix.Kernel.IxonReader.NatOpPinData

def source : String := {s!"sha256:{digest} sha256:{certDigest}".quote}

def toolchain : String := {toolchain.quote}

def ops : Array (String × Nat × List Nat) := #[
{",\n".intercalate opLines}]

def table : String := r\"
{table}
\"

end Ix.Kernel.IxonReader.NatOpPinData
"
  IO.FS.writeFile natOutput natText
  let proofCount := (opRoots.toList.map (·.2.2.length)).foldl (· + ·) 0
  IO.eprintln s!"pin-gen: wrote {natOutput}: {tableLines.size} nodes, {proofCount} certificate proofs"
  return 0

end Benchmarks.Kernel.PinGen

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.PinGen.run args
