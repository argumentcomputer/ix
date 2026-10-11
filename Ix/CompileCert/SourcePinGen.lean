import Ix.CompileCert.ProjectionLoweringLean
import Ix.CompileCert.SourceNatOpPinData
import IxC.Kernel.Ixon.Prelude

/-! # Source-named pins of the pin-certified Nat operations (untrusted generator)

The certified checker accepts the eight pin-certified `Nat` operations
(`Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight`) only through a pin variant
(`Ix.Kernel.NatOpPinSet`): per operation, a pinned defining expression the
stored value must be definitionally equal to, and certificate proofs of the
checker's own pinned recurrence statements (`Ix.Kernel.divModCertStmts`),
checked by the fold at the operation's install. The committed variant
(`IxC/Kernel/Ixon/NatOpPinData.lean`, `Benchmarks/Kernel/PinGen.lean`) is read
from the compiled Ixon: its helpers are named by content address and its alias
fibers are merged (`LT.lt` and `LE.le` are one address), so it does not
translate back to the names of the normalised source installation, which folds
Lean's declarations under their own names.

This module generates the **same variant over the Lean environment**, by the
rule of `kernel-pin-gen`'s step 3, through the lane's export:

* **the pins** are the operations' Lean values, exported by `exportSourceExpr`
  (Lean's names, `sourceName`): exactly the values the source installation
  stores;
* **the certificate proofs** are the values of the same theorems of
  `IxC/Kernel/PinGen/Certs.lean` (`certSpecs`, the order of the checker's
  statements), as Lean elaborated them, exported by `exportSourceExpr`, and
  closed by upstream's rule (`inlineCertClosure`): every constant outside the
  operation's **Lean dependency cone** (its closure under the lane's
  `declarationRefs`: what every closed source cone containing the operation
  contains), its certificate ground (`Ix.Kernel.natOpDeps`) and the
  statements' machinery (`stmtNames`) is replaced by its exported value
  (levels instantiated, β-reduced against its arguments), with β, `let` and
  projection-of-constructor reduction, to a fixpoint; a residual outside those
  sets fails the generation.

`verifyOp` installs an operation's source cone with the generated variant
through the S route itself (`installSourceNormalizedComplete`: the export,
model proposal, normalisation, basis completion and the verified fold).
`SourcePinGenMain.lean` (`source-pin-gen`) runs the generation and the
verification and writes `SourceNatOpPinData.lean` (a share table in the format
of `IxC/Kernel/Ixon/Prelude.lean`, decoded by the committed decoder and
compared with the generated variant before it is written);
`sourceNatOpPinSets` decodes the committed data.

**Nothing here is trusted.** The fold takes its pin list as a parameter and
`Ix.Kernel.model_exists` (and so every theorem of the source installation)
holds for every list: the pin is compared with the stored value by `isDefEq`
and every certificate proof is type-checked against the checker's pinned
statement. A wrong or stale variant can only leave an operation declined.
`IxC/**` and `Benchmarks/Kernel/PinGen.lean` are not changed; the expression
surgery and the share-table encoder below are copies of the latter's (whose
module defines `main` and cannot be imported into a library). -/

namespace Ix.CompileCert.SourcePinGen

/-- The Lean name a kernel name is the `sourceName` of (`sourceName` is injective). -/
def leanOf : Kernel.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (leanOf p) s
  | .num p i => .num (leanOf p) i

/-- Per pin-certified operation, in `NatOpPinSet` field order: its Lean name, its
pinned name, and the theorems of `IxC/Kernel/PinGen/Certs.lean` that certify it,
in the order of its pinned statements (`Ix.Kernel.divModCertStmts`), as
`kernel-pin-gen`'s `certSpecs`. -/
def certSpecs : List (Lean.Name × Kernel.Name × List Lean.Name) :=
  [(`Nat.div, Kernel.natDivName, [`Ix.Kernel.PinGen.divRecCert, `Ix.Kernel.PinGen.divBaseGtCert,
     `Ix.Kernel.PinGen.divBaseZeroCert]),
   (`Nat.mod, Kernel.natModName, [`Ix.Kernel.PinGen.modRecCert, `Ix.Kernel.PinGen.modBaseGtCert,
     `Ix.Kernel.PinGen.modBaseZeroCert]),
   (`Nat.gcd, Kernel.natGcdName, [`Ix.Kernel.PinGen.gcdRecCert, `Ix.Kernel.PinGen.gcdBaseCert]),
   (`Nat.land, Kernel.natLandName, [`Ix.Kernel.PinGen.landRecCert, `Ix.Kernel.PinGen.landBaseCert]),
   (`Nat.lor, Kernel.natLorName, [`Ix.Kernel.PinGen.lorRecCert, `Ix.Kernel.PinGen.lorBaseCert]),
   (`Nat.xor, Kernel.natXorName, [`Ix.Kernel.PinGen.xorRecCert, `Ix.Kernel.PinGen.xorBaseCert]),
   (`Nat.shiftLeft, Kernel.natShiftLeftName, [`Ix.Kernel.PinGen.shiftLeftRecCert,
     `Ix.Kernel.PinGen.shiftLeftBaseCert]),
   (`Nat.shiftRight, Kernel.natShiftRightName, [`Ix.Kernel.PinGen.shiftRightRecCert,
     `Ix.Kernel.PinGen.shiftRightBaseCert])]

/-- The certificate statements' machinery (`kernel-pin-gen`'s `stmtNames`). -/
def stmtNames : List Kernel.Name :=
  [Kernel.natName, Kernel.natZeroName, Kernel.natSuccName, Kernel.natName.str "rec",
   Kernel.boolName, Kernel.boolTrueName, Kernel.boolFalseName, Kernel.boolName.str "rec",
   Kernel.eqName, Kernel.eqReflName, Kernel.eqName.str "rec"]

/-- The Lean dependency cone of `roots`: their closure under the lane's
`declarationRefs` (the reference sets of `CompleteSource`), in discovery order. -/
def leanCone (find : Lean.Name → Option Lean.ConstantInfo) (roots : List Lean.Name) :
    Except String (Array Lean.Name) := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut out : Array Lean.Name := #[]
  let mut todo : Array Lean.Name := roots.toArray.reverse
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := find n | return .error s!"missing source declaration {n}"
    out := out.push n
    for r in (declarationRefs ci).reverse do
      unless seen.contains r do todo := todo.push r
  return .ok out

/-! ## Expression surgery (memoised over the DAG; host code, as `kernel-pin-gen`'s) -/

abbrev Memo := Std.HashMap Kernel.Expr Kernel.Expr

/-- The level parameters `ks` instantiated by `us`. -/
partial def instLevelsGo (ks : List Kernel.Name) (us : List Kernel.Level) (e : Kernel.Expr) :
    StateM Memo Kernel.Expr := do
  if !e.hasLP then return e
  if let some r := (← get)[e]? then return r
  let r ← match e with
    | .sort u => pure (.sort (Kernel.Level.subst ks us u))
    | .const n ls => pure (.const n (ls.map (Kernel.Level.subst ks us)))
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

def instLevels (ks : List Kernel.Name) (us : List Kernel.Level) (e : Kernel.Expr) : Kernel.Expr :=
  if ks.isEmpty then e else (instLevelsGo ks us e |>.run {}).1

/-- No loose `bvar` at or above `d`. -/
def closedAbove (e : Kernel.Expr) (d : Nat) : Bool :=
  e.bvarBRaw < Kernel.satRange && e.bvarBRaw ≤ d

/-- `e` with loose `bvar (d + k)` replaced by `vs[n - 1 - k]` (lifted past the
`d` binders crossed) for `k < n = vs.size`, and the loose `bvar`s above lowered
by `n` (Lean's `instantiate` of the reversed `vs`). -/
partial def instGo (vs : Array Kernel.Expr) (d : Nat) (e : Kernel.Expr) :
    StateM (Std.HashMap (Kernel.Expr × Nat) Kernel.Expr) Kernel.Expr := do
  if closedAbove e d then return e
  if let some r := (← get)[(e, d)]? then return r
  let n := vs.size
  let r ← match e with
    | .bvar i =>
      if i < d then pure (.bvar i)
      else if i - d < n then
        let v := vs[n - 1 - (i - d)]!
        pure (if d == 0 || closedAbove v 0 then v else Kernel.Expr.liftLooseBVars d 0 v)
      else pure (Kernel.Expr.mkBvar (i - n))
    | .app f a => return .app (← instGo vs d f) (← instGo vs d a)
    | .lam t b m => return .lam (← instGo vs d t) (← instGo vs (d + 1) b) m
    | .forallE t b m => return .forallE (← instGo vs d t) (← instGo vs (d + 1) b) m
    | .letE t v b => return .letE (← instGo vs d t) (← instGo vs d v) (← instGo vs (d + 1) b)
    | .proj s i x => return .proj s i (← instGo vs d x)
    | e => pure e
  modify (·.insert (e, d) r)
  return r

def instantiate (e : Kernel.Expr) (vs : Array Kernel.Expr) : Kernel.Expr :=
  if vs.isEmpty then e else (instGo vs 0 e |>.run {}).1

/-- The number of leading `fun` binders of `f`, at most `k`, and the body under them. -/
def peelLams : Nat → Kernel.Expr → Nat × Kernel.Expr
  | k + 1, .lam _ b _ => let (m, body) := peelLams k b; (m + 1, body)
  | _, e => (0, e)

/-- `f args`, β-reduced at the head. -/
def betaApp (f : Kernel.Expr) (args : Array Kernel.Expr) : Kernel.Expr :=
  let (m, body) := peelLams args.size f
  let head := if m == 0 then f else instantiate body (args.extract 0 m)
  (args.extract m args.size).foldl .app head

/-- What the inliner needs: the exported values (with their universe telescopes)
of the constants it may unfold, and the parameter counts of constructors. -/
structure Universe where
  values : Std.HashMap Kernel.Name (List Kernel.Name × Kernel.Expr) := {}
  ctorParams : Kernel.Name → Option Nat

/-- One pass: every constant `inline` selects that has a value is replaced by it
(levels instantiated, β-reduced against its arguments), and the result is
visited again (upstream's `unfoldStep`). -/
partial def unfoldGo (u : Universe) (inline : Kernel.Name → Bool) (e : Kernel.Expr) :
    StateM Memo Kernel.Expr := do
  if let some r := (← get)[e]? then return r
  let unfolded : Option Kernel.Expr := match e.getAppFn with
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
def projOfCtor (u : Universe) (i : Nat) (x : Kernel.Expr) : Option Kernel.Expr :=
  match x.getAppFn with
  | .const c _ => do
    let nP ← u.ctorParams c
    let args := x.getAppArgs.toArray
    if h : nP + i < args.size then some args[nP + i] else none
  | _ => none

/-- One pass of β, `let` (ζ) and projection-of-constructor reduction, each
result visited again (upstream's `simpStep`). -/
partial def simpGo (u : Universe) (e : Kernel.Expr) : StateM Memo Kernel.Expr := do
  if let some r := (← get)[e]? then return r
  let reduced : Option Kernel.Expr := match e with
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
partial def constsGo (e : Kernel.Expr) :
    StateM (Std.HashSet Kernel.Expr × Std.HashSet Kernel.Name) Unit := do
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

def constsOf (e : Kernel.Expr) : Std.HashSet Kernel.Name := ((constsGo e).run ({}, {})).2.2

/-- Upstream's `inlineCertClosure`: unfold and simplify to a fixpoint, then
require every remaining constant to be `allowed`. -/
def inlineCertClosure (u : Universe) (allowed : Kernel.Name → Bool) (e : Kernel.Expr) :
    Except String Kernel.Expr := do
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
    throw s!"residual constants outside the operation's Lean cone, ground and statement machinery \
      (name, has a value): {bad.map fun n => (n, (u.values[n]?).isSome)}"
  return e

/-! ## The generation -/

/-- A constant's exported value and universe telescope, if it has one
(definitions, theorems, opaques), under Lean's names. -/
def exportedValue (find : Lean.Name → Option Lean.ConstantInfo) (c : Kernel.Name) :
    Except String (Option (List Kernel.Name × Kernel.Expr)) := do
  let value? : Option (List Lean.Name × Lean.Expr) := match find (leanOf c) with
    | some (.defnInfo v) => some (v.levelParams, v.value)
    | some (.thmInfo v) => some (v.levelParams, v.value)
    | some (.opaqueInfo v) => some (v.levelParams, v.value)
    | _ => none
  match value? with
  | none => return none
  | some (lps, value) =>
    let e ← (exportSourceExpr lps value).mapError (s!"export of {leanOf c}: " ++ ·)
    return some (lps.map sourceName, e)

/-- The values the inliner may need for `roots`: every constant reachable from
them through the values of constants `allowed` rejects. -/
def collectValues (find : Lean.Name → Option Lean.ConstantInfo) (allowed : Kernel.Name → Bool)
    (roots : List Kernel.Expr) : Except String (Std.HashMap Kernel.Name (List Kernel.Name × Kernel.Expr)) := do
  let mut values : Std.HashMap Kernel.Name (List Kernel.Name × Kernel.Expr) := {}
  let mut seen : Std.HashSet Kernel.Name := {}
  let mut todo : Array Kernel.Name := roots.foldl (fun acc e => acc ++ (constsOf e).toArray) #[]
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains c || allowed c then continue
    seen := seen.insert c
    if let some (lps, v) ← exportedValue find c then
      values := values.insert c (lps, v)
      for d in constsOf v do
        unless seen.contains d do todo := todo.push d
  return values

def ctorParamsOf (find : Lean.Name → Option Lean.ConstantInfo) (c : Kernel.Name) : Option Nat :=
  match find (leanOf c) with
  | some (.ctorInfo v) => some v.numParams
  | _ => none

/-- One operation's source pin and closed certificate proofs, with the size of
its Lean cone and the number of values inlined from. -/
def generateOp (find : Lean.Name → Option Lean.ConstantInfo) (op : Lean.Name) (opK : Kernel.Name)
    (thms : List Lean.Name) : Except String (Kernel.Expr × List Kernel.Expr × Nat × Nat) := do
  unless sourceName op == opK do throw s!"{op} is not the source name of {opK}"
  let some (.defnInfo d) := find op | throw s!"{op} is not a definition of the environment"
  let pin ← (exportSourceExpr d.levelParams d.value).mapError (s!"export of {op}: " ++ ·)
  let cone ← leanCone find [op]
  let coneK : Std.HashSet Kernel.Name := cone.foldl (fun s n => s.insert (sourceName n)) {}
  let ground := Kernel.natOpDeps opK ++ stmtNames
  let allowed : Kernel.Name → Bool := fun c => c == opK || ground.contains c || coneK.contains c
  let raw ← thms.mapM fun t => do
    let some (.thmInfo tv) := find t | throw s!"{t} is not a theorem of the environment"
    unless tv.levelParams.isEmpty do throw s!"{t} is universe-polymorphic"
    (exportSourceExpr tv.levelParams tv.value).mapError (s!"export of {t}: " ++ ·)
  let values ← collectValues find allowed raw
  let u : Universe := { values, ctorParams := ctorParamsOf find }
  let proofs ← raw.zip thms |>.mapM fun (e, t) =>
    (inlineCertClosure u allowed e).mapError (s!"certificate {t} of {op}: " ++ ·)
  return (pin, proofs, cone.size, values.size)

/-- The source variant, from an environment that has Lean's operations and the
theorems of `IxC/Kernel/PinGen/Certs.lean` (e.g. `importModules` of
`IxC.Kernel.PinGen.Certs`). `log` receives one line per operation. -/
def generate (find : Lean.Name → Option Lean.ConstantInfo) (toolchain : String) :
    Except String (Kernel.NatOpPinSet × List String) := do
  let mut out : Array (Kernel.Expr × List Kernel.Expr) := #[]
  let mut log : List String := []
  for (op, opK, thms) in certSpecs do
    let (pin, proofs, cone, inlined) ← generateOp find op opK thms
    log := log ++ [s!"{op}: Lean cone {cone} declarations, {inlined} values inlinable, \
      {proofs.length} certificates closed"]
    out := out.push (pin, proofs)
  let get (i : Nat) : Kernel.Expr × List Kernel.Expr := out[i]!
  return ({ toolchain := s!"{toolchain} (source names)",
            divPin := (get 0).1, modPin := (get 1).1, gcdPin := (get 2).1, landPin := (get 3).1,
            lorPin := (get 4).1, xorPin := (get 5).1, shiftLeftPin := (get 6).1,
            shiftRightPin := (get 7).1,
            divProofs := (get 0).2, modProofs := (get 1).2, gcdProofs := (get 2).2,
            landProofs := (get 3).2, lorProofs := (get 4).2, xorProofs := (get 5).2,
            shiftLeftProofs := (get 6).2, shiftRightProofs := (get 7).2 }, log)

/-- One operation's pin and certificate proofs in a variant. -/
def opEntry (ps : Kernel.NatOpPinSet) (opK : Kernel.Name) : Kernel.Expr × List Kernel.Expr :=
  (Kernel.divModDeclPin ps opK, Kernel.divModCertProofs ps opK)

/-- The Lean declarations an operation's pin and certificates name (its certificate
ground in the environment), sorted. -/
def groundOf (find : Lean.Name → Option Lean.ConstantInfo) (ps : Kernel.NatOpPinSet)
    (opK : Kernel.Name) : Array Lean.Name :=
  let (pin, proofs) := opEntry ps opK
  let names := (pin :: proofs).foldl (fun s e => (constsOf e).fold (fun s c => s.insert c) s)
    ({} : Std.HashSet Kernel.Name)
  let leans := names.toArray.filterMap fun c => (find (leanOf c)).map (fun _ => leanOf c)
  leans.qsort (fun a b => a.toString < b.toString)

/-- Structural equality of two variants (`DecidableEq` on the expressions). -/
def sameVariant (a b : Kernel.NatOpPinSet) : Bool :=
  a.toolchain == b.toolchain &&
  certSpecs.all fun (_, opK, _) => decide (opEntry a opK = opEntry b opK)

/-! ## Verification through the S route -/

/-- The source cone of `roots` (`leanCone`, discovery order) with its
completeness decided, for the normalised installation. -/
def sourceCone (find : Lean.Name → Option Lean.ConstantInfo) (roots : List Lean.Name) :
    Except String ((source : Source) × PLift (CompleteSource source roots)) := do
  let names ← leanCone find roots
  let source : Source := ⟨names.toList.filterMap find⟩
  if h : CompleteSource source roots then return ⟨source, ⟨h⟩⟩
  else throw "source cone is not closed"

/-- Install the source cone of `roots` with `pins` through the normalised source
installation (the S route), returning the number of installed declarations or
the refusal. -/
def installCone (env : Lean.Environment) (pins : List Kernel.NatOpPinSet) (roots : List Lean.Name) :
    IO (Except String Nat) := do
  match sourceCone env.find? roots with
  | .error why => return .error why
  | .ok ⟨source, ⟨complete⟩⟩ =>
    let witnesses ← LoweringLean.sourceWitnesses env source
    return match installSourceNormalizedComplete complete pins witnesses with
      | .ok installed => .ok installed.declarations.length
      | .error (.checking error position) => .error s!"source fold at {position}: {error}"
      | .error _ => .error "source installation refused before the fold"

/-! ## The share table (the format of `IxC/Kernel/Ixon/Prelude.lean`; `kernel-pin-gen`'s encoder) -/

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
  names : Std.HashMap Kernel.Name Nat := {}
  levels : Std.HashMap Kernel.Level Nat := {}
  exprs : Std.HashMap Kernel.Expr Nat := {}

abbrev EncM := StateT Enc (Except String)

def emit (line : String) : EncM Nat := do
  let i := (← get).lines.size + 2
  modify fun s => { s with lines := s.lines.push line }
  return i

partial def encName (n : Kernel.Name) : EncM Nat := do
  if let .anonymous := n then return 0
  if let some i := (← get).names[n]? then return i
  let i ← match n with
    | .str p s => do let a ← encName p; emit s!"n {a} {percentEncode s}"
    | .num p k => do let a ← encName p; emit s!"m {a} {k}"
    | .anonymous => pure 0
  modify fun s => { s with names := s.names.insert n i }
  return i

partial def encLevel (l : Kernel.Level) : EncM Nat := do
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

def requireNever (m : Kernel.BinderMeta) : EncM Unit :=
  unless m.pw.toList?.isNone do throw "a binder with a prop-ness annotation other than `never`"

partial def encExpr (e : Kernel.Expr) : EncM Nat := do
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
def encodePins (ps : Kernel.NatOpPinSet) :
    Except String (Array String × Array (String × Nat × List Nat)) := do
  let act : EncM (List (String × Nat × List Nat)) := certSpecs.mapM fun (op, opK, _) => do
    let (pin, proofs) := opEntry ps opK
    let p ← encExpr pin
    let qs ← proofs.mapM encExpr
    return (op.toString, p, qs)
  let (roots, enc) ← act.run {}
  return (enc.lines, roots.toArray)

/-- Decode a share table and its roots into a variant (the committed decoder). -/
def decodePins (toolchain table : String) (ops : Array (String × Nat × List Nat)) :
    Except String Kernel.NatOpPinSet := do
  Kernel.Reader.natOpPinSetOf toolchain (← Kernel.Reader.decodePinTable table) ops

/-! ## The committed source variant -/

/-- The committed source-named variant (`SourceNatOpPinData.lean`, generated by
`source-pin-gen`), decoded; an error when the data is absent or corrupted. -/
def committedSourceNatOpPins : Except String Kernel.NatOpPinSet :=
  decodePins SourceNatOpPinData.toolchain SourceNatOpPinData.table SourceNatOpPinData.ops

/-- The pin list of the source fold: the committed source variant (none when it
does not decode, the route's original form). -/
def sourceNatOpPinSets : List Kernel.NatOpPinSet :=
  match committedSourceNatOpPins with
  | .ok ps => [ps]
  | .error _ => []

end Ix.CompileCert.SourcePinGen
