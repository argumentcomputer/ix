import IxC.Kernel.Ixon.Reader

/-! # Proof evidence for the role table (untrusted)

A well-founded `Nat` operation (`Nat.div`, `Nat.mod`, …) is validated in the
fold against its `ops` specification by **proof evidence**: one theorem per
certificate statement (`Ix.Kernel.divModCertStmts`), whose proof the fold
checks against the statement with the operation's self-references replaced by
its value, in the environment before the operation is installed
(`Ix.Kernel.checkDivModEvidence`). The fold also requires the proofs to be
**local** (`Ix.Kernel.evidenceLocal`): every constant a proof mentions lies in
the dependency closure of the operation's value and of its dependencies'
roles.

The theorems are those of `IxC/Kernel/PinGen/Certs.lean` (`certTheorems`).
As elaborated they reach constants outside that closure (`Nat.div.go.eq_def`,
`Nat.le_of_ble_eq_true`, their own private helpers), so a proof is first
**closed** over the closure (`closeProof`, upstream con-leche's pinner's
rule): every constant outside it is replaced by its value, with beta, `let`
and projection-of-constructor redexes reduced, to a fixpoint. The closure is
the fold's own (`Ix.Kernel.refClosureGo`), computed over the declarations
read so far (`declInfos`). A residual outside it fails.

Both front ends use this module: Source mode closes the theorems as it ingests
them (`Ix.LeanIngress.sourceEvidence`), and the table generator
(`Benchmarks/Kernel/PinGen.lean`) closes them once and emits the closed proofs
as theorem records that the default table's evidence names. Nothing here is
trusted: the fold is sound at every evidence (`Ix.Kernel.model_exists`); a
proof this module gets wrong only declines its operation. -/

namespace Ix.RoleEvidence

open Ix.Kernel.Reader (CName CExpr CLevel CDecl)
open Ix.Kernel (LevelParam)

/-- The certificate theorems of `IxC/Kernel/PinGen/Certs.lean`: per
well-founded operation, its theorems in the order of its certificate
statements (`Ix.Kernel.divModCertStmts`). This is Source mode's fixed
evidence, and the generator's input. -/
def certTheorems : List (Ix.Kernel.Role × List Lean.Name) :=
  [(.natDiv, [`Ix.Kernel.PinGen.divRecCert, `Ix.Kernel.PinGen.divBaseGtCert,
     `Ix.Kernel.PinGen.divBaseZeroCert]),
   (.natMod, [`Ix.Kernel.PinGen.modRecCert, `Ix.Kernel.PinGen.modBaseGtCert,
     `Ix.Kernel.PinGen.modBaseZeroCert]),
   (.natGcd, [`Ix.Kernel.PinGen.gcdRecCert, `Ix.Kernel.PinGen.gcdBaseCert]),
   (.natLand, [`Ix.Kernel.PinGen.landRecCert, `Ix.Kernel.PinGen.landBaseCert]),
   (.natLor, [`Ix.Kernel.PinGen.lorRecCert, `Ix.Kernel.PinGen.lorBaseCert]),
   (.natXor, [`Ix.Kernel.PinGen.xorRecCert, `Ix.Kernel.PinGen.xorBaseCert]),
   (.natShiftLeft, [`Ix.Kernel.PinGen.shiftLeftRecCert, `Ix.Kernel.PinGen.shiftLeftBaseCert]),
   (.natShiftRight, [`Ix.Kernel.PinGen.shiftRightRecCert, `Ix.Kernel.PinGen.shiftRightBaseCert])]

/-- The structural operations: their evidence is one `defeq` entry per
recurrence equation. -/
def defeqRoles : List Ix.Kernel.Role :=
  [.natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq, .natBle]

/-- The `defeq` evidence of a structural operation, one entry per equation of
its specification. -/
def defeqEvidence {K : Type} (r : Ix.Kernel.Role) : List (Ix.Kernel.Evidence K) :=
  (Ix.Kernel.natOpEquations (md := .anon) 0 (Ix.Kernel.roleKey r)).map fun _ => .defeq

/-- A key's Lean name: its spelling (`Ix.Kernel.Key.toName`). -/
def toLeanName (k : CName md) : Lean.Name := go k.toName
where
  go : Ix.Kernel.Name → Lean.Name
    | .anonymous => .anonymous
    | .str p s => .str (go p) s
    | .num p n => .num (go p) n

/-- The key of a Lean name under Source mode's binding (`Ix.Kernel.Key.ofName`). -/
def ofLeanName (n : Lean.Name) : CName md := Ix.Kernel.Key.ofName (Ix.Kernel.Name.ofLeanName n)

/-! ## The declarations read so far, as the closure sees them -/

/-- What the inliner needs about the declarations read: the values of the
definitions, theorems and opaques (with their level parameters), and the
parameter counts of the constructors. -/
structure Universe (md : Ix.Kernel.Mode) where
  values : Std.HashMap (CName md) (List LevelParam × CExpr md) := {}
  ctorParams : Std.HashMap (CName md) Nat := {}

def Universe.add (u : Universe md) (d : CDecl md) : Universe md :=
  match d with
  | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
    { u with values := u.values.insert cv.name (cv.levelParams, v) }
  | .indDecl block _ => block.foldl (fun u ci => match ci with
      | .ctorInfo cv nP _ => { u with ctorParams := u.ctorParams.insert cv.name nP }
      | _ => u) u
  | _ => u

/-- The constants a declaration installs, as the fold stores them (raw:
before annotation; an opaque as an axiom, without its value). -/
def declInfos (d : CDecl md) : List (Ix.Kernel.ConstantInfo md) :=
  match d with
  | .axiomDecl cv => [.axiomInfo cv]
  | .defnDecl cv v hint => [.defnInfo cv v hint]
  | .thmDecl cv v => [.thmInfo cv v]
  | .opaqueDecl cv _ => [.axiomInfo cv]
  | .basisDecl kind => kind.declsA
  | .indDecl block _ => block
  | .quotDecl _ cv => [.axiomInfo cv]

/-- A lookup over the declarations read so far. -/
def lookupOf (decls : Array (CDecl md)) : Std.HashMap (CName md) (Ix.Kernel.ConstantInfo md) :=
  decls.foldl (fun m d => (declInfos d).foldl (fun m ci => m.insert ci.name ci) m) {}

/-- **What a proof of operation `op` may mention**: the dependency closure of
`op`'s value and of its dependencies' roles (`Ix.Kernel.evidenceLocal`'s), and
`op` itself (its self-references, which the fold replaces by the value). -/
def allowedFor (look : CName md → Option (Ix.Kernel.ConstantInfo md)) (op : CName md) (opValue : CExpr md) :
    Std.HashSet (CName md) :=
  (Ix.Kernel.refClosureGo look Ix.Kernel.walkFuel
    (opValue.constKeys.toList ++ Ix.Kernel.evidenceDepKeys op) {}).insert op

/-! ## Expression surgery (memoized over the DAG) -/

abbrev Memo (md : Ix.Kernel.Mode) := Std.HashMap (CExpr md) (CExpr md)

/-- The level parameters `ks` instantiated by `us`. -/
partial def instLevelsGo (ks : List LevelParam) (us : List CLevel) (e : CExpr md) :
    StateM (Memo md) (CExpr md) := do
  if !e.hasLP then return e
  if let some r := (← get)[e]? then return r
  let r ← match e with
    | .sort u => pure (.sort (Ix.Kernel.Level.subst ks us u))
    | .const n ls => pure (.const n (ls.map (Ix.Kernel.Level.subst ks us)))
    | .app f a => return .app (← instLevelsGo ks us f) (← instLevelsGo ks us a)
    | .lam t b m => return .lam (← instLevelsGo ks us t) (← instLevelsGo ks us b) m
    | .forallE t b m => return .forallE (← instLevelsGo ks us t) (← instLevelsGo ks us b) m
    | .letE t v b l =>
      return .letE (← instLevelsGo ks us t) (← instLevelsGo ks us v) (← instLevelsGo ks us b) l
    | .proj s i x => return .proj s i (← instLevelsGo ks us x)
    | .fvar i t => return .fvar i (← instLevelsGo ks us t)
    | e => pure e
  modify (·.insert e r)
  return r

def instLevels (ks : List LevelParam) (us : List CLevel) (e : CExpr md) : CExpr md :=
  if ks.isEmpty then e else (instLevelsGo ks us e |>.run {}).1

/-- No loose `bvar` at or above `d`. -/
def closedAbove (e : CExpr md) (d : Nat) : Bool :=
  e.bvarBRaw < Ix.Kernel.satRange && e.bvarBRaw ≤ d

/-- `e` with loose `bvar (d + k)` replaced by `vs[n - 1 - k]` (lifted past the
`d` binders crossed) for `k < n = vs.size`, and the loose `bvar`s above
lowered by `n`: Lean's `instantiate` of the reversed `vs`, so `vs[n - 1]` is
`bvar 0`. -/
partial def instGo (vs : Array (CExpr md)) (d : Nat) (e : CExpr md) :
    StateM (Std.HashMap (CExpr md × Nat) (CExpr md)) (CExpr md) := do
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
    | .letE t v b l => return .letE (← instGo vs d t) (← instGo vs d v) (← instGo vs (d + 1) b) l
    | .proj s i x => return .proj s i (← instGo vs d x)
    | e => pure e
  modify (·.insert (e, d) r)
  return r

def instantiate (e : CExpr md) (vs : Array (CExpr md)) : CExpr md :=
  if vs.isEmpty then e else (instGo vs 0 e |>.run {}).1

/-- The number of leading `fun` binders of `f`, at most `k`, and the body
under them. -/
def peelLams : Nat → CExpr md → Nat × CExpr md
  | k + 1, .lam _ b _ => let (m, body) := peelLams k b; (m + 1, body)
  | _, e => (0, e)

/-- `f args`, beta-reduced at the head. -/
def betaApp (f : CExpr md) (args : Array (CExpr md)) : CExpr md :=
  let (m, body) := peelLams args.size f
  let head := if m == 0 then f else instantiate body (args.extract 0 m)
  (args.extract m args.size).foldl .app head

/-- One pass: every constant `inline` selects that has a value is replaced by
it (levels instantiated, beta-reduced against its arguments), and the result
is visited again (upstream's `unfoldStep` under `Core.transform`). -/
partial def unfoldGo (u : Universe md) (inline : CName md → Bool) (e : CExpr md) : StateM (Memo md) (CExpr md) := do
  if let some r := (← get)[e]? then return r
  let unfolded : Option (CExpr md) := match e.getAppFn with
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
      | .letE t v b l =>
        return .letE (← unfoldGo u inline t) (← unfoldGo u inline v) (← unfoldGo u inline b) l
      | .proj s i x => return .proj s i (← unfoldGo u inline x)
      | e => pure e
  modify (·.insert e r)
  return r

/-- A projection of a constructor application: its field. -/
def projOfCtor (u : Universe md) (i : Nat) (x : CExpr md) : Option (CExpr md) :=
  match x.getAppFn with
  | .const c _ => do
    let nP ← u.ctorParams[c]?
    let args := x.getAppArgs.toArray
    if h : nP + i < args.size then some args[nP + i] else none
  | _ => none

/-- One pass of beta, `let` (zeta) and projection-of-constructor reduction
(upstream's `simpStep`, and the zeta-expansion of its `toConLeche`), each
result visited again. -/
partial def simpGo (u : Universe md) (e : CExpr md) : StateM (Memo md) (CExpr md) := do
  if let some r := (← get)[e]? then return r
  let reduced : Option (CExpr md) := match e with
    | .letE _ v b _ => some (instantiate b #[v])
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

/-- **A proof closed over `allowed`** (upstream's `inlineCertClosure`):
unfold and simplify to a fixpoint, then require every remaining constant to
be allowed. -/
def closeProof (u : Universe md) (allowed : CName md → Bool) (e : CExpr md) : Except String (CExpr md) := do
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
  let bad := e.constKeys.toList.filter (!allowed ·)
  unless bad.isEmpty do
    throw s!"residual constants outside the operation's dependency closure \
      (name, has a value): {bad.map fun n => (n, (u.values[n]?).isSome)}"
  return e

/-! ## Evidence from declarations -/

/-- The value of the definition `name` among `decls`. -/
def valueOf (decls : Array (CDecl md)) (name : CName md) : Option (CExpr md) :=
  decls.findSome? fun
    | .defnDecl cv v _ => if cv.name == name then some v else none
    | _ => none

/-- The value of the theorem `name` among `decls`. -/
def theoremOf (decls : Array (CDecl md)) (name : CName md) : Option (CExpr md) :=
  decls.findSome? fun
    | .thmDecl cv v => if cv.name == name then some v else none
    | _ => none

/-- **One well-founded operation's proof evidence, from declarations**: its
certificate theorems (`certTheorems`, under `key`'s naming), each closed over
the operation's dependency closure. -/
def closedProofs (decls : Array (CDecl md)) (uni : Universe md)
    (look : CName md → Option (Ix.Kernel.ConstantInfo md)) (key : Lean.Name → CName md)
    (r : Ix.Kernel.Role) : Except String (List (CName md × CExpr md)) := do
  let op := Ix.Kernel.roleKey r
  let some opValue := valueOf decls op | throw s!"{op} is not a definition here"
  let allowed := allowedFor look op opValue
  let thms := ((certTheorems.find? (·.1 == r)).map (·.2)).getD []
  thms.mapM fun t => do
    let k := key t
    let some v := theoremOf decls k | throw s!"{k} is not a theorem here"
    let p ← (closeProof uni allowed.contains v).mapError (s!"{k}: " ++ ·)
    pure (k, p)

end Ix.RoleEvidence
