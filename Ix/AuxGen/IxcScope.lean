/-
  Ix.AuxGen.IxcScope: AuxGen's level questions answered by IxC Source mode
  over the Source service (AuxGen on IxC, M2a; AUXGEN-IXC §3.3; the plan is
  `auxgen-m2.md` §1.3). It builds the closures of `Ix.AuxGen.Oracle`.

  ## The scope

  A `Scope` is a local context over a Source environment (`SourceEnv`: the
  verified fold, its evidence, and the class map σ):
  * **Terms in.** A Lean term over the context goes through the Source
    ingress's own conversion, with nothing copied: its free variables are
    abstracted into loose bound variables (`batchAbstractWith`, the local at
    level `i` of `n` becomes `bvar (n - 1 - i)`); the term goes through σ and
    the shared `ingressExprs` (`SourceEnv.ingress`), which refuses any other
    free variable, metavariable or unknown level parameter; the loose bound
    variables are then instantiated with the locals, IxC's
    `.fvar i (annotated type)`. Level parameters are numbered by position in
    the context's `lps`.
  * **Locals** are annotated once, when pushed, at their own depth (IxC
    checks binder data).
  * **`getLevel`** is the `inferAppType` fast path where it applies (below),
    else `annotate`, `infer`, `ensureSort` in IxC's cached checker
    (`coreKnotI .verified`, fuel `checkFuel`; running out is a refusal). The
    level goes out as `Ix.Tc` would have built it (`Egress.egressLevel`), and
    a ∀'s level is `levelNormalize`d, as `Ix.Tc`'s `getLevel` does.

  ## The fast path

  `Ix.Tc`'s `getLevel` first tries `inferAppType`'s shortcut: a constant
  applied to as many arguments as its type has leading ∀s, whose body is a
  sort, has that sort's level with the arguments' levels substituted
  (`tryInferAppSortLevel`). The spelling of Lean's own auxiliaries depends on
  it. Here it reads the head's **Lean type** (the input's, through the
  service's lookups), rebuilt as `Ix.Tc`'s ingress rebuilds a level
  (`Egress.normalize`), and substitutes with `Ix.Tc`'s rules
  (`kunivToLevelWithConstLevels`). It never reads IxC's environment, so the
  level spelling the Source environment holds cannot change it.

  ## The oracle

  `oracleOf` builds one block's `AuxOracle` over a service snapshot, given
  lazily (the drivers' snapshot is a task that the first question waits
  for). `withFlat` installs the block's own canonical flat block
  (`Service.installFlat`) when the block's layout is not Lean's.

  Nothing here is trusted: every answer comes from IxC's verified checker over
  declarations the verified fold accepted, and an answer it cannot give is a
  refusal.
-/
module
public import Ix.AuxGen.Oracle
public import Ix.AuxGen.SourceService
public import Ix.AuxGen.LevelEgress
public import Ix.AuxGen.Levels
public section

namespace Ix.AuxGen.Ixc

open Ix.AuxGen.Source (SourceEnv Service renderCheck)

/-- The fuel of one scope chain: operations on a scope and the scopes it
returns. -/
def scopeFuel : Nat := 1000000

/-- The fuel of one oracle chain: flat-block installs. -/
def oracleFuel : Nat := 4

/-! ## The fast path -/

/-- `Ix.Tc`'s `isNotZeroLevel`. -/
def isNotZero : Level → Bool
  | .succ _ _ => true
  | .max a b _ => isNotZero a || isNotZero b
  | .imax _ b _ => isNotZero b
  | _ => false

/-- `Ix.Tc`'s `kunivToLevelWithConstLevels` on a Lean level in `Ix.Tc`'s
shape (`Egress.normalize`): the head constant's level parameter `cLps[i]` is
its argument `us[i]`, `max` through `levelMax`, `imax` by Lean's `mk_imax`
rules. A parameter that is not the head's, or has no argument, is refused. -/
def constLevelSubst (cLps : Array Name) (us : Array Level) : Level → Except String Level
  | .zero _ => pure Level.mkZero
  | .succ u _ => return Level.mkSucc (← constLevelSubst cLps us u)
  | .max a b _ => return levelMax (← constLevelSubst cLps us a) (← constLevelSubst cLps us b)
  | .imax a b _ => do
    let la ← constLevelSubst cLps us a
    let lb ← constLevelSubst cLps us b
    return if isNotZero lb then levelMax la lb
      else if lb matches .zero _ then lb
      else if la matches .zero _ then lb
      else if la matches .succ (.zero _) _ then lb
      else if la == lb then la
      else Level.mkIMax la lb
  | .param n _ =>
    match cLps.findIdx? (· == n) with
    | some i =>
      match us[i]? with
      | some l => pure l
      | none => throw s!"fast path: constant universe argument index {i} out of range"
    | none => throw s!"fast path: level parameter {n.pretty} is not the head constant's"
  | .mvar _ _ => throw "fast path: level metavariable"

/-- A term with its metadata wrappers removed. -/
def stripMData : Expr → Expr
  | .mdata _ e _ => stripMData e
  | e => e

/-- **The `inferAppType` fast path** on the head's Lean type: `some` level
when `ty` is a constant applied to as many arguments as its type has leading
∀s and the body is a sort. -/
def fastLevel (get? : Name → Option ConstantInfo) (ty : Expr) : Except String (Option Level) := do
  let (head, args) := decomposeApps ty
  let .const name us _ := head | return none
  let some ci := get? name | return none
  let cv := ci.getCnst
  let mut cur := stripMData cv.type
  for _ in [0:args.size] do
    match cur with
    | .forallE _ _ body _ _ => cur := stripMData body
    | _ => return none
  let .sort u _ := cur | return none
  return some (← constLevelSubst cv.levelParams us (Egress.normalize u))

/-! ## The scope -/

/-- **A local context over a Source environment.** Locals are numbered by
level, outermost `0`, as IxC's `fvar`s are; `locals[i]` is `.fvar i ty` with
the local's annotated type. -/
structure Scope where
  env : SourceEnv
  lps : Array Name
  fvarLevels : Std.HashMap Name Nat := {}
  locals : Array (Ix.Kernel.Expr .source) := #[]
  /-- each local's name, by level (the egress's free variables) -/
  names : Array Name := #[]
  cs : Ix.Kernel.Cached.CState .source := {}

namespace Scope

def depth (s : Scope) : Nat := s.locals.size

/-- One action of IxC's cached checker over the scope's environment, with the
scope's memo state. -/
def run (s : Scope)
    (act : Ix.Kernel.Cached.CoreFnsI .source → Ix.Kernel.Cached.CheckCM .source α) :
    Except String (α × Scope) :=
  match (act (Ix.Kernel.Cached.coreKnotI .verified s.env.fold.fe Ix.Kernel.checkFuel)).run s.cs with
  | .ok (a, cs) => .ok (a, { s with cs })
  | .error e => .error (renderCheck e)

/-- **A Lean term over the context as an IxC term**: free variables
abstracted, the Source ingress through σ, the loose bound variables
instantiated with the locals. -/
def term (s : Scope) (e : Expr) : Except String (Ix.Kernel.Expr .source) := do
  let n := s.depth
  let closed := batchAbstractWith s.fvarLevels.get? e n 0
  match s.env.ingress s.lps [closed] with
  | .ok [k] => pure (k.instantiateList s.locals.reverse.toList)
  | .ok _ => throw "ingress: arity"
  | .error err => throw s!"ingress: {err}"

/-- Push one local: its domain over the context, annotated at its depth. A
name already in the context is refused. -/
def push1 (s : Scope) (loc : Name × Expr) : Except String Scope := do
  let (name, domain) := loc
  if s.fvarLevels.contains name then throw s!"duplicate free variable {name.pretty}"
  let i := s.depth
  let ty ← s.term domain
  let (ty', s) ← s.run fun r => r.annotate i ty
  pure { s with fvarLevels := s.fvarLevels.insert name i, locals := s.locals.push (.fvar i ty'),
                names := s.names.push name }

/-- Push a telescope, outermost first. -/
def push (s : Scope) (locals : Array (Name × Expr)) : Except String Scope :=
  locals.foldlM push1 s

/-- Pop the most recently pushed `k` locals. -/
def pop (s : Scope) (k : Nat) : Except String Scope := do
  if k > s.depth then throw s!"pop of {k} locals from a context of {s.depth}"
  let keep := s.depth - k
  let fvarLevels := s.fvarLevels.fold (init := {}) fun m name i =>
    if i < keep then m.insert name i else m
  pure { s with fvarLevels, locals := s.locals.extract 0 keep, names := s.names.extract 0 keep }

/-- A context over `lps` with no locals; duplicate level parameters are
refused. -/
def new (env : SourceEnv) (lps : Array Name) : Except String Scope := do
  let mut seen : Std.HashSet Name := {}
  for n in lps do
    if seen.contains n then throw s!"duplicate universe parameter {n.pretty}"
    seen := seen.insert n
  pure { env, lps }

/-- The level of a type by IxC's checker: `annotate`, `infer`, `ensureSort`;
the level as `Ix.Tc` builds it, `levelNormalize`d for a ∀. -/
def slowLevel (s : Scope) (ty : Expr) : Except String (Level × Scope) := do
  let d := s.depth
  let e ← s.term ty
  let (u, s) ← s.run fun r => do
    let e' ← r.annotate d e
    let t ← r.infer d e'
    Ix.Kernel.Cached.ensureSortI r d t
  let l ← (Egress.egressLevel s.lps u).mapError toString
  if ty matches .forallE .. then return (levelNormalize l, s)
  return (l, s)

/-- **The sort level of a type**: the fast path on the head's Lean type, else
IxC's checker. -/
def getLevel (get? : Name → Option ConstantInfo) (s : Scope) (ty : Expr) :
    Except String (Level × Bool × Scope) := do
  if let some l ← fastLevel get? ty then return (l, true, s)
  let (l, s) ← s.slowLevel ty
  return (l, false, s)

/-! ### Terms out, decision-grade (AuxGen M3)

`.brecOn.eq`'s unit-like test reads `inferType?` and `whnf?` results to
decide between `Eq` and `HEq`, and never emits them (the `AuxKernel`
contract's clause 6). So an IxC result goes out as a term that denotes the
same value over the context, and nothing more:
- a free variable is its local's name;
- a constant is its Source key's Lean name (`.id n` as `n`, `.role r` as
  `r`'s Lean name), a fresh name (`Flat.fresh n`: a flat block's member, an
  admitted `.below`) as the `n` it is fresh for, which `term` sends back
  through σ; so the generator's lookups (`lookupConst?` on the head) see the
  names `Ix.Tc` gives; a derived key (`.aux`) is refused;
- levels are spelled as `Ix.Tc` builds them (`Egress.egressLevel`);
- binder names are anonymous, binder information default.
The result re-enters through `term`, as the generator passes `inferType?`'s
answer back to `whnf?` and `isDefEq?`. -/

/-- An IxC name as an `Ix.Name`: `ingressName`'s inverse, with a fresh name's
reserved root dropped (`Flat.fresh`'s inverse; no input name has the root). -/
def egressName : Ix.Kernel.Name → Name
  | .anonymous => Name.mkAnon
  | .str .anonymous s => if s == Flat.freshRoot then Name.mkAnon else Name.mkStr Name.mkAnon s
  | .str p s => Name.mkStr (egressName p) s
  | .num p n => Name.mkNat (egressName p) n

/-- A Source key's Lean name. -/
def egressKey : Ix.Kernel.Key .source → Except String Name
  | .id n => pure (egressName n)
  | .role r => pure (egressName r.leanName)
  | .aux _ _ => throw "egress: a derived key has no Lean name"

/-- **An IxC term over the context as a Lean term**, decision-grade. -/
def egress (s : Scope) : Ix.Kernel.Expr .source → Except String Expr
  | .bvar i => pure (Expr.mkBVar i)
  | .fvar i _ =>
    match s.names[i]? with
    | some n => pure (Expr.mkFVar n)
    | none => throw s!"egress: free variable {i} beyond the context's {s.names.size}"
  | .sort u => return Expr.mkSort (← (Egress.egressLevel s.lps u).mapError toString)
  | .const k us => do
    let us ← us.toArray.mapM fun u => (Egress.egressLevel s.lps u).mapError toString
    return Expr.mkConst (← egressKey k) us
  | .app f a => return Expr.mkApp (← s.egress f) (← s.egress a)
  | .lam t b _ => return Expr.mkLam Name.mkAnon (← s.egress t) (← s.egress b) .default
  | .forallE t b _ => return Expr.mkForallE Name.mkAnon (← s.egress t) (← s.egress b) .default
  | .letE t v b _ =>
    return Expr.mkLetE Name.mkAnon (← s.egress t) (← s.egress v) (← s.egress b) false
  | .lit (.natVal n) => pure (Expr.mkLit (.natVal n))
  | .lit (.strVal str) => pure (Expr.mkLit (.strVal str))
  | .proj k i e => return Expr.mkProj (← egressKey k) i (← s.egress e)

/-- The type of a term, decision-grade: `annotate`, `infer`, out. -/
def inferExpr (s : Scope) (e : Expr) : Except String (Expr × Scope) := do
  let d := s.depth
  let k ← s.term e
  let (t, s) ← s.run fun r => do
    let k' ← r.annotate d k
    r.infer d k'
  return (← s.egress t, s)

/-- The weak head normal form of a term, decision-grade: `annotate`, `whnf`,
out. -/
def whnfExpr (s : Scope) (e : Expr) : Except String (Expr × Scope) := do
  let d := s.depth
  let k ← s.term e
  let (w, s) ← s.run fun r => do
    let k' ← r.annotate d k
    r.whnf d k'
  return (← s.egress w, s)

/-- Definitional equality of two terms: both annotated, then IxC's `defeq`. -/
def defEq (s : Scope) (a b : Expr) : Except String (Bool × Scope) := do
  let d := s.depth
  let ka ← s.term a
  let kb ← s.term b
  s.run fun r => do
    let a' ← r.annotate d ka
    let b' ← r.annotate d kb
    r.defeq d a' b'

end Scope

/-- **The scope as an `OracleScope`**, with `fuel` operations left. -/
def ofScope (get? : Name → Option ConstantInfo) : Nat → Scope → OracleScope
  | 0, _ =>
    let out {α} : Except String α := .error "scope fuel exhausted"
    .mk (fun _ => out) (fun _ => out) (fun _ => out) (fun _ => out) (fun _ => out) (fun _ _ => out)
  | n + 1, s =>
    .mk
      (fun ty => (s.getLevel get? ty).map fun (l, fast, s') => (l, fast, ofScope get? n s'))
      (fun locals => (s.push locals).map (ofScope get? n))
      (fun k => (s.pop k).map (ofScope get? n))
      (fun e => (s.inferExpr e).map fun (t, s') => (t, ofScope get? n s'))
      (fun e => (s.whnfExpr e).map fun (w, s') => (w, ofScope get? n s'))
      (fun a b => (s.defEq a b).map fun (q, s') => (q, ofScope get? n s'))

/-! ## The oracle -/

/-- The block's own canonical flat block, installed when its layout is not
Lean's: the service after it, or `none`. The flat block is built as the
fixture test builds it (`Flat.build` over the input's lookups and the σ of
the blocks installed before), and lowered and installed by the service
(`Service.installFlat`); a refusal is an error naming its reason. -/
def installOwnFlat (svc : Service) (classes : Array (Array Name)) (originalAll : Array Name)
    (canonicalRecs : Array (Name × RecursorVal)) : Except String (Option Service) := do
  let nClasses := classes.size
  let auxNames := (canonicalRecs.extract nClasses canonicalRecs.size).map (·.1)
  let leanNested := match originalAll[0]?.bind svc.input.get? with
    | some (.inductInfo v) => v.numNested
    | _ => 0
  unless Flat.needed classes originalAll auxNames leanNested do return none
  let fb ← (Flat.build svc.input.get? classes canonicalRecs svc.sigma).mapError (·.render)
  let svc := svc.installFlat fb
  match svc.flatStatus? (fb.firstName.getD default) with
  | some .accepted => return some svc
  | some (.refused why) => throw s!"flat block refused: {why}"
  | _ => throw "flat block not recorded"

/-- The block's generated Type-level `.below` definitions made visible
(AuxGen M3, the `AuxKernel` contract's clause 9), on the block's copy of
the service: each admitted through σ under its fresh name
(`Service.admitDefinition`), as `Ix.Tc`'s kenv takes the generated
definition at its name. The service after them, and how many were admitted
and refused. -/
def admitBelowIn (svc : Service) (defs : Array BelowDef) : Service × Nat × Nat := Id.run do
  let mut svc := svc
  let mut ok := 0
  let mut bad := 0
  for d in defs do
    let (svc', st) := svc.admitDefinition d.name d.levelParams d.typ d.value (thm := false)
    svc := svc'
    if st.isAccepted then ok := ok + 1 else bad := bad + 1
  return (svc, ok, bad)

/-- **One block's oracle** over a service, given lazily (`svc ()` is asked at
the first question; the drivers' snapshot is a task), in `mode` (tracing the
tail's counts under `trace`), with `fuel` installs left (the flat block, the
generated `.below`). -/
def oracleOf (mode : IxcMode) (trace : Bool) : Nat → (Unit → Except String Service) → AuxOracle
  | 0, _ =>
    .mk mode trace (fun _ _ => .error "oracle fuel exhausted")
      (fun _ _ _ => .error "oracle fuel exhausted") (fun _ => .error "oracle fuel exhausted")
  | n + 1, svc =>
    .mk mode trace
      (fun lps locals => do
        let svc ← svc ()
        let s ← Scope.new svc.env lps
        let s ← s.push locals
        pure (ofScope svc.input.get? scopeFuel s))
      (fun classes originalAll canonicalRecs => do
        let svc ← svc ()
        match ← installOwnFlat svc classes originalAll canonicalRecs with
        | none => pure none
        | some svc' => pure (some (oracleOf mode trace n fun _ => .ok svc')))
      (fun defs => do
        let svc ← svc ()
        let (svc', ok, bad) := admitBelowIn svc defs
        pure (oracleOf mode trace n fun _ => .ok svc', ok, bad))

/-- **One block's oracle over the snapshot `run`** (a run of the drivers'
service), with the block's `members` folded first (`Service.ensureNames`): a
no-op when the run asked for the block, and otherwise its groups and what they
depend on, folded on this block's copy of the snapshot, so a block the asks
did not select is still answered. The service is taken once, at the first
question, and shared by the block's scopes. `trace`: the tail traces its
counts. -/
def oracleOfRun (mode : IxcMode) (trace : Bool) (run : Unit → Source.Run) (members : Array Name) :
    AuxOracle :=
  let svc : Thunk (Except String Service) :=
    Thunk.mk fun _ => (run ()).service.map (·.ensureNames members)
  oracleOf mode trace oracleFuel fun _ => svc.get

end Ix.AuxGen.Ixc

end
