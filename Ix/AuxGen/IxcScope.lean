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
  pure { s with fvarLevels := s.fvarLevels.insert name i, locals := s.locals.push (.fvar i ty') }

/-- Push a telescope, outermost first. -/
def push (s : Scope) (locals : Array (Name × Expr)) : Except String Scope :=
  locals.foldlM push1 s

/-- Pop the most recently pushed `k` locals. -/
def pop (s : Scope) (k : Nat) : Except String Scope := do
  if k > s.depth then throw s!"pop of {k} locals from a context of {s.depth}"
  let keep := s.depth - k
  let fvarLevels := s.fvarLevels.fold (init := {}) fun m name i =>
    if i < keep then m.insert name i else m
  pure { s with fvarLevels, locals := s.locals.extract 0 keep }

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

end Scope

/-- **The scope as an `OracleScope`**, with `fuel` operations left. -/
def ofScope (get? : Name → Option ConstantInfo) : Nat → Scope → OracleScope
  | 0, _ =>
    .mk (fun _ => .error "scope fuel exhausted") (fun _ => .error "scope fuel exhausted")
      (fun _ => .error "scope fuel exhausted")
  | n + 1, s =>
    .mk
      (fun ty => (s.getLevel get? ty).map fun (l, fast, s') => (l, fast, ofScope get? n s'))
      (fun locals => (s.push locals).map (ofScope get? n))
      (fun k => (s.pop k).map (ofScope get? n))

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

/-- **One block's oracle** over a service, given lazily (`svc ()` is asked at
the first question; the drivers' snapshot is a task), in `mode`, with `fuel`
flat-block installs left. -/
def oracleOf (mode : IxcMode) : Nat → (Unit → Except String Service) → AuxOracle
  | 0, _ =>
    .mk mode (fun _ _ => .error "oracle fuel exhausted") (fun _ _ _ => .error "oracle fuel exhausted")
  | n + 1, svc =>
    .mk mode
      (fun lps locals => do
        let svc ← svc ()
        let s ← Scope.new svc.env lps
        let s ← s.push locals
        pure (ofScope svc.input.get? scopeFuel s))
      (fun classes originalAll canonicalRecs => do
        let svc ← svc ()
        match ← installOwnFlat svc classes originalAll canonicalRecs with
        | none => pure none
        | some svc' => pure (some (oracleOf mode n fun _ => .ok svc')))

/-- The oracle over the snapshot `run` (a run of the drivers' service). -/
def oracleOfRun (mode : IxcMode) (run : Unit → Source.Run) : AuxOracle :=
  oracleOf mode oracleFuel fun _ => (run ()).service

end Ix.AuxGen.Ixc

end
