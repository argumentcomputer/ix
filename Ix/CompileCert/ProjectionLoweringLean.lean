import Ix.CompileCert.SourceNormalization

/-! # Lowering equations on the Lean side (untrusted producer)

For a projection function `f : ∀ p⃗ (self : T p⃗), R` with Lean value
`fun p⃗ self => .proj T i self`, `buildLoweringWitness` builds, in `MetaM` over
the host environment:

* the lowered value `fun p⃗ (self : T p⃗) => T.rec.{ℓ, u⃗} p⃗ motives… minors… self`
  exactly as `Ix.Kernel.Frontend.projRecValue` builds it (the motive for `T` is
  `fun t => R[self := t]`, the others `PUnit.{ℓ}`; the minor for `T`'s
  constructor returns field `i`, the others `PUnit.unit.{ℓ}`; every binder read
  off `T.rec`'s own type), with `ℓ` **inferred** as the sort of `R`
  (`Meta.getLevel`);
* the theorem `f._ix_projection_lowering :
  ∀ p⃗ (self : T p⃗), @Eq.{ℓ} R (f p⃗ self) (lowered p⃗ self)`, proved by
  `T.casesOn` on `self` with the minor `fun fs => Eq.refl (f p⃗ (C p⃗ fs))`.

`admitLoweringWitness` submits the theorem to Lean's kernel
(`Lean.Environment.addDeclCore` with checking on). Nothing here is trusted: the
lane's `checkSourceProjectionLowering` decides the receipt, and the theorem
counts only once Lean's kernel has accepted it. `LoweringTamper` builds the
negative controls of the tests. -/

namespace Ix.CompileCert.LoweringLean

open Lean Meta

/-- Deliberate defects, for negative controls only. -/
inductive LoweringTamper where
  | none
  /-- the `T` minor returns another field -/
  | field (index : Nat)
  /-- the elimination level and the `Eq` level both one universe higher -/
  | level
  /-- only the recursor's elimination level one universe higher -/
  | recLevel
  /-- the subject's binder domain `T p⃗` spelled as `id (T p⃗)` (convertible, not syntactic) -/
  | domain
  deriving Inhabited, BEq

/-- Leading `∀` binders (name, domain, info), outermost first, and the body; domains
keep their loose bound variables, as `Ix.Kernel.Frontend.stripPisAll` does. -/
def stripForalls : Lean.Expr → List (Lean.Name × Lean.Expr × Lean.BinderInfo) × Lean.Expr
  | .forallE n d b bi =>
    let (bs, e) := stripForalls b
    ((n, d, bi) :: bs, e)
  | e => ([], e)

def mkLams (bs : List (Lean.Name × Lean.Expr × Lean.BinderInfo)) (body : Lean.Expr) : Lean.Expr :=
  bs.foldr (fun (n, d, bi) acc => .lam n d acc bi) body

def headIs (name : Lean.Name) (e : Lean.Expr) : Bool := e.getAppFn.isConstOf name

/-- Instantiate `k` leading binders one at a time with terms built from each domain. -/
def buildBinders (mk : Lean.Expr → MetaM Lean.Expr) : Nat → Lean.Expr → MetaM (List Lean.Expr × Lean.Expr)
  | 0, e => pure ([], e)
  | k + 1, .forallE _ dom body _ => do
    let t ← mk dom
    let (ts, rest) ← buildBinders mk k (body.instantiate1 t)
    pure (t :: ts, rest)
  | _ + 1, _ => throwError "recursor type has too few binders"

def instantiateForallsWith (e : Lean.Expr) : List Lean.Expr → MetaM Lean.Expr
  | [] => pure e
  | a :: as => match e with
    | .forallE _ _ body _ => instantiateForallsWith (body.instantiate1 a) as
    | _ => throwError "type has too few binders"

/-- The lowered value and the lowering equation of projection function `f`. -/
def buildLoweringWitness (f : Lean.Name) (tamper : LoweringTamper := .none) : MetaM Lean.TheoremVal := do
  let env ← getEnv
  let some d := env.find? f | throwError "{f} is not in the environment"
  let some sourceValue := projectionSourceValue d | throwError "{f} is not a definition or theorem"
  let some (owner, field, binders) := sourceProjectionBody sourceValue
    | throwError "{f} is not a projection function"
  let some (.inductInfo T) := env.find? owner | throwError "{owner} is not an inductive type"
  let [ctorName] := T.ctors | throwError "{owner} is not structure-like (not one constructor)"
  unless T.numIndices == 0 do throwError "{owner} is not structure-like (indexed)"
  let nP := T.numParams
  unless binders == nP + 1 do throwError "{f} has {binders} binders, expected {nP + 1}"
  let some (.recInfo rec) := env.find? (owner.str "rec") | throwError "{owner} has no recursor"
  unless rec.levelParams.length == T.levelParams.length + 1 do
    throwError "{owner}.rec has no elimination level parameter"
  unless d.levelParams == T.levelParams do
    throwError "{f} and {owner} have different universe telescopes"
  let casesOnName := owner.str "casesOn"
  let some casesOn := env.find? casesOnName | throwError "{owner} has no casesOn"
  let us := T.levelParams.map Lean.Level.param
  let field := match tamper with
    | .field index => index
    | _ => field
  forallBoundedTelescope d.type (some (nP + 1)) fun xs R => do
    unless xs.size == nP + 1 do throwError "{f}'s type has fewer than {nP + 1} binders"
    let params := (xs.extract 0 nP).toList
    let self := xs[nP]!
    let inferred ← getLevel R
    let eqLevel := match tamper with
      | .level => inferred.succ
      | _ => inferred
    let ℓ := match tamper with
      | .level | .recLevel => inferred.succ
      | _ => inferred
    let recType ← instantiateForallsWith
      (rec.type.instantiateLevelParams rec.levelParams (ℓ :: us)) params
    let motiveBody := R.abstract #[self]
    let mkMotive : Lean.Expr → MetaM Lean.Expr := fun dom =>
      match stripForalls dom with
      | ([(n, dd, bi)], .sort _) =>
        if headIs owner dd then pure (.lam n dd motiveBody bi)
        else pure (.lam n dd (.const ``PUnit [ℓ]) bi)
      | (bs, .sort _) => pure (mkLams bs (.const ``PUnit [ℓ]))
      | _ => throwError "recursor motive domain is not a sort-valued telescope"
    let (motives, recType) ← buildBinders mkMotive rec.numMotives recType
    let mkMinor : Lean.Expr → MetaM Lean.Expr := fun dom => do
      let (bs, cod) := stripForalls dom
      let some major := cod.getAppArgs.back? | throwError "recursor minor has no major"
      if headIs ctorName major then
        if field < bs.length then pure (mkLams bs (.bvar (bs.length - 1 - field)))
        else throwError "field {field} out of range"
      else pure (mkLams bs (.const ``PUnit.unit [ℓ]))
    let (minors, recType) ← buildBinders mkMinor rec.numMinors recType
    let .forallE _ majorDomain _ _ := recType | throwError "recursor has no major premise"
    unless headIs owner majorDomain do throwError "recursor major premise has another owner"
    let app := mkAppN (.const rec.name (ℓ :: us)) (params ++ motives ++ minors ++ [self]).toArray
    let lowered ← match tamper with
      | .domain => do
        let selfType ← inferType self
        let spelled ← mkAppM ``id #[selfType]
        mkLambdaFVars (xs.extract 0 nP) (.lam `self spelled (app.abstract #[self]) .default)
      | _ => mkLambdaFVars xs app
    let fConst := Lean.Expr.const f (d.levelParams.map Lean.Level.param)
    let statementBody := mkApp3 (.const ``Eq [eqLevel]) R (mkAppN fConst xs) (mkAppN lowered xs)
    let type ← mkForallFVars xs statementBody
    -- the proof: `T.casesOn` on `self`; on a constructor both sides reduce to the field
    let selfType ← inferType self
    let motiveP ← withLocalDeclD `t selfType fun t => do
      mkLambdaFVars #[t] (mkApp3 (.const ``Eq [eqLevel]) (R.replaceFVar self t)
        (mkAppN fConst (params ++ [t]).toArray) (mkAppN lowered (params ++ [t]).toArray))
    let casesType ← instantiateForallsWith
      (casesOn.type.instantiateLevelParams casesOn.levelParams (Lean.Level.zero :: us))
      (params ++ [motiveP, self])
    let .forallE _ minorDomain _ _ := casesType | throwError "{casesOnName} has no minor premise"
    let minor ← forallTelescope minorDomain fun ys _ => do
      let constructed := mkAppN (.const ctorName us) (params.toArray ++ ys)
      mkLambdaFVars ys (← mkEqRefl (mkAppN fConst (params ++ [constructed]).toArray))
    let proof := mkAppN (.const casesOnName (Lean.Level.zero :: us)) (params ++ [motiveP, self, minor]).toArray
    let value ← mkLambdaFVars xs proof
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    return { name := loweringEquationName f, levelParams := d.levelParams, type, value }

/-- Run a `MetaM` action over an environment, with no heartbeat limit. -/
def runMeta (env : Lean.Environment) (x : MetaM α) : IO (Except String α) := do
  let ctx : Core.Context := { fileName := "<projection-lowering>", fileMap := default, maxHeartbeats := 0 }
  try
    let (a, _) ← (x.run' {} {}).toIO ctx { env }
    return .ok a
  catch e => return .error (toString e)

/-- Lean's kernel on the lowering equation (`addDeclCore`, checking on). -/
def admitLoweringWitness (env : Lean.Environment) (witness : Lean.TheoremVal) : IO (Except String Lean.Environment) := do
  match env.addDeclCore 0 0 (.thmDecl witness) none (doCheck := true) with
  | .ok env => return .ok env
  | .error e => return .error (← (e.toMessageData {}).toString)

/-- The four source entries the receipt reads: the definition, its owner, the
owner's constructor and recursor. On any larger source with unique names the
lookups return the same entries. -/
def receiptSource (env : Lean.Environment) (f : Lean.Name) : Except String Source := do
  let some ci := env.find? f | throw s!"{f} is not in the environment"
  let some sourceValue := projectionSourceValue ci | throw s!"{f} is not a definition or theorem"
  let some (owner, _, _) := sourceProjectionBody sourceValue | throw s!"{f} is not a projection function"
  let some oi@(.inductInfo T) := env.find? owner | throw s!"{owner} is not an inductive type"
  let ctors := T.ctors.filterMap env.find?
  let some ri := env.find? (owner.str "rec") | throw s!"{owner} has no recursor"
  return ⟨[ci, oi] ++ ctors ++ [ri]⟩

/-- The outcome of one projection function. -/
structure LoweringOutcome where
  witness : Lean.TheoremVal
  /-- the elimination level, as Lean inferred it -/
  level : Lean.Level
  kernel : Except String Unit
  receipt : Except String Unit

/-- Build the witness, have Lean's kernel check it, and decide the lane's receipt
(`proposeSourceProjection`, `checkSourceProjectionLowering`,
`checkSourceProjectionReceipt`) on the receipt source. -/
def lowerProjection (env : Lean.Environment) (f : Lean.Name) (tamper : LoweringTamper := .none) :
    IO (Except String LoweringOutcome) := do
  match ← runMeta env (buildLoweringWitness f tamper) with
  | .error why => return .error s!"witness: {why}"
  | .ok witness =>
    let level ← match ← runMeta env (do
        let some d := (← getEnv).find? f | throwError "absent"
        let some (owner, _, _) := (projectionSourceValue d).bind sourceProjectionBody
          | throwError "not a projection"
        let some (.inductInfo T) := (← getEnv).find? owner | throwError "no owner"
        forallBoundedTelescope d.type (some (T.numParams + 1)) fun _ R => getLevel R) with
      | .ok l => pure l
      | .error _ => pure Lean.Level.zero
    let kernel ← match ← admitLoweringWitness env witness with
      | .ok _ => pure (.ok ())
      | .error why => pure (.error why)
    let receipt : Except String Unit := do
      let source ← receiptSource env f
      let some ci := env.find? f | throw "absent"
      let some original := entryDeclaration (← exportSourceEntry ci)
        | throw "projection export is not a definition or theorem"
      let replacement ← match ← proposeSourceProjection source [witness] original with
        | some (replacement, equation) =>
          let _ ← checkSourceProjectionReceipt source original replacement equation
          pure replacement
        | none => match ← proposeSourceProof source [witness] original with
          | some replacement => pure replacement
          | none => throw "no lowering proposed"
      let _ ← checkSourceProjectionLowering source [witness] original replacement
      return ()
    return .ok { witness, level, kernel, receipt }

/-- The owners whose projection functions the normalised route lowers: every
structure-like the checker's direct route does not take (a mutual member, a
nested or a recursive structure-like), as the certifier's measurement classes
them. -/
def lowerableOwner (env : Lean.Environment) (owner : Lean.Name) : Bool :=
  match env.find? owner with
  | some (.inductInfo v) => v.all.length > 1 || v.numNested > 0 || v.isRec
  | _ => false

/-- The projection functions among some declarations whose owner is lowerable. -/
def projectionFunctionsIn (env : Lean.Environment) (declarations : List Lean.ConstantInfo) : List Lean.Name :=
  declarations.filterMap fun ci =>
    match (projectionSourceValue ci).bind sourceProjectionBody with
    | some (owner, _, _) => if lowerableOwner env owner then some ci.name else none
    | none => none

/-- Witnesses for the named projection functions, each accepted by Lean's
kernel; the first refusal fails the whole list. -/
def kernelCheckedWitnesses (env : Lean.Environment) (names : List Lean.Name) : IO (Except String LoweringWitnesses) := do
  let mut out : LoweringWitnesses := []
  for f in names do
    match ← runMeta env (buildLoweringWitness f) with
    | .error why => return .error s!"{f}: {why}"
    | .ok witness =>
      match ← admitLoweringWitness env witness with
      | .error why => return .error s!"{f}: Lean's kernel refused the lowering equation: {why}"
      | .ok _ => out := out ++ [witness]
  return .ok out

/-- The witnesses for a captured source: every lowerable projection function in it. -/
def sourceWitnesses (env : Lean.Environment) (source : Source) : IO LoweringWitnesses := do
  IO.ofExcept (← kernelCheckedWitnesses env (projectionFunctionsIn env source.declarations))

end Ix.CompileCert.LoweringLean
