/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Batteries.Data.List.Basic
import Ix.Theory.Named.Reference.Environment.Basic
import Ix.Theory.Named.Reference.TypeChecker

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive
open TypeChecker

structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  deriving Inhabited

structure InductiveStats where
  lctx : LocalContext := {}
  levels : List Level
  resultLevel : Level
  nindices : Array Nat := #[]
  indConsts : Array Expr
  params : Array Expr
  isNotZero : Bool
  deriving Inhabited

/-- Explicit initial state for family validation. Naming this value keeps the
executable producer and its exact-result lemmas independent of the opaque
compiler-generated `Inhabited` instance. -/
def InductiveStats.initial (levels : List Level) : InductiveStats where
  levels := levels
  resultLevel := .zero
  indConsts := #[]
  params := #[]
  isNotZero := false

structure Context where
  env : Environment
  lctx : LocalContext := {}
  lparams : List Name
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool
  fuel : FuelConfig := {}

/-- Checker context represented by an inductive-add context. Candidate traces
retain the latter so Verify can recover this exact former value. -/
def Context.toTypeChecker (context : Context) : TypeChecker.Context where
  env := context.env
  lctx := context.lctx
  safety := context.safety
  lparams := context.lparams
  fuel := context.fuel

/-- The exact free variable allocated by the next `withLocalDecl` in an
inductive-add context. -/
def Context.freshFVarId (context : Context) : FVarId :=
  ⟨context.ngen.curr⟩

def Context.freshExpr (context : Context) : Expr :=
  .fvar context.freshFVarId

/-- Context seen by the body of the next `withLocalDecl`.  Naming this update
lets candidate traces index a Pi body by the actual reader context used by the
producer, rather than retaining an unrelated context as unchecked data. -/
def Context.pushLocalDecl (context : Context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr) : Context :=
  { context with
    lctx := context.lctx.mkLocalDecl context.freshFVarId name type binderInfo
    ngen := context.ngen.next }

abbrev M := ReaderT Context <| Except Exception

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel)

@[simp] theorem liftTypeChecker_apply (x : TypeChecker.M α) (c : Context) :
    (liftM x : M α) c =
      x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel) :=
  rfl

@[simp] theorem liftExcept_apply (x : Except Exception α) (c : Context) :
    (liftM x : M α) c = x :=
  rfl

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[simp] theorem withLocalDecl_apply
    (name : Name) (binderInfo : BinderInfo) (type : Expr)
    (k : Expr → M α) (context : Context) :
    withLocalDecl name binderInfo type k context =
      k context.freshExpr
        (context.pushLocalDecl name binderInfo type) := by
  rfl

@[inline] def withEnv (env : Environment) (x : M α) : M α :=
  withReader (fun c => { c with env }) x

/-- Run an action under a different universe parameter list. The recursors are checked under
their own parameters, which carry the extra eliminator level the declaration itself lacks. -/
@[inline] def withLParams (lparams : List Name) (x : M α) : M α :=
  withReader (fun c => { c with lparams }) x

/-- Run a closed-metadata action without inheriting validation-local
declarations.  All other reader fields, including the staged environment and
fuel, are preserved exactly. -/
@[inline] def withEmptyLocalContext (x : M α) : M α :=
  withReader (fun c : Context => { c with lctx := {} }) x

@[simp] theorem withEmptyLocalContext_apply (x : M α) (context : Context) :
    withEmptyLocalContext x context = x { context with lctx := {} } := by
  rfl

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

/-- Transparent binder-annotation peeling used by inductive checking.

Lean's `Expr.consumeTypeAnnotations` is an opaque partial implementation.  A
kernel proof of an exact successful inductive pass cannot reduce through that
helper, so using it directly would require a separate contract axiom for every
annotated binder.  This structural mirror covers the same four top-level
annotations and is regression-checked against Lean's helper below at the
candidate boundary. -/
def consumeTypeAnnotations : (source : Expr) → Expr
  | .app (.app (.const name levels) type) default =>
    if name = ``_root_.optParam then
      consumeTypeAnnotations type
    else if name = ``_root_.autoParam then
      consumeTypeAnnotations type
    else
      .app (.app (.const name levels) type) default
  | .app (.const name levels) type =>
    if name = ``_root_.outParam then
      consumeTypeAnnotations type
    else if name = ``_root_.semiOutParam then
      consumeTypeAnnotations type
    else
      .app (.const name levels) type
  | source => source
termination_by source => sizeOf source

/-- Transparent structural equality used only as a fast path before the
normalization-based universe comparison. -/
def levelStructEq : Level → Level → Bool
  | .zero, .zero => true
  | .succ u, .succ v => levelStructEq u v
  | .max u₁ u₂, .max v₁ v₂ | .imax u₁ u₂, .imax v₁ v₂ =>
    levelStructEq u₁ v₁ && levelStructEq u₂ v₂
  | .param u, .param v => u == v
  | .mvar u, .mvar v => u == v
  | _, _ => false

/-- Transparent sufficient comparison for the common structural universe
cases used by constructor fields.  Every universe is at least zero, successor
is monotone, and otherwise exact structural equality is sufficient.  Cases
outside this deliberately small relation continue to the standard
normalization-based `Level.geq` comparison below. -/
def levelStructGe : Level → Level → Bool
  | _, .zero => true
  | .succ u, .succ v => levelStructGe u v
  | u, v => levelStructEq u v

def checkInductiveTypes
    (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  let rec loopInd dIdx stats : M α := do
    if _h : dIdx < indTypes.size then
      let indType := indTypes[dIdx]
      let env := (← read).env
      let type := indType.type
      env.checkNoMVarNoFVar indType.name type
      _ ← checkType type
      let rec loop stats type i nindices fuel k : M α := match fuel with
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := type then
          if i < nparams then
            if stats.indConsts.isEmpty then
              withLocalDecl name bi (consumeTypeAnnotations dom) fun param => do
                let stats := { stats with params := stats.params.push param }
                let type := body.instantiate1 param
                loop stats (← whnf type) (i + 1) nindices fuel k
            else
              let param := stats.params[i]!
              unless ← isDefEq dom (← getType param) do
                throw <| .other "parameters of all inductive datatypes must match"
              let type := body.instantiate1 param
              loop stats (← whnf type) (i + 1) nindices fuel k
          else
            withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
              let type := body.instantiate1 arg
              loop stats (← whnf type) i (nindices + 1) fuel k
        else
          if i != nparams then
            throw <| .other "number of parameters mismatch in inductive datatype declaration"
          k type stats nindices
      let fuel := (← readThe Context).fuel.inductiveFuel
      loop stats (← whnf type) 0 0 fuel fun type stats nindices => show M α from do
      let type ← ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indType.name stats.levels) }
      loopInd (dIdx + 1) stats
    else
      k <|
        assert! stats.levels.length == (← read).lparams.length
        assert! stats.nindices.size == indTypes.size
        assert! stats.indConsts.size == indTypes.size
        assert! stats.params.size == nparams
        stats
  termination_by indTypes.size - dIdx
  loopInd 0 (InductiveStats.initial ((← read).lparams.map .param))

/-- Exact singleton result of the family-validation pass when the family type
normalizes directly to a sort. This is the non-telescope producer seam used by
end-to-end candidate certificates: the executable pass selects every retained
statistic, while callers supply only the ordinary checker runs it consumed. -/
def singletonInductiveStats (context : Context)
    (indType : InductiveType) (resultLevel : Level) : InductiveStats where
  lctx := context.lctx
  levels := context.lparams.map .param
  resultLevel := resultLevel
  nindices := #[0]
  indConsts := #[.const indType.name (context.lparams.map .param)]
  params := #[]
  isNotZero := resultLevel.isNeverZero

theorem checkInductiveTypes_singleton_zero_of_whnf_sort
    (context : Context) (indType : InductiveType)
    (inferred : Expr) (resultLevel : Level)
    (k : InductiveStats → M α)
    (hfuel : 0 < context.fuel.inductiveFuel)
    (hclosed :
      context.env.checkNoMVarNoFVar indType.name indType.type = .ok ())
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType indType.type) =
        .ok inferred)
    (hwhnf :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf indType.type) =
        .ok (.sort resultLevel))
    (hensure :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel
          (TypeChecker.ensureSort (.sort resultLevel)) =
        .ok (.sort resultLevel)) :
    checkInductiveTypes 0 #[indType] k context =
      k (singletonInductiveStats context indType resultLevel) context := by
  cases hfuel_eq : context.fuel.inductiveFuel with
  | zero => omega
  | succ fuel =>
    simp [checkInductiveTypes, checkInductiveTypes.loopInd, checkInductiveTypes.loopInd.loop,
      singletonInductiveStats, readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure, liftTypeChecker_apply, hclosed,
      hcheck, hwhnf, hensure, hfuel_eq, InductiveStats.initial, Expr.sortLevel!]

/-- Transparent occurrence test for constants in the inductive block.

Lean's `Expr.find?` is an opaque native traversal.  Using it here makes the
kernel's recursive-family and positivity decisions impossible to reduce in an
exact producer theorem without postulating a separate contract for that
traversal.  This structural version follows the same expression children and
keeps those decisions computational in the logic as well as at runtime. -/
def hasIndOcc (indConsts : Array Expr) : Expr → Bool
  | .const name _ => indConsts.any fun I => I.constName! == name
  | .app fn arg => hasIndOcc indConsts fn || hasIndOcc indConsts arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
    hasIndOcc indConsts domain || hasIndOcc indConsts body
  | .letE _ type value body _ =>
    hasIndOcc indConsts type || hasIndOcc indConsts value ||
      hasIndOcc indConsts body
  | .mdata _ body | .proj _ _ body => hasIndOcc indConsts body
  | _ => false

/-- Return true if declaration is recursive -/
def isRec (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- Return true if the given declaration is reflexive.

Remark: We say an inductive type `T` is reflexive if it
contains at least one constructor that takes as an argument a
function returning `T'` where `T'` is another inductive datatype (possibly equal to `T`)
in the same mutual declaration. -/
def isReflexive (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => dom.isForall && hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

def declareInductiveTypes (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : M Environment :=
  fun c =>
  let all := indTypes.map (·.name) |>.toList
  let infos := indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    { indType with
      numParams, numIndices, all, numNested, isUnsafe
      levelParams := c.lparams
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts }
  infos.foldlM (init := c.env) fun env info => do
    env.checkName info.name c.allowPrimitive
    return env.add (.inductInfo info)

/-- The exact kernel family record assembled for a singleton inductive block.
Naming it exposes the value installed by `declareInductiveTypes` without
asking a replay proof to duplicate the producer's record construction. -/
def singletonDeclaredInfo (stats : InductiveStats) (numParams numIndices : Nat)
    (indType : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) : InductiveVal :=
  { indType with
    numParams, numIndices, all := [indType.name], numNested, isUnsafe
    levelParams := context.lparams
    ctors := indType.ctors.map (·.name)
    isRec := isRec #[indType] stats.indConsts
    isReflexive := isReflexive #[indType] stats.indConsts }

/-- A successful singleton family declaration installs exactly the family
record assembled by the executable producer.  The result equation supplies
the name-check evidence; replay callers provide only the validator's exact
singleton index count. -/
theorem declareInductiveTypes_singleton_constants
    (stats : InductiveStats) (numParams numIndices : Nat)
    (indType : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) (familyEnv : Environment)
    (hnindices : stats.nindices = #[numIndices])
    (hdeclare :
      declareInductiveTypes stats numParams #[indType] numNested isUnsafe context =
        .ok familyEnv) :
    familyEnv.constants =
      context.env.constants.insert indType.name
        (.inductInfo <| singletonDeclaredInfo stats numParams numIndices
          indType numNested isUnsafe context) := by
  unfold declareInductiveTypes at hdeclare
  rw [hnindices] at hdeclare
  cases hcheck : context.env.checkName indType.name context.allowPrimitive with
  | error error =>
      simp [hcheck, Bind.bind, Except.bind, Pure.pure, Except.pure] at hdeclare
  | ok _ =>
      simp [hcheck, Bind.bind, Except.bind, Pure.pure, Except.pure] at hdeclare
      exact congrArg Kernel.Environment.constants hdeclare.symm

/-- A successful singleton family declaration changes only the constant map;
in particular it preserves the kernel's quotient-initialization flag. -/
theorem declareInductiveTypes_singleton_quotInit
    (stats : InductiveStats) (numParams numIndices : Nat)
    (indType : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) (familyEnv : Environment)
    (hnindices : stats.nindices = #[numIndices])
    (hdeclare :
      declareInductiveTypes stats numParams #[indType] numNested isUnsafe context =
        .ok familyEnv) :
    familyEnv.quotInit = context.env.quotInit := by
  unfold declareInductiveTypes at hdeclare
  rw [hnindices] at hdeclare
  cases hcheck : context.env.checkName indType.name context.allowPrimitive with
  | error error =>
      simp [hcheck, Bind.bind, Except.bind, Pure.pure, Except.pure] at hdeclare
  | ok _ =>
      simp [hcheck, Bind.bind, Except.bind, Pure.pure, Except.pure] at hdeclare
      subst familyEnv
      rfl

/-- Family declaration observes only the environment, universe parameters,
and primitive-name policy of its reader context.  In particular, the local
telescope and fresh-name generator retained by family validation do not alter
the staged environment it produces. -/
theorem declareInductiveTypes_context_eq
    (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) (left right : Context)
    (henv : left.env = right.env)
    (hlparams : left.lparams = right.lparams)
    (hallow : left.allowPrimitive = right.allowPrimitive) :
    declareInductiveTypes stats numParams indTypes numNested isUnsafe left =
      declareInductiveTypes stats numParams indTypes numNested isUnsafe right := by
  unfold declareInductiveTypes
  rw [henv, hlparams, hallow]

def isValidIndAppIdx (stats : InductiveStats) (t : Expr) (i : Nat) : Bool :=
  t.withApp fun I args => Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  for i in [:stats.params.size] do
    if stats.params[i]! != args[i]! then return false
  for i in [stats.params.size:args.size] do
    if hasIndOcc stats.indConsts args[i]! then return false
  true

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat := do
  for i in [:stats.indConsts.size] do
    if isValidIndAppIdx stats t i then
      return i
  none

theorem isValidIndApp?_singleton_zero
    (stats : InductiveStats) (t : Expr)
    (hsize : stats.indConsts.size = 1)
    (hvalid : isValidIndAppIdx stats t 0 = true) :
    isValidIndApp? stats t = some 0 := by
  unfold isValidIndApp?
  simp [hsize, hvalid]

def isRecArg (stats : InductiveStats) (t : Expr) : M (Option Nat) := do
  loop t (← readThe Context).fuel.inductiveFuel
where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return isValidIndApp? stats t
    withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
    loop (body.instantiate1 arg) fuel

def checkPositivity (stats : InductiveStats) (t : Expr) (ctor : Name) (idx : Nat) :
    M Unit := do loop t (← readThe Context).fuel.inductiveFuel where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    if !hasIndOcc stats.indConsts t then return
    if let .forallE name dom body bi := t then
      if hasIndOcc stats.indConsts dom then
        throw <| .other s!"arg #{idx + 1} of '{ctor}' \
          has a non positive occurrence of the datatypes being declared"
      withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
      loop (body.instantiate1 arg) fuel
    else if let none := isValidIndApp? stats t then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non valid occurrence of the datatypes being declared"

/-- Validate the parameter/field telescope and terminal family application of
one constructor. This is factored from the outer traversal so successful
executions can be retained without reproducing compiler-expanded `for` loops. -/
def checkConstructorType (stats : InductiveStats) (isUnsafe : Bool)
    (idx : Nat) (n : Name) (t : Expr) : M Unit := do
  loop t 0 (← readThe Context).fuel.inductiveFuel
where
  loop t i
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        unless ← isDefEq dom (← getType param) do
          throw <| .other
            s!"arg #{i + 1} of '{n}' does not match inductive datatype parameters"
        loop (body.instantiate1 param) (i + 1) fuel
      else
        let s ← ensureType dom
        -- Equal levels are reflexively admissible, so discharge that common
        -- case before consulting the full normalization comparison.
        if levelStructGe stats.resultLevel s.sortLevel! then
          pure ()
        else
          unless stats.resultLevel.isAlwaysZero || stats.resultLevel.geq s.sortLevel! do
            throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{n}' \
              is too big for the corresponding inductive datatype"
        if !isUnsafe then
          checkPositivity stats dom n i
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
          loop (body.instantiate1 arg) (i + 1) fuel
    else if !isValidIndAppIdx stats t idx then
      throw <| .other s!"invalid return type for '{n}'"

/-- Validate constructors in source order while retaining the duplicate-name
accumulator as the fold result. -/
def checkConstructorFold (env : Environment) (stats : InductiveStats)
    (isUnsafe : Bool) (idx : Nat) (seen : NameSet)
    (ctors : List Constructor) : M NameSet := match ctors with
  | [] => pure seen
  | ctor :: ctors => do
    let n := ctor.name
    if seen.contains n then
      throw <| .other s!"duplicate constructor name '{n}'"
    let seen := seen.insert n
    let t := ctor.type
    env.checkNoMVarNoFVar n t
    -- Constructor metadata has just been established to contain no free
    -- variables. Its full closed-type check does not inherit family locals;
    -- parameter matching in `checkConstructorType` deliberately does.
    _ ← withEmptyLocalContext do checkType t
    checkConstructorType stats isUnsafe idx n t
    checkConstructorFold env stats isUnsafe idx seen ctors

/-- The named family recursion of `checkConstructors`.  Naming the loop keeps
the executable shell and its validation-trace mirror aligned without depending
on proof terms synthesized by `for` notation. -/
def checkConstructorsLoop (env : Environment) (stats : InductiveStats)
    (isUnsafe : Bool) : Nat → List InductiveType → M Unit
  | _, [] => pure ()
  | idx, indType :: rest => do
    _ ← checkConstructorFold env stats isUnsafe idx {} indType.ctors
    checkConstructorsLoop env stats isUnsafe (idx + 1) rest

def checkConstructors (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) : M Unit := do
  let env ← getEnv
  checkConstructorsLoop env stats isUnsafe 0 indTypes.toList

/-- One observed WHNF node in the executable normalization-candidate pass.
The complete `AddInductive.Context` is retained because Verify must replay the
same environment, safety mode, local context, level parameters, transparency,
and checker fuel before the observation acquires semantic authority. -/
structure CandidateWhnfStep where
  context : Context
  source : Expr
  result : Expr

/-- Exact ordinary-checker execution represented by one retained step. -/
def CandidateWhnfStep.Valid (step : CandidateWhnfStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.whnf step.source) =
    .ok step.result

/-- The result of evaluating one WHNF step together with the equality that
certifies the observation. -/
structure CandidateWhnfObservation (context : Context) (source : Expr) where
  result : Expr
  valid : CandidateWhnfStep.Valid ⟨context, source, result⟩

def observeCandidateWhnf (context : Context) (source : Expr) :
    Except Exception (CandidateWhnfObservation context source) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.whnf source) with
  | .error err => .error err
  | .ok result => .ok ⟨result, hrun⟩

theorem observeCandidateWhnf_of_run
    (context : Context) (source result : Expr)
    (hrun : CandidateWhnfStep.Valid ⟨context, source, result⟩) :
    observeCandidateWhnf context source = .ok ⟨result, hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.whnf source) =
      .ok result at hrun
  unfold observeCandidateWhnf
  split
  · simp_all
  · rename_i observed hobserved
    have : observed = result := by simp_all
    subst observed
    rfl

/-- Recover the state-bearing recursive checker execution erased by
`TypeChecker.M.run`. This is the exact `WhnfRun.run_eq` boundary used by
Verify; no final state is guessed or chosen. -/
theorem CandidateWhnfStep.innerRun
    (step : CandidateWhnfStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel + 1)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf' step.source
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (step.result, state) := by
  unfold CandidateWhnfStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  simp only [TypeChecker.Methods.withFuel,
    TypeChecker.Inner.whnf] at hvalid
  cases hinner :
      TypeChecker.Inner.whnf' step.source
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = step.result := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- One full, non-inference-only type-check observation retained by the
candidate producer. -/
structure CandidateCheckTypeStep where
  context : Context
  source : Expr
  inferred : Expr

def CandidateCheckTypeStep.Valid
    (step : CandidateCheckTypeStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.checkType step.source) =
    .ok step.inferred

structure CandidateCheckTypeObservation
    (context : Context) (source : Expr) where
  inferred : Expr
  valid : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩

def observeCandidateCheckType (context : Context) (source : Expr) :
    Except Exception (CandidateCheckTypeObservation context source) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.checkType source) with
  | .error err => .error err
  | .ok inferred => .ok ⟨inferred, hrun⟩

theorem observeCandidateCheckType_of_run
    (context : Context) (source inferred : Expr)
    (hrun : CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    observeCandidateCheckType context source =
      .ok ⟨inferred, hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.checkType source) =
      .ok inferred at hrun
  unfold observeCandidateCheckType
  split
  · simp_all
  · rename_i observed hobserved
    have : observed = inferred := by simp_all
    subst observed
    rfl

/-- Recover the state-bearing full-check execution erased by `M.run`. -/
theorem CandidateCheckTypeStep.innerRun
    (step : CandidateCheckTypeStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType step.source false
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (step.inferred, state) := by
  unfold CandidateCheckTypeStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.checkType
    TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  cases hinner :
      TypeChecker.Inner.inferType step.source false
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = step.inferred := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- One exact successful definitional-equality observation retained by the
candidate producer. The result is fixed to `true`; a negative checker result
is not evidence and aborts candidate construction. -/
structure CandidateIsDefEqStep where
  context : Context
  lhs : Expr
  rhs : Expr

def CandidateIsDefEqStep.Valid
    (step : CandidateIsDefEqStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.isDefEq step.lhs step.rhs) =
    .ok true

structure CandidateIsDefEqObservation
    (context : Context) (lhs rhs : Expr) : Type where
  valid : CandidateIsDefEqStep.Valid ⟨context, lhs, rhs⟩

def observeCandidateIsDefEq
    (context : Context) (lhs rhs : Expr) :
    Except Exception (CandidateIsDefEqObservation context lhs rhs) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.isDefEq lhs rhs) with
  | .error err => .error err
  | .ok false =>
    .error (.other "normalization candidate changed a binder domain")
  | .ok true => .ok ⟨hrun⟩

theorem observeCandidateIsDefEq_of_run
    (context : Context) (lhs rhs : Expr)
    (hrun : CandidateIsDefEqStep.Valid ⟨context, lhs, rhs⟩) :
    observeCandidateIsDefEq context lhs rhs = .ok ⟨hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.isDefEq lhs rhs) =
      .ok true at hrun
  unfold observeCandidateIsDefEq
  split
  · simp_all
  · simp_all
  · rfl

/-- Recover the state-bearing equality execution erased by `M.run`. -/
theorem CandidateIsDefEqStep.innerRun
    (step : CandidateIsDefEqStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEq step.lhs step.rhs
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (true, state) := by
  unfold CandidateIsDefEqStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.isDefEq
    TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  cases hinner :
      TypeChecker.Inner.isDefEq step.lhs step.rhs
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = true := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- Source-indexed retained full-check execution. -/
structure CandidateCheckTypeRun (source : Expr) where
  step : CandidateCheckTypeStep
  source_eq : step.source = source
  valid : step.Valid

def buildCandidateCheckType
    (source : Expr) : M (CandidateCheckTypeRun source) := do
  let context ← readThe Context
  match observeCandidateCheckType context source with
  | .error err => throw err
  | .ok ⟨inferred, valid⟩ =>
    return ⟨⟨context, source, inferred⟩, rfl, valid⟩

/-- Structural certificate for the four top-level binder-domain annotations
peeled by `Expr.consumeTypeAnnotations`.

The certificate exposes which application argument survives. Verify can
therefore recover a strict translation and free-variable facts for the
consumed domain from the translated raw domain, without assigning semantic
authority to Lean's opaque helper. -/
inductive CandidateTypeAnnotationTrace : Expr → Expr → Type where
  | identity (source : Expr) :
      CandidateTypeAnnotationTrace source source
  | outParam (levels : List Level) (type : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.const ``outParam levels) type) consumed
  | semiOutParam (levels : List Level) (type : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.const ``semiOutParam levels) type) consumed
  | optParam (levels : List Level) (type default : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.app (.const ``optParam levels) type) default) consumed
  | autoParam (levels : List Level) (type tactic : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.app (.const ``autoParam levels) type) tactic) consumed

namespace CandidateTypeAnnotationTrace

/-- Transparent structural mirror of the top-level peeling algorithm. -/
def build : (source : Expr) → Sigma (CandidateTypeAnnotationTrace source)
  | .app (.app (.const name levels) type) default =>
    if hopt : name = ``_root_.optParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .optParam levels type default inner⟩
    else if hauto : name = ``_root_.autoParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .autoParam levels type default inner⟩
    else
      ⟨.app (.app (.const name levels) type) default, .identity _⟩
  | .app (.const name levels) type =>
    if hout : name = ``_root_.outParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .outParam levels type inner⟩
    else if hsemi : name = ``_root_.semiOutParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .semiOutParam levels type inner⟩
    else
      ⟨.app (.const name levels) type, .identity _⟩
  | source => ⟨source, .identity source⟩
termination_by source => sizeOf source

/-- The structural annotation builder computes the same transparent peeling
used by inductive validation.  This deliberately relates two definitions in
this module, not Lean's opaque `Expr.consumeTypeAnnotations`. -/
theorem build_consumed (source : Expr) :
    (build source).1 = consumeTypeAnnotations source := by
  fun_induction build source <;> simp_all [consumeTypeAnnotations]

end CandidateTypeAnnotationTrace

/-- A structural peeling certificate. Verify assigns semantic authority only
to the trace; compatibility with Lean's opaque helper is retained as a
differential executable check rather than a proof axiom. -/
structure CandidateTypeAnnotations (source : Expr) where
  consumed : Expr
  trace : CandidateTypeAnnotationTrace source consumed

def buildCandidateTypeAnnotations
    (source : Expr) : Except Exception (CandidateTypeAnnotations source) :=
  let ⟨consumed, trace⟩ := CandidateTypeAnnotationTrace.build source
  .ok ⟨consumed, trace⟩

namespace CandidateTypeAnnotations

/-- Operational compatibility with this module's transparent annotation
peeling.  Semantic consumers still rely on `trace` plus the retained
definitional-equality execution; `Matches` is used to replay the executable
family-validation path exactly. -/
def Matches (annotations : CandidateTypeAnnotations source) : Prop :=
  annotations.consumed = consumeTypeAnnotations source

theorem matches_of_build
    (annotations : CandidateTypeAnnotations source)
    (hbuild : buildCandidateTypeAnnotations source = .ok annotations) :
    annotations.Matches := by
  unfold buildCandidateTypeAnnotations at hbuild
  cases htrace : CandidateTypeAnnotationTrace.build source with
  | mk consumed trace =>
    simp only [Except.ok.injEq] at hbuild
    subst annotations
    simpa [Matches, htrace] using
      CandidateTypeAnnotationTrace.build_consumed source

end CandidateTypeAnnotations

/-- Differential check pinning the transparent implementation to Lean's
opaque helper. This is executable regression evidence, not a logical premise
of the candidate producer. -/
def candidateTypeAnnotationsAgree (source : Expr) : Bool :=
  let ⟨consumed, _⟩ := CandidateTypeAnnotationTrace.build source
  consumed.equal source.consumeTypeAnnotations

/-- Context- and source-indexed tree underlying one candidate expression.
The recursive indices are important: a Pi-domain trace uses the exact parent
context, while its body trace uses precisely `Context.pushLocalDecl` with the
structurally certified annotation-consumed domain and the corresponding fresh
free variable. The retained equality run relates that local declaration back
to the raw binder syntax. Thus expression position, annotation handling, and
checker-context provenance are enforced by the type rather than being
invariants of the producer alone. -/
inductive CandidateExprTrace : Context → Expr → Type where
  | terminal (context : Context) (source inferred result : Expr)
      (checked : CandidateCheckTypeStep.Valid
        ⟨context, source, inferred⟩)
      (valid : CandidateWhnfStep.Valid ⟨context, source, result⟩) :
      CandidateExprTrace context source
  | forallE (context : Context) (source : Expr)
      (inferred : Expr)
      (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (fresh : context.lctx.find? context.freshFVarId = none)
      (annotations : CandidateTypeAnnotations domain)
      (annotationsEq : CandidateIsDefEqStep.Valid
        ⟨context, domain, annotations.consumed⟩)
      (checked : CandidateCheckTypeStep.Valid
        ⟨context, source, inferred⟩)
      (valid : CandidateWhnfStep.Valid
        ⟨context, source, .forallE name domain body binderInfo⟩)
      (domainCandidate : CandidateExprTrace context domain)
      (bodyCandidate : CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr)) :
      CandidateExprTrace context source

namespace CandidateExprTrace

/-- The main Pi spine exposed by candidate WHNF was already present in the
stored source syntax at every traversed body position.

This is the structural precondition needed by mixed generation: it permits
normalization inside binder domains and at the terminal result, but it does
not let WHNF invent or remove the raw binders that generation must emit. -/
def storedSpine :
    {context : Context} → {source : Expr} →
      CandidateExprTrace context source → Bool
  | _, _, .terminal .. => true
  | _, _, .forallE _ source _ name domain body binderInfo _ _ _ _ _ _
      bodyCandidate =>
    Expr.structuralEq source (.forallE name domain body binderInfo) &&
      storedSpine bodyCandidate

/-- Number of stored Pi binders on the main (body) path of a candidate. -/
def spineLength :
    {context : Context} → {source : Expr} →
      CandidateExprTrace context source → Nat
  | _, _, .terminal .. => 0
  | _, _, .forallE _ _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    bodyCandidate.spineLength + 1

/-- The exact full-check observation at the root of a candidate trace. -/
def rootCheck :
    CandidateExprTrace context source →
      CandidateCheckTypeObservation context source
  | .terminal _ _ inferred _ checked _ => ⟨inferred, checked⟩
  | .forallE _ _ inferred _ _ _ _ _ _ _ checked _ _ _ =>
    ⟨inferred, checked⟩

/-- The exact WHNF result at the root, before recursively normalized domains
and bodies are reassembled into `view`. -/
def rootWhnf : CandidateExprTrace context source → Expr
  | .terminal _ _ _ result _ _ => result
  | .forallE _ _ _ name domain body binderInfo _ _ _ _ _ _ _ =>
    .forallE name domain body binderInfo

theorem rootWhnf_valid (candidate : CandidateExprTrace context source) :
    CandidateWhnfStep.Valid ⟨context, source, candidate.rootWhnf⟩ := by
  cases candidate <;> assumption

/-- Reader context reached after following the complete main Π spine. -/
def terminalContext : CandidateExprTrace context source → Context
  | .terminal context _ _ _ _ _ => context
  | .forallE _ _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    bodyCandidate.terminalContext

theorem terminalContext_lparams
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.lparams = context.lparams := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine preserves the kernel environment. -/
theorem terminalContext_env
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.env = context.env := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine preserves the primitive-name
policy used by family declaration. -/
theorem terminalContext_allowPrimitive
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.allowPrimitive = context.allowPrimitive := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine changes only the local context and
name generator; it preserves the checker safety mode. -/
theorem terminalContext_safety
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.safety = context.safety := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine preserves the checker fuel
configuration. -/
theorem terminalContext_fuel
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.fuel = context.fuel := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Non-Π result reached after following the complete main Π spine. -/
def terminalResult : CandidateExprTrace context source → Expr
  | .terminal _ _ _ result _ _ => result
  | .forallE _ _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    bodyCandidate.terminalResult

/-- The first `count` local expressions allocated along the main Π spine.
These are exactly the expressions accumulated as inductive parameters when
`count` is the declaration's `nparams`. -/
def parameterList :
    (count : Nat) → CandidateExprTrace context source → List Expr
  | 0, _ => []
  | _ + 1, .terminal .. => []
  | count + 1,
      .forallE context _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    context.freshExpr :: bodyCandidate.parameterList count

theorem parameterList_length
    (candidate : CandidateExprTrace context source)
    (hcount : count ≤ candidate.spineLength) :
    (candidate.parameterList count).length = count := by
  induction candidate generalizing count with
  | terminal =>
    simp [spineLength] at hcount
    subst count
    rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [parameterList, List.length_cons]
      rw [body_ih]
      simpa [spineLength] using hcount

/-- Every annotation choice on the main Π spine matches the transparent
peeling operation used by `checkInductiveTypes`.  This is operational
provenance, separate from the semantic raw/consumed equality stored at each
candidate node. -/
def validationAnnotations :
    CandidateExprTrace context source → Prop
  | .terminal .. => True
  | .forallE _ _ _ _ _ _ _ _ annotations _ _ _ _ bodyCandidate =>
    annotations.Matches ∧ bodyCandidate.validationAnnotations

/-- Replay the inner family-telescope validator from a candidate's exact main
Π spine. The first `remaining` binders extend `stats.params`; every later
binder contributes an index. The theorem is independent of any fixture and
preserves the exact terminal reader context reached by the executable loop. -/
theorem checkInductiveTypes_loop_of_candidate
    (candidate : CandidateExprTrace context source)
    (stats : InductiveStats) (nparams i nindices fuel : Nat)
    (remaining : Nat) (k : Expr → InductiveStats → Nat → M α)
    (hi : i + remaining = nparams)
    (hcount : remaining ≤ candidate.spineLength)
    (hfuel : candidate.spineLength < fuel)
    (hempty : stats.indConsts.isEmpty = true)
    (hannotations : candidate.validationAnnotations)
    (hterminal : candidate.terminalResult.isForall = false) :
    checkInductiveTypes.loopInd.loop nparams stats candidate.rootWhnf
        i nindices fuel k context =
      k candidate.terminalResult
        { stats with
          params := stats.params ++
            (candidate.parameterList remaining).toArray }
        (nindices + (candidate.spineLength - remaining))
        candidate.terminalContext := by
  induction candidate generalizing i nindices fuel remaining stats with
  | terminal context source inferred result checked valid =>
    simp only [spineLength] at hcount hfuel
    have hremaining : remaining = 0 := by omega
    subst remaining
    have hi' : i = nparams := by omega
    subst i
    cases stats
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases result <;>
        simp_all [rootWhnf, terminalResult, terminalContext, parameterList,
          spineLength, checkInductiveTypes.loopInd.loop, Expr.isForall]
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    rcases hannotations with ⟨hmatch, hbodyAnnotations⟩
    cases remaining with
    | zero =>
      have hi' : i = nparams := by omega
      subst i
      have hbodyFuel : bodyCandidate.spineLength < fuel - 1 := by
        simp only [spineLength] at hfuel
        omega
      have hbodyCount : 0 ≤ bodyCandidate.spineLength := Nat.zero_le _
      have hvalid := bodyCandidate.rootWhnf_valid
      change TypeChecker.M.run _ _ _ _ _
          (TypeChecker.whnf (body.instantiate1 context.freshExpr)) =
        .ok bodyCandidate.rootWhnf at hvalid
      rw [show fuel = (fuel - 1) + 1 by omega]
      simp only [rootWhnf, checkInductiveTypes.loopInd.loop,
        Nat.lt_irrefl, if_false, withLocalDecl_apply]
      rw [← hmatch]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [hvalid]
      simp only [Except.bind]
      rw [body_ih stats nparams (nindices + 1) (fuel - 1) 0 rfl
        hbodyCount hbodyFuel hempty hbodyAnnotations hterminal]
      simp [terminalResult, terminalContext, parameterList, spineLength,
        Nat.add_comm, Nat.add_assoc]
    | succ remaining =>
      have hil : i < nparams := by omega
      have hbodyCount : remaining ≤ bodyCandidate.spineLength := by
        simp only [spineLength] at hcount
        omega
      have hbodyFuel : bodyCandidate.spineLength < fuel - 1 := by
        simp only [spineLength] at hfuel
        omega
      have hvalid := bodyCandidate.rootWhnf_valid
      change TypeChecker.M.run _ _ _ _ _
          (TypeChecker.whnf (body.instantiate1 context.freshExpr)) =
        .ok bodyCandidate.rootWhnf at hvalid
      rw [show fuel = (fuel - 1) + 1 by omega]
      simp only [rootWhnf, checkInductiveTypes.loopInd.loop, hil, if_true,
        hempty, withLocalDecl_apply]
      rw [← hmatch]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [hvalid]
      simp only [Except.bind]
      rw [body_ih { stats with
          params := stats.params.push context.freshExpr }
        (i + 1) nindices (fuel - 1) remaining (by omega)
        hbodyCount hbodyFuel (by simpa using hempty) hbodyAnnotations
        hterminal]
      simp [terminalResult, terminalContext, parameterList, spineLength]

/-- Exact singleton statistics selected by a candidate family spine with an
arbitrary parameter/index split. -/
def singletonCandidateInductiveStats
    (indType : InductiveType)
    (candidate : CandidateExprTrace context indType.type)
    (nparams : Nat) (resultLevel : Level) : InductiveStats where
  lctx := candidate.terminalContext.lctx
  levels := context.lparams.map .param
  resultLevel := resultLevel
  nindices := #[candidate.spineLength - nparams]
  indConsts := #[.const indType.name (context.lparams.map .param)]
  params := (candidate.parameterList nparams).toArray
  isNotZero := resultLevel.isNeverZero

/-- A source-indexed candidate family spine discharges the complete singleton
family-validation pass for any number of parameters and indices.  The result
records the same local expressions, terminal context, index count, universe,
and family constant selected by the executable validator. -/
theorem checkInductiveTypes_singleton_of_candidate
    (indType : InductiveType)
    (candidate : CandidateExprTrace context indType.type)
    (nparams : Nat) (resultLevel : Level)
    (k : InductiveStats → M α)
    (hclosed :
      context.env.checkNoMVarNoFVar indType.name indType.type = .ok ())
    (hcount : nparams ≤ candidate.spineLength)
    (hfuel : candidate.spineLength < context.fuel.inductiveFuel)
    (hannotations : candidate.validationAnnotations)
    (hterminal : candidate.terminalResult = .sort resultLevel)
    (hensure :
      TypeChecker.M.run candidate.terminalContext.env
          candidate.terminalContext.safety candidate.terminalContext.lctx
          candidate.terminalContext.lparams candidate.terminalContext.fuel
          (TypeChecker.ensureSort (.sort resultLevel)) =
        .ok (.sort resultLevel)) :
    checkInductiveTypes nparams #[indType] k context =
      k (candidate.singletonCandidateInductiveStats
        indType nparams resultLevel) candidate.terminalContext := by
  have hcheck := candidate.rootCheck.valid
  have hwhnf := candidate.rootWhnf_valid
  change TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.checkType indType.type) =
    .ok candidate.rootCheck.inferred at hcheck
  change TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.whnf indType.type) =
    .ok candidate.rootWhnf at hwhnf
  have hterminalForall : candidate.terminalResult.isForall = false := by
    rw [hterminal]
    rfl
  have hterminalLparams :
      candidate.terminalContext.lparams = context.lparams :=
    candidate.terminalContext_lparams
  have hparameterLength := candidate.parameterList_length hcount
  unfold checkInductiveTypes
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind]
  rw [checkInductiveTypes.loopInd.eq_1]
  have hsize : 0 < #[indType].size := by simp
  rw [dif_pos hsize]
  rw [show #[indType][0] = indType by rfl]
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind,
    liftTypeChecker_apply, hclosed, hcheck, hwhnf]
  rw [candidate.checkInductiveTypes_loop_of_candidate
    (stats := InductiveStats.initial (context.lparams.map .param))
    (nparams := nparams) (i := 0) (nindices := 0)
    (fuel := context.fuel.inductiveFuel) (remaining := nparams)
    (hi := Nat.zero_add nparams) (hcount := hcount) (hfuel := hfuel)
    (hempty := rfl) (hannotations := hannotations)
    (hterminal := hterminalForall)]
  rw [hterminal]
  simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
  rw [hensure]
  simp only [Except.bind]
  rw [if_pos (show ((InductiveStats.initial
      (List.map Level.param context.lparams)).indConsts).isEmpty = true from
    rfl)]
  simp only [Expr.sortLevel!, InductiveStats.initial, Nat.zero_add]
  simp only [ReaderT.bind, Bind.bind, Except.pure, Except.bind]
  rw [checkInductiveTypes.loopInd.eq_1]
  have hdone : ¬1 < #[indType].size := by simp
  rw [dif_neg hdone]
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind]
  simp [singletonCandidateInductiveStats, hterminalLparams,
    hparameterLength]

/-- Exact successful singleton family-validation execution retained at the
candidate selected by `buildNormalizationCandidate`.

The executable validator owns the parameter/index split, result universe,
statistics, and terminal reader context. Keeping the universally quantified
continuation equation makes this a decomposition of the real
`checkInductiveTypes` call rather than a fixture-specific success flag. The
semantic interpretation of the retained candidate remains in Verify. -/
structure FamilyValidationRun
    (indType : InductiveType)
    {context : Context}
    (candidate : CandidateExprTrace context indType.type) where
  nparams : Nat
  resultLevel : Level
  stats : InductiveStats
  stats_eq : stats = candidate.singletonCandidateInductiveStats
    indType nparams resultLevel
  terminal_eq : candidate.terminalResult = Expr.sort resultLevel
  run : ∀ {α} (k : InductiveStats → M α),
    checkInductiveTypes nparams #[indType] k context =
      k stats candidate.terminalContext

/-- The retained singleton validation run exposes exactly the candidate view
parameter expressions selected by the executable family pass. -/
def FamilyValidationRun.parameters
    (run : FamilyValidationRun indType candidate) : List Expr :=
  candidate.parameterList run.nparams

/-- The retained singleton validation run exposes the number of candidate
view indices following the selected parameter prefix. -/
def FamilyValidationRun.numIndices
    (run : FamilyValidationRun indType candidate) : Nat :=
  candidate.spineLength - run.nparams

/-- Candidate expression reconstructed from the traced WHNF/Pi tree. -/
def view : CandidateExprTrace context source → Expr
  | .terminal _ _ _ result _ _ => result
  | .forallE context _ _ name _ _ binderInfo _ _ _ _ _ domain body =>
    .forallE name domain.view
      (body.view.abstract #[context.freshExpr]) binderInfo

/-- Preorder list of all retained checker observations. -/
def steps : CandidateExprTrace context source → List CandidateWhnfStep
  | .terminal context source _ result _ _ => [{ context, source, result }]
  | .forallE context source _ name domain body binderInfo _ _ _ _ _
      domainCandidate bodyCandidate =>
    { context, source,
      result := .forallE name domain body binderInfo } ::
      domainCandidate.steps ++ bodyCandidate.steps

/-- Preorder list of all retained full-check observations. -/
def checkSteps : CandidateExprTrace context source → List CandidateCheckTypeStep
  | .terminal context source inferred _ _ _ =>
    [{ context, source, inferred }]
  | .forallE context source inferred _ _ _ _ _ _ _ _ _
      domainCandidate bodyCandidate =>
    { context, source, inferred } ::
      domainCandidate.checkSteps ++ bodyCandidate.checkSteps

/-- Preorder list of all retained binder-domain equality observations. -/
def isDefEqSteps :
    CandidateExprTrace context source → List CandidateIsDefEqStep
  | .terminal .. => []
  | .forallE context _ _ _ domain _ _ _ annotations _ _ _
      domainCandidate bodyCandidate =>
    { context, lhs := domain, rhs := annotations.consumed } ::
      domainCandidate.isDefEqSteps ++ bodyCandidate.isDefEqSteps

/-- Every retained WHNF observation is an exact checker execution. -/
theorem allValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.steps, step.Valid
  | .terminal context source _ result _ valid, step, h => by
    simp only [steps, List.mem_singleton] at h
    subst step
    exact valid
  | .forallE _ _ _ _ _ _ _ _ _ _ _ valid domain body, step, h => by
    simp only [steps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact valid
    · exact domain.allValid step h
    · exact body.allValid step h

/-- Every retained full-check observation is an exact checker execution. -/
theorem allChecksValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.checkSteps, step.Valid
  | .terminal context source inferred _ checked _, step, h => by
    simp only [checkSteps, List.mem_singleton] at h
    subst step
    exact checked
  | .forallE _ _ _ _ _ _ _ _ _ _ checked _ domain body, step, h => by
    simp only [checkSteps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact checked
    · exact domain.allChecksValid step h
    · exact body.allChecksValid step h

/-- Every retained binder-domain equality is an exact successful checker
execution. -/
theorem allIsDefEqValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.isDefEqSteps, step.Valid
  | .terminal .., step, h => by simp [isDefEqSteps] at h
  | .forallE _ _ _ _ _ _ _ _ _ annotationsEq _ _ domain body,
      step, h => by
    simp only [isDefEqSteps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact annotationsEq
    · exact domain.allIsDefEqValid step h
    · exact body.allIsDefEqValid step h

end CandidateExprTrace

/-- Source-indexed trace for one candidate expression. The tree records the
full-check and WHNF observations at every inspected node and retains the exact
positional split through Pi domains and instantiated bodies. Every node
carries the exact checker-run equalities produced by
`observeCandidateCheckType` and `observeCandidateWhnf`; Theory translation and
semantic refinement are intentionally separate. -/
structure CandidateExpr (source : Expr) where
  context : Context
  trace : CandidateExprTrace context source

def CandidateExpr.view (candidate : CandidateExpr source) : Expr :=
  candidate.trace.view

def CandidateExpr.steps
    (candidate : CandidateExpr source) : List CandidateWhnfStep :=
  candidate.trace.steps

def CandidateExpr.checkSteps
    (candidate : CandidateExpr source) :
    List CandidateCheckTypeStep :=
  candidate.trace.checkSteps

def CandidateExpr.isDefEqSteps
    (candidate : CandidateExpr source) :
    List CandidateIsDefEqStep :=
  candidate.trace.isDefEqSteps

theorem CandidateExpr.step_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.steps) :
    step.Valid :=
  candidate.trace.allValid step hstep

theorem CandidateExpr.checkStep_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.checkSteps) :
    step.Valid :=
  candidate.trace.allChecksValid step hstep

theorem CandidateExpr.isDefEqStep_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.isDefEqSteps) :
    step.Valid :=
  candidate.trace.allIsDefEqValid step hstep

/-- Normalize exactly the expression positions inspected by inductive
analysis. Each node is fully checked and then exposed with the ordinary
checker `whnf`; Pi domains retain their raw syntax, while bodies are traversed
under the structurally certified annotation-consumed local declarations used
by kernel checking. Every raw/consumed domain pair is also checked by an exact
successful ordinary-checker `isDefEq` run. The recursion budget is the
configured inductive fuel, while every checker run uses the configured
transparency/fuel.

The returned trace is only a candidate analysis view and operational
provenance. It is not stored in the kernel environment and acquires semantic
authority only after Verify reconstructs and refines every retained checker
run. -/
def buildCandidateExpr (e : Expr) : M (CandidateExpr e) := do
  let context ← readThe Context
  return ⟨context, ← loop context e context.fuel.inductiveFuel⟩
where
  loop (context : Context) (e : Expr) :
      Nat → Except Exception (CandidateExprTrace context e)
    | 0 => throw .deepRecursion
    | fuel + 1 => do
      match observeCandidateCheckType context e with
      | .error err => throw err
      | .ok ⟨inferred, checked⟩ =>
        match observeCandidateWhnf context e with
        | .error err => throw err
        | .ok ⟨view, valid⟩ =>
          match view, valid with
          | .forallE name domain body binderInfo, valid =>
            match hfresh : context.lctx.find? context.freshFVarId with
            | some _ =>
              throw (Exception.other
                "normalization candidate generated a duplicate free variable")
            | none =>
              let annotations ← buildCandidateTypeAnnotations domain
              let ⟨annotationsEq⟩ ← observeCandidateIsDefEq
                context domain annotations.consumed
              let domainCandidate ← loop context domain fuel
              let bodyContext :=
                context.pushLocalDecl name binderInfo
                  annotations.consumed
              let bodyCandidate ← loop bodyContext
                (body.instantiate1 context.freshExpr) fuel
              return .forallE context e inferred name domain body
                binderInfo hfresh annotations annotationsEq checked valid
                domainCandidate bodyCandidate
          | result, valid =>
            return .terminal context e inferred result checked valid

/-- One terminal recursive step of `buildCandidateExpr`, with its traversal
budget made explicit. This is the reusable reduction seam for exact producer
fixtures; all semantic evidence remains the ordinary checker executions
stored in the resulting trace. -/
theorem buildCandidateExpr_loop_of_whnf_nonForall
    (context : Context) (e inferred view : Expr) (fuel : Nat)
    (hcheck : CandidateCheckTypeStep.Valid
      ⟨context, e, inferred⟩)
    (hrun : CandidateWhnfStep.Valid ⟨context, e, view⟩)
    (hview : view.isForall = false) :
    buildCandidateExpr.loop context e (fuel + 1) =
      .ok (.terminal context e inferred view hcheck hrun) := by
  unfold buildCandidateExpr.loop
  rw [observeCandidateCheckType_of_run context e inferred hcheck]
  rw [observeCandidateWhnf_of_run context e view hrun]
  cases view <;>
    simp_all [Expr.isForall, Pure.pure, Except.pure]

/-- One forall recursive step of `buildCandidateExpr`, exposing the exact
child executions used at the decremented traversal budget. -/
theorem buildCandidateExpr_loop_of_whnf_forall
    (context : Context) (e inferred : Expr) (fuel : Nat)
    (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
    (hfresh : context.lctx.find? context.freshFVarId = none)
    (annotations : CandidateTypeAnnotations domain)
    (hannotations :
      buildCandidateTypeAnnotations domain = .ok annotations)
    (hannotationsEq : CandidateIsDefEqStep.Valid
      ⟨context, domain, annotations.consumed⟩)
    (hcheck : CandidateCheckTypeStep.Valid
      ⟨context, e, inferred⟩)
    (hrun : CandidateWhnfStep.Valid
      ⟨context, e, .forallE name domain body binderInfo⟩)
    (domainCandidate : CandidateExprTrace context domain)
    (bodyCandidate : CandidateExprTrace
      (context.pushLocalDecl name binderInfo annotations.consumed)
      (body.instantiate1 context.freshExpr))
    (hdomain :
      buildCandidateExpr.loop context domain fuel =
        .ok domainCandidate)
    (hbody :
      buildCandidateExpr.loop
          (context.pushLocalDecl name binderInfo annotations.consumed)
          (body.instantiate1 context.freshExpr) fuel =
        .ok bodyCandidate) :
    buildCandidateExpr.loop context e (fuel + 1) =
      .ok (.forallE context e inferred name domain body binderInfo
        hfresh annotations hannotationsEq hcheck hrun
        domainCandidate bodyCandidate) := by
  unfold buildCandidateExpr.loop
  simp only [observeCandidateCheckType_of_run context e inferred hcheck,
    observeCandidateWhnf_of_run context e
      (.forallE name domain body binderInfo) hrun]
  split
  · simp_all
  · simp [Bind.bind, Except.bind, hannotations,
      observeCandidateIsDefEq_of_run context domain
        annotations.consumed hannotationsEq,
      hdomain, hbody, Pure.pure, Except.pure]

/-- Every annotation choice on a successfully built candidate main spine
comes from the transparent annotation builder used by the ordinary producer.
This recovers validator-replay provenance from the executable traversal
itself; callers do not supply an independent annotation premise. -/
theorem CandidateExprTrace.validationAnnotations_of_loop
    {context : Context} {source : Expr} {fuel : Nat}
    {candidate : CandidateExprTrace context source}
    (h : buildCandidateExpr.loop context source fuel = .ok candidate) :
    candidate.validationAnnotations := by
  fun_induction buildCandidateExpr.loop context source fuel <;>
    simp_all
  case case5 =>
    simp only [Bind.bind, Except.bind] at h
    repeat' split at h
    all_goals try simp_all [Functor.map, Except.map]
    repeat' split at h
    all_goals try simp_all
    subst candidate
    constructor
    · apply CandidateTypeAnnotations.matches_of_build
      assumption
    · apply_assumption
      assumption
  case case6 =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst candidate
    trivial

/-- A successful ordinary candidate-expression call carries the complete
annotation provenance needed to replay family validation. -/
theorem CandidateExpr.validationAnnotations_of_build
    {context : Context} {source : Expr}
    {candidate : CandidateExpr source}
    (h : buildCandidateExpr source context = .ok candidate) :
    candidate.trace.validationAnnotations := by
  unfold buildCandidateExpr at h
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp_all
  simp [ReaderT.pure, Pure.pure, Except.pure] at h
  subst candidate
  apply CandidateExprTrace.validationAnnotations_of_loop
  assumption

/-- The context stored at the root of a successful expression candidate is
the exact reader context in which the ordinary builder was executed. -/
theorem CandidateExpr.context_eq_of_build
    {context : Context} {source : Expr}
    {candidate : CandidateExpr source}
    (h : buildCandidateExpr source context = .ok candidate) :
    candidate.context = context := by
  unfold buildCandidateExpr at h
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp_all
  simp [ReaderT.pure, Pure.pure, Except.pure] at h
  subst candidate
  rfl

/-- Erase the operational trace and retain only the analysis expression. -/
def normalizeCandidateExpr (e : Expr) : M Expr := do
  return (← buildCandidateExpr e).view

/-- A successful ordinary WHNF run to a non-Pi expression is exactly one
terminal step of the candidate traversal. This exposes the operational seam
used by Verify without duplicating the `ReaderT`/checker lift plumbing in
every certificate. -/
theorem buildCandidateExpr_of_whnf_nonForall
    (context : Context) (e inferred view : Expr)
    (hfuel : 0 < context.fuel.inductiveFuel)
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType e) =
        .ok inferred)
    (hrun :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) =
        .ok view)
    (hview : view.isForall = false) :
    buildCandidateExpr e context =
      .ok ⟨context, .terminal context e inferred view hcheck hrun⟩ := by
  cases hf : context.fuel.inductiveFuel with
  | zero => omega
  | succ fuel =>
    cases hresult :
        TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) with
    | error err => simp [hresult] at hrun
    | ok result =>
      have : result = view := by simpa [hresult] using hrun
      subst result
      unfold buildCandidateExpr
      unfold buildCandidateExpr.loop
      simp [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure,
        hf, observeCandidateCheckType_of_run context e inferred hcheck,
        observeCandidateWhnf_of_run context e view hrun]
      cases view <;>
        simp_all [ReaderT.pure, Pure.pure, Except.pure, Expr.isForall]

theorem normalizeCandidateExpr_of_whnf_nonForall
    (context : Context) (e inferred view : Expr)
    (hfuel : 0 < context.fuel.inductiveFuel)
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType e) =
        .ok inferred)
    (hrun :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) =
        .ok view)
    (hview : view.isForall = false) :
    normalizeCandidateExpr e context = .ok view := by
  simp [normalizeCandidateExpr, ReaderT.bind, Bind.bind,
    ReaderT.pure, Pure.pure, Except.bind, Except.pure,
    CandidateExpr.view, CandidateExprTrace.view,
    buildCandidateExpr_of_whnf_nonForall context e inferred view
      hfuel hcheck hrun hview]

/-- A dependent list retains the exact source position of each candidate. -/
inductive CandidateList {α : Type} (F : α → Type) : List α → Type
  | nil : CandidateList F []
  | cons : F a → CandidateList F as → CandidateList F (a :: as)

namespace CandidateList

def toList (f : (a : α) → F a → β) :
    CandidateList F source → List β
  | .nil => []
  | .cons head tail => f _ head :: tail.toList f

/-- Eliminate a source-indexed singleton without a partial list operation. -/
def singleton : CandidateList F [source] → F source
  | .cons head .nil => head

/-- A source-indexed singleton list is completely determined by its total
singleton projection.  This eta law lets retained producer witnesses be
reindexed at staged singleton APIs without inspecting or replacing their
candidate payload. -/
theorem singleton_eta (candidates : CandidateList F [source]) :
    candidates = .cons candidates.singleton .nil := by
  cases candidates with
  | cons head tail =>
      cases tail
      rfl

end CandidateList

/-- Candidate for one constructor; its header is always taken from `source`. -/
structure CandidateConstructor (source : Constructor) where
  type : CandidateExpr source.type

def CandidateConstructor.view
    (candidate : CandidateConstructor source) : Constructor :=
  { source with type := candidate.type.view }

/-- Candidate for one family type, computed before raw family insertion. -/
structure CandidateFamilyType (source : InductiveType) where
  type : CandidateExpr source.type

/-- Complete candidate for one family, with constructor traces computed only
after raw family insertion. -/
structure CandidateFamily (source : InductiveType) where
  familyType : CandidateFamilyType source
  constructors :
    CandidateList CandidateConstructor source.ctors

/-- Project the pre-family candidate spine from a complete dependent family
candidate list without erasing source indices or using a parallel list. -/
def CandidateList.familyTypes :
    {sources : List InductiveType} →
      CandidateList CandidateFamily sources →
      CandidateList CandidateFamilyType sources
  | [], .nil => .nil
  | _ :: _, .cons family families =>
    .cons family.familyType families.familyTypes

def CandidateFamily.view (candidate : CandidateFamily source) : InductiveType :=
  { source with
    type := candidate.familyType.type.view
    ctors := candidate.constructors.toList fun _ ctor => ctor.view }

def normalizeCandidateConstructor
    (ctor : Constructor) : M (CandidateConstructor ctor) := do
  return ⟨← buildCandidateExpr ctor.type⟩

/-- The root context stored by a successful constructor normalization is the
exact post-family reader context used for that traversal. -/
theorem CandidateConstructor.context_eq_of_normalize
    {context : Context} {source : Constructor}
    {candidate : CandidateConstructor source}
    (h : normalizeCandidateConstructor source context = .ok candidate) :
    candidate.type.context = context := by
  unfold normalizeCandidateConstructor at h
  simp only [ReaderT.bind, Bind.bind] at h
  cases hbuild : buildCandidateExpr source.type context with
  | error error =>
      simp [Except.bind, hbuild] at h
  | ok type =>
      simp [Except.bind, ReaderT.pure, Pure.pure, Except.pure, hbuild] at h
      subst candidate
      exact CandidateExpr.context_eq_of_build hbuild

def normalizeCandidateFamilyType
    (indType : InductiveType) : M (CandidateFamilyType indType) := do
  return ⟨← buildCandidateExpr indType.type⟩

/-- A successful family-type normalization carries the annotation provenance
of its underlying executable expression traversal. -/
theorem CandidateFamilyType.validationAnnotations_of_normalize
    {context : Context} {source : InductiveType}
    {candidate : CandidateFamilyType source}
    (h : normalizeCandidateFamilyType source context = .ok candidate) :
    candidate.type.trace.validationAnnotations := by
  unfold normalizeCandidateFamilyType at h
  simp only [ReaderT.bind, Bind.bind] at h
  cases hbuild : buildCandidateExpr source.type context with
  | error error =>
      simp [Except.bind, hbuild] at h
  | ok type =>
      simp [Except.bind, ReaderT.pure, Pure.pure, Except.pure, hbuild] at h
      subst candidate
      exact type.validationAnnotations_of_build hbuild

/-- The root context stored by a successful family-type normalization is the
exact pre-family reader context used for that traversal. -/
theorem CandidateFamilyType.context_eq_of_normalize
    {context : Context} {source : Lean.InductiveType}
    {candidate : CandidateFamilyType source}
    (h : normalizeCandidateFamilyType source context = .ok candidate) :
    candidate.type.context = context := by
  unfold normalizeCandidateFamilyType at h
  simp only [ReaderT.bind, Bind.bind] at h
  cases hbuild : buildCandidateExpr source.type context with
  | error error =>
      simp [Except.bind, hbuild] at h
  | ok type =>
      simp [Except.bind, ReaderT.pure, Pure.pure, Except.pure, hbuild] at h
      subst candidate
      exact CandidateExpr.context_eq_of_build hbuild

def normalizeCandidateConstructorList :
    (ctors : List Constructor) →
      M (CandidateList CandidateConstructor ctors)
  | [] => return .nil
  | ctor :: ctors => do
    return .cons (← normalizeCandidateConstructor ctor)
      (← normalizeCandidateConstructorList ctors)

def normalizeCandidateFamilyTypeList :
    (types : List InductiveType) →
      M (CandidateList CandidateFamilyType types)
  | [] => return .nil
  | indType :: types => do
    return .cons (← normalizeCandidateFamilyType indType)
      (← normalizeCandidateFamilyTypeList types)

def normalizeCandidateFamilyList :
    {types : List InductiveType} →
      CandidateList CandidateFamilyType types →
      M (CandidateList CandidateFamily types)
  | [], .nil => return .nil
  | indType :: _, .cons familyType tail => do
    return .cons
      { familyType,
        constructors := ←
          normalizeCandidateConstructorList indType.ctors }
      (← normalizeCandidateFamilyList tail)

/-- Exact successful traversal of an arbitrary source-indexed family-type
list. The dependent indices prevent a proof for one metadata position from
being reused at another position or from silently truncating the source. -/
inductive CandidateFamilyTypeListProduced (context : Context) :
    {sources : List InductiveType} →
      CandidateList CandidateFamilyType sources → Prop where
  | nil : CandidateFamilyTypeListProduced context .nil
  | cons
      (head : normalizeCandidateFamilyType source context = .ok candidate)
      (tail : CandidateFamilyTypeListProduced context candidates) :
      CandidateFamilyTypeListProduced context (.cons candidate candidates)

/-- A source-indexed family-type traversal determines the complete executable
list result for any length, without a fixture-specific list reduction. -/
theorem CandidateFamilyTypeListProduced.normalize
    {sources : List InductiveType}
    {candidates : CandidateList CandidateFamilyType sources}
    (run : CandidateFamilyTypeListProduced context candidates) :
    normalizeCandidateFamilyTypeList sources context = .ok candidates := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    unfold normalizeCandidateFamilyTypeList
    simp only [ReaderT.bind, Bind.bind]
    rw [head, ih]
    rfl

/-- A successful singleton family-type traversal retains the annotation
provenance of the exact candidate selected at its sole source position. -/
theorem CandidateFamilyTypeListProduced.singleton_validationAnnotations
    {context : Context} {source : Lean.InductiveType}
    {candidates : CandidateList CandidateFamilyType [source]}
    (run : CandidateFamilyTypeListProduced context candidates) :
    candidates.singleton.type.trace.validationAnnotations := by
  cases run with
  | cons head tail =>
      cases tail
      exact CandidateFamilyType.validationAnnotations_of_normalize head

/-- A successful singleton family-type traversal stores its exact traversal
context at the candidate root. -/
theorem CandidateFamilyTypeListProduced.singleton_context_eq
    {context : Context} {source : Lean.InductiveType}
    {candidates : CandidateList CandidateFamilyType [source]}
    (run : CandidateFamilyTypeListProduced context candidates) :
    candidates.singleton.type.context = context := by
  cases run with
  | cons head tail =>
      cases tail
      exact CandidateFamilyType.context_eq_of_normalize head

/-- Exact successful traversal of an arbitrary source-indexed constructor
list in one post-family context. Every candidate remains indexed by its source
constructor, so ordering, length, and header provenance are preserved by the
type rather than recovered from an erased list equality. -/
inductive CandidateConstructorListProduced (context : Context) :
    {sources : List Constructor} →
      CandidateList CandidateConstructor sources → Prop where
  | nil : CandidateConstructorListProduced context .nil
  | cons
      (head : normalizeCandidateConstructor source context = .ok candidate)
      (tail : CandidateConstructorListProduced context candidates) :
      CandidateConstructorListProduced context (.cons candidate candidates)

/-- A source-indexed constructor traversal determines the complete executable
list result for any length, with no `zip`, partial lookup, or fixture-specific
cons-chain reduction. -/
theorem CandidateConstructorListProduced.normalize
    {sources : List Constructor}
    {candidates : CandidateList CandidateConstructor sources}
    (run : CandidateConstructorListProduced context candidates) :
    normalizeCandidateConstructorList sources context = .ok candidates := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    unfold normalizeCandidateConstructorList
    simp only [ReaderT.bind, Bind.bind]
    rw [head, ih]
    rfl

/-- A successful singleton constructor traversal stores its exact traversal
context at the candidate root. -/
theorem CandidateConstructorListProduced.singleton_context_eq
    {context : Context} {source : Constructor}
    {candidates : CandidateList CandidateConstructor [source]}
    (run : CandidateConstructorListProduced context candidates) :
    candidates.singleton.type.context = context := by
  cases run with
  | cons head tail =>
      cases tail
      exact CandidateConstructor.context_eq_of_normalize head

/-- Exact successful assembly of complete family candidates from an already
source-indexed family-type list. Each constructor traversal is tied to the
corresponding family source, and the tail remains tied to the remaining family
sources. This is the reusable ordered-list boundary needed before mutual-block
staging. -/
inductive CandidateFamilyListProduced (context : Context) :
    {sources : List InductiveType} →
      CandidateList CandidateFamilyType sources →
      CandidateList CandidateFamily sources → Prop where
  | nil : CandidateFamilyListProduced context .nil .nil
  | cons
      (constructors : CandidateConstructorListProduced
        context family.constructors)
      (tail : CandidateFamilyListProduced context familyTypes families) :
      CandidateFamilyListProduced context
        (.cons family.familyType familyTypes) (.cons family families)

/-- Source-indexed family assembly determines the exact executable family-list
result for arbitrary list lengths. -/
theorem CandidateFamilyListProduced.normalize
    {sources : List InductiveType}
    {familyTypes : CandidateList CandidateFamilyType sources}
    {families : CandidateList CandidateFamily sources}
    (run : CandidateFamilyListProduced context familyTypes families) :
    normalizeCandidateFamilyList familyTypes context = .ok families := by
  induction run with
  | nil => rfl
  | cons constructors tail ih =>
    unfold normalizeCandidateFamilyList
    simp only [ReaderT.bind, Bind.bind]
    rw [constructors.normalize, ih]
    rfl

/-- Singleton family assembly reuses, without replacement, the family-type
candidate produced in the pre-family environment. -/
theorem CandidateFamilyListProduced.singleton_familyType
    {context : Context} {source : Lean.InductiveType}
    {familyTypes : CandidateList CandidateFamilyType [source]}
    {families : CandidateList CandidateFamily [source]}
    (run : CandidateFamilyListProduced context familyTypes families) :
    families.singleton.familyType = familyTypes.singleton := by
  cases run with
  | cons constructors tail =>
      cases tail
      rfl

/-- Singleton family assembly exposes the exact source-indexed constructor
traversal retained for its sole family. -/
theorem CandidateFamilyListProduced.singleton_constructors
    {context : Context} {source : Lean.InductiveType}
    {familyTypes : CandidateList CandidateFamilyType [source]}
    {families : CandidateList CandidateFamily [source]}
    (run : CandidateFamilyListProduced context familyTypes families) :
    CandidateConstructorListProduced context
      families.singleton.constructors := by
  cases run with
  | cons constructors tail =>
      cases tail
      exact constructors

/-- A successful singleton family assembly can be reindexed directly by the
family-type payload retained in its assembled result.  This dependent eta law
avoids rewriting the input list underneath the execution witness. -/
theorem CandidateFamilyListProduced.singleton_reindex
    {context : Context} {source : Lean.InductiveType}
    {familyTypes : CandidateList CandidateFamilyType [source]}
    {families : CandidateList CandidateFamily [source]}
    (run : CandidateFamilyListProduced context familyTypes families) :
    CandidateFamilyListProduced context
      (.cons families.singleton.familyType .nil) families := by
  cases run with
  | cons constructors tail =>
      cases tail
      exact .cons constructors .nil

/-- Shape-preserving output of the executable normalization-candidate pass.
The dependent family/constructor lists prevent positional provenance from
being silently reused for a different inductive request. Names, ordering, and
record headers come from the indexed source; only expression payloads are
reconstructed from candidate traces. -/
structure NormalizationCandidate (source : List InductiveType) where
  families : CandidateList CandidateFamily source

def NormalizationCandidate.view
    (candidate : NormalizationCandidate source) : List InductiveType :=
  candidate.families.toList fun _ family => family.view

/-- One exact family-type traversal result together with the source-indexed
operational witness that produced it.  The witness is provenance for later
Verify staging; it carries no Theory semantics. -/
structure CandidateFamilyTypeListExecution (context : Context)
    (sources : List InductiveType) where
  candidates : CandidateList CandidateFamilyType sources
  produced : CandidateFamilyTypeListProduced context candidates

/-- Run the existing family-type normalizer while retaining its exact
source-ordered traversal equations.  Errors and candidate data are unchanged. -/
def executeCandidateFamilyTypeList (context : Context) :
    (sources : List InductiveType) →
      Except Exception (CandidateFamilyTypeListExecution context sources)
  | [] => .ok ⟨.nil, .nil⟩
  | source :: sources =>
      match hhead : normalizeCandidateFamilyType source context with
      | .error error => .error error
      | .ok head =>
          match executeCandidateFamilyTypeList context sources with
          | .error error => .error error
          | .ok tail => .ok {
              candidates := .cons head tail.candidates
              produced := .cons (by simpa using hhead) tail.produced }

/-- One exact constructor traversal result together with its source-indexed
operational witness. -/
structure CandidateConstructorListExecution (context : Context)
    (sources : List Constructor) where
  candidates : CandidateList CandidateConstructor sources
  produced : CandidateConstructorListProduced context candidates

/-- Run the existing constructor normalizer while retaining its exact
source-ordered traversal equations. -/
def executeCandidateConstructorList (context : Context) :
    (sources : List Constructor) →
      Except Exception (CandidateConstructorListExecution context sources)
  | [] => .ok ⟨.nil, .nil⟩
  | source :: sources =>
      match hhead : normalizeCandidateConstructor source context with
      | .error error => .error error
      | .ok head =>
          match executeCandidateConstructorList context sources with
          | .error error => .error error
          | .ok tail => .ok {
              candidates := .cons head tail.candidates
              produced := .cons (by simpa using hhead) tail.produced }

/-- One exact family/constructor assembly result together with both dependent
source lists retained by the ordinary traversal. -/
structure CandidateFamilyListExecution (context : Context)
    {sources : List InductiveType}
    (familyTypes : CandidateList CandidateFamilyType sources) where
  candidates : CandidateList CandidateFamily sources
  produced : CandidateFamilyListProduced context familyTypes candidates

/-- Run the existing family assembler while retaining each constructor-list
execution.  This is an operational refinement of
`normalizeCandidateFamilyList`, not an additional acceptance premise. -/
def executeCandidateFamilyList (context : Context) :
    {sources : List InductiveType} →
    (familyTypes : CandidateList CandidateFamilyType sources) →
      Except Exception (CandidateFamilyListExecution context familyTypes)
  | [], .nil => .ok ⟨.nil, .nil⟩
  | source :: _, .cons familyType familyTypes =>
      match executeCandidateConstructorList context source.ctors with
      | .error error => .error error
      | .ok constructors =>
          match executeCandidateFamilyList context familyTypes with
          | .error error => .error error
          | .ok tail =>
            let family : CandidateFamily source := {
              familyType
              constructors := constructors.candidates }
            .ok {
              candidates := .cons family tail.candidates
              produced := by
                change CandidateFamilyListProduced context
                  (.cons family.familyType familyTypes)
                  (.cons family tail.candidates)
                exact .cons constructors.produced tail.produced }

/-- Detailed operational result of `buildNormalizationCandidate`.

The ordinary result erases to `candidate`.  The remaining fields retain the
validator-selected statistics, intermediate environment, and exact list
traversals already executed by the same call.  Verify uses these equations as
staging provenance; all semantic authority still comes from the D1--D4
interpreters. -/
structure NormalizationCandidateExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) where
  validationContext : Context
  stats : InductiveStats
  familyTypes : CandidateFamilyTypeListExecution
    { candidateContext with lctx := {} } types
  familyEnv : Environment
  declareRun : declareInductiveTypes stats nparams types.toArray
    numNested isUnsafe validationContext = .ok familyEnv
  constructorRun : checkConstructors types.toArray stats isUnsafe
    { validationContext with env := familyEnv } = .ok ()
  families : CandidateFamilyListExecution
    { candidateContext with env := familyEnv, lctx := {} }
    familyTypes.candidates

def NormalizationCandidateExecution.candidate
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext) : NormalizationCandidate types :=
  ⟨execution.families.candidates⟩

/-- The post-family half of the detailed ordinary execution. -/
def buildNormalizationCandidateExecutionAfterValidation
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context)
    (stats : InductiveStats) :
    M (NormalizationCandidateExecution nparams types numNested isUnsafe
      candidateContext) :=
  fun validationContext =>
    match executeCandidateFamilyTypeList
        { candidateContext with lctx := {} } types with
    | .error error => .error error
    | .ok familyTypes =>
      match hdeclare : declareInductiveTypes stats nparams types.toArray
          numNested isUnsafe validationContext with
      | .error error => .error error
      | .ok familyEnv =>
        match hconstructors : checkConstructors types.toArray stats isUnsafe
            { validationContext with env := familyEnv } with
        | .error error => .error error
        | .ok () =>
          match executeCandidateFamilyList
              { candidateContext with env := familyEnv, lctx := {} }
              familyTypes.candidates with
          | .error error => .error error
          | .ok families => .ok {
              validationContext
              stats
              familyTypes
              familyEnv
              declareRun := by simpa using hdeclare
              constructorRun := by simpa using hconstructors
              families }

/-- A retained successful post-validation execution exposes exactly the
statistics and reader context supplied by the family validator. -/
theorem NormalizationCandidateExecution.fields_of_afterValidation
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext)
    (stats : InductiveStats) (validationContext : Context)
    (h : buildNormalizationCandidateExecutionAfterValidation nparams types
        numNested isUnsafe candidateContext stats validationContext =
      .ok execution) :
    execution.stats = stats ∧
      execution.validationContext = validationContext := by
  unfold buildNormalizationCandidateExecutionAfterValidation at h
  repeat' split at h
  all_goals try simp_all
  subst execution
  exact ⟨rfl, rfl⟩

/-- Execute the ordinary singleton/mutual candidate pass while retaining the
exact operational provenance erased by the public candidate result. -/
def buildNormalizationCandidateExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) :
    Except Exception (NormalizationCandidateExecution nparams types
      numNested isUnsafe candidateContext) :=
  checkInductiveTypes nparams types.toArray (fun stats =>
    buildNormalizationCandidateExecutionAfterValidation nparams types
      numNested isUnsafe candidateContext stats) candidateContext

/-- Run the generic one-pass candidate producer at the same two environments
as kernel inductive checking: family types in the input environment, then
constructor types after insertion of every raw family constant.

This repeats the ordinary family/constructor validity checks so a candidate
cannot be obtained from metadata already rejected at those stages. The Theory
analyzer and Verify semantic certificate remain separate downstream gates. -/
def buildNormalizationCandidate
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) :
    M (NormalizationCandidate types) :=
  -- Family validation retains its parameter/index telescope while invoking
  -- the continuation.  That context is required by `checkConstructors`, whose
  -- parameter checks refer to the free variables recorded in `stats`, but it
  -- is not part of the closed metadata being normalized.  Snapshot the entry
  -- context so both candidate traversals use one stable fresh-name provenance
  -- and an empty local context; only the staged kernel environment changes.
  fun candidateContext =>
  let indTypes := types.toArray
  checkInductiveTypes nparams indTypes (fun stats => do
    let familyTypes ←
      withReader (fun _ : Context => { candidateContext with lctx := {} }) do
        normalizeCandidateFamilyTypeList types
    let familyEnv ←
      declareInductiveTypes stats nparams indTypes numNested isUnsafe
    withEnv familyEnv do
      checkConstructors indTypes stats isUnsafe
      let families ←
        withReader (fun _ : Context =>
          { candidateContext with env := familyEnv, lctx := {} }) do
          normalizeCandidateFamilyList familyTypes
      return ⟨families⟩) candidateContext

/-- Erase a retained successful execution back to the unchanged public
candidate producer.  The family-validation equation supplies the continuation
boundary selected by `checkInductiveTypes`; every later rewrite comes from an
operation already stored in `execution`. -/
theorem NormalizationCandidateExecution.produces
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext)
    (validationRun : ∀ {α} (k : InductiveStats → M α),
      checkInductiveTypes nparams types.toArray k candidateContext =
        k execution.stats execution.validationContext) :
    buildNormalizationCandidate nparams types numNested isUnsafe
        candidateContext = .ok execution.candidate := by
  unfold buildNormalizationCandidate
  rw [validationRun]
  simp only [ReaderT.bind, Bind.bind]
  rw [show
    (withReader (fun _ : Context =>
        { candidateContext with lctx := {} })
      (normalizeCandidateFamilyTypeList types)) execution.validationContext =
        .ok execution.familyTypes.candidates by
      change normalizeCandidateFamilyTypeList types
        { candidateContext with lctx := {} } = _
      exact execution.familyTypes.produced.normalize]
  simp only [Except.bind]
  rw [execution.declareRun]
  unfold withEnv
  change (ReaderT.bind
      (checkConstructors types.toArray execution.stats isUnsafe)
      (fun _ => ReaderT.bind
        (withReader (fun _ : Context =>
          { candidateContext with
            env := execution.familyEnv, lctx := {} })
          (normalizeCandidateFamilyList execution.familyTypes.candidates))
        (fun families => pure
          (⟨families⟩ : NormalizationCandidate types))))
      ({ execution.validationContext with
        env := execution.familyEnv } : Context) = _
  simp only [ReaderT.bind, Bind.bind]
  rw [execution.constructorRun]
  simp only [Except.bind]
  rw [show
    (withReader (fun _ : Context =>
        { candidateContext with
          env := execution.familyEnv, lctx := {} })
      (normalizeCandidateFamilyList execution.familyTypes.candidates))
      { execution.validationContext with env := execution.familyEnv } =
        .ok execution.families.candidates by
      change normalizeCandidateFamilyList execution.familyTypes.candidates
        { candidateContext with env := execution.familyEnv, lctx := {} } = _
      exact execution.families.produced.normalize]
  rfl

#guard_named_axioms Ix.Theory.Named.AddInductive.buildCandidateExpr [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.observeCandidateIsDefEq_of_run [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.buildCandidateExpr_loop_of_whnf_forall [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateTypeAnnotationTrace.build [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateTypeAnnotationTrace.build_consumed [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.buildCandidateTypeAnnotations [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateTypeAnnotations.matches_of_build [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.buildCandidateCheckType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.buildNormalizationCandidate [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateFamilyTypeListProduced.normalize [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateConstructorListProduced.normalize [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateFamilyListProduced.normalize [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateList.singleton []

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.storedSpine [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.spineLength [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.rootWhnf_valid [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.terminalContext_lparams [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.parameterList_length [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.checkInductiveTypes_loop_of_candidate [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.FamilyValidationRun [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.FamilyValidationRun.parameters [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExprTrace.FamilyValidationRun.numIndices [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExpr.step_valid [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExpr.checkStep_valid [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateExpr.isDefEqStep_valid [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateWhnfStep.innerRun [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateCheckTypeStep.innerRun [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.CandidateIsDefEqStep.innerRun [propext, Classical.choice, Quot.sound]

def declareConstructors (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) : M Environment :=
  fun c => indTypes.foldlM (init := c.env) fun env indType => do
    let (_, env) ← indType.ctors.foldlM (init := (0, env)) fun (cidx, env) ctor => do
      let type := ctor.type
      let rec arity i
        | .forallE _ _ body _ => arity (i+1) body
        | _ => i
      let arity := arity 0 type
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, env.add <| .ctorInfo {
        type, cidx, isUnsafe
        levelParams := c.lparams
        name := ctor.name
        induct := indType.name
        numParams := stats.params.size
        numFields := assert! arity ≥ stats.params.size; arity - stats.params.size
      })
    pure env

/-- Return true if recursor can map into any universe -/
def isLargeEliminator (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  if stats.isNotZero then return true
  let #[indType] := indTypes | return false
  match indType.ctors with
  | [] => return true
  | [ctor] =>
    let rec loop type i toCheck
    | 0 => throw .deepRecursion
    | fuel+1 => do
      if let .forallE name dom body bi := type then
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
          let mut toCheck := toCheck
          if i ≥ stats.params.size then
            if !(← ensureType dom).sortLevel!.isAlwaysZero then
              toCheck := toCheck.push arg
          loop (body.instantiate1 arg) (i + 1) toCheck fuel
      else
        return toCheck.all type.getAppArgs.contains
    loop ctor.type 0 #[] (← readThe Context).fuel.inductiveFuel
  | _ => return false

/-- Search the kernel's elimination-universe name sequence (`u`, `u_1`, …)
for its first entry not already used by the inductive declaration.  Among
`lparams.length + 1` distinct candidates at least one is available; the
zero-fuel branch is therefore only a totality fallback. -/
def getFreshElimParam.loop (lparams : List Name) (u : Name) (i : Nat) :
    Nat → Name
  | 0 => u
  | fuel + 1 =>
      if lparams.contains u then
        loop lparams ((`u).appendIndexAfter i) (i + 1) fuel
      else
        u

def getFreshElimParam (lparams : List Name) : Name :=
  getFreshElimParam.loop lparams `u 1 (lparams.length + 1)

def getElimLevel (stats : InductiveStats) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let {lparams, ..} ← read
  return .param (getFreshElimParam lparams)

/-- The constructor-shape fragment of the kernel's K-target test. A visible
Pi is accepted only while it belongs to the shared parameter prefix; the
first visible field makes the target ineligible. -/
def isKTargetCtor (nparams : Nat) : Nat → Expr → Bool
  | i, .forallE _ _ body _ => i < nparams && isKTargetCtor nparams (i + 1) body
  | _, _ => true

def isKTarget (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  let #[indType] := indTypes | return false
  unless stats.resultLevel.isAlwaysZero do return false
  let [ctor] := indType.ctors | return false
  return isKTargetCtor stats.params.size 0 ctor.type

@[inline] def getIIndices (stats : InductiveStats) (t : Expr) : Nat × Array Expr :=
  ((isValidIndApp? stats t).get!, t.getAppArgs[stats.params.size:])

-- FIXME: The function below has been exploded into nested loops as standalone functions
-- because I couldn't get them all to compile together as `let rec`s.
namespace mkRecInfos

def loopArgs1 (stats : InductiveStats) (type : Expr) (i : Nat) (indices : Array Expr)
    (fuel : Nat) (k : Array Expr → M α) : M α := match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < stats.params.size then
        loopArgs1 stats (← whnf <| body.instantiate1 stats.params[i]!) (i + 1) indices fuel k
      else
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      k indices

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let ctx ← readThe Context
    loopArgs1 stats (← whnf indTypes[dIdx].type) 0 #[] ctx.fuel.inductiveFuel fun indices =>
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    withLocalDecl `t .default (consumeTypeAnnotations tTy) fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then (`motive).appendIndexAfter (dIdx+1) else `motive
    withLocalDecl name .default (consumeTypeAnnotations motiveTy) fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push { motive, minors := #[], indices, major }) k
  else
    k recInfos
termination_by indTypes.size - dIdx

variable (stats : InductiveStats) in
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array Expr → M α) : M α := do
  loop t 0 #[] #[] (← readThe Context).fuel.inductiveFuel
where
  loop t i bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        loop (body.instantiate1 param) (i + 1) bu u fuel
      else
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
        let bu := bu.push arg
        let u := if (← isRecArg stats dom).isSome then u.push arg else u
        loop (body.instantiate1 arg) (i + 1) bu u fuel
    else k t bu u

def loopUArgs (ui : Expr) (k : Expr → Array Expr → M α) : M α := do
  loop (← whnf (← inferType ui)) #[] (← readThe Context).fuel.inductiveFuel
where
  loop uiTy xs
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := uiTy then
      withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
      loop (← whnf <| body.instantiate1 arg) (xs.push arg) fuel
    else
      k uiTy xs

variable (stats : InductiveStats) (u : Array Expr) (recInfos : Array RecInfo) in
def loopU (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let viTy ← loopUArgs ui fun uiTy xs => do
      let (itIdx, itIndices) := getIIndices stats uiTy
      return (← getLCtx).mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    withLocalDecl vName .default (consumeTypeAnnotations viTy) fun vi => do
    loopU (i + 1) (v.push vi) k
  else
    k v
termination_by u.size - i

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
def loopCtors (recInfos : Array RecInfo)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    loopCtorArgs stats ctor.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopU stats u recInfos 0 #[] fun v => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName .default (consumeTypeAnnotations minorTy) fun minor => do
    let recInfos := recInfos.modify dIdx fun s => { s with minors := s.minors.push minor }
    loopCtors recInfos ctors k
  | [] => k recInfos

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
def loopInd2 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let indTypeName := indType.name
    loopCtors stats indTypeName dIdx recInfos indType.ctors fun recInfos =>
    loopInd2 (dIdx + 1) recInfos k
  else
    k recInfos
termination_by indTypes.size - dIdx

end mkRecInfos

def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α :=
  mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] fun recInfos =>
  mkRecInfos.loopInd2 stats indTypes 0 recInfos k

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

def mkRecRules (indTypes : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (dIdx : Nat) (motives : Array Expr) (minors : Array Expr) :
    StateT Nat M (List RecursorRule) := do
  let d := indTypes[dIdx]!
  let lvls := getRecLevels elimLevel stats.levels
  let mut rules := #[]
  for ctor in d.ctors do
    let rule ← fun minorIdx => mkRecInfos.loopCtorArgs stats ctor.type fun _ bu u =>
      let rec loopU i (v : Array Expr) k := do
        if _h : i < u.size then
          let ui := u[i]
          let val ← mkRecInfos.loopUArgs ui fun uiTy xs => do
            let (itIdx, itIndices) := getIIndices stats uiTy
            let val := .const (mkRecName indTypes[itIdx]!.name) lvls
            let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params) motives) minors) itIndices
            return (← getLCtx).mkLambda xs <| val.app (mkAppN ui xs)
          loopU (i + 1) (v.push val) k
        else
          k v
      termination_by u.size - i
      loopU 0 #[] fun v => do
      let lctx ← getLCtx
      let rule := {
        ctor := ctor.name
        nfields := bu.size
        rhs := lctx.mkLambda stats.params <| lctx.mkLambda motives <|
          lctx.mkLambda minors <| lctx.mkLambda bu <|
          mkAppN (mkAppN minors[minorIdx]! bu) v
      }
      return (rule, minorIdx + 1)
    rules := rules.push rule
  return rules.toList

/-- Defensively type-checks the generated recursors.

`run` installs a recursor and its computation rules without re-checking them. This verifies that
(1) each recursor's type is well typed, and (2) each computation rule is type-preserving: reducing
the recursor applied to a constructor yields a term whose type is the recursor's declared result
type. This catches a recursor whose minor-premise type and reduction rule disagree; checking only
that a rule's right-hand side has *some* type is insufficient, because an under-applied minor
premise is still a well-typed (function) term. -/
def checkRecursors (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (motives minors : Array Expr) : M Unit := do
  let {lparams, ..} ← read
  let lvls := getRecLevels elimLevel stats.levels
  withLParams (getRecLevelParams elimLevel lparams) do
  for h : dIdx in [:indTypes.size] do
    let indType := indTypes[dIdx]
    let recName := mkRecName indType.name
    let recCi ← (← read).env.get recName
    -- (1) The recursor type must be well typed.
    _ ← (TypeChecker.checkType recCi.type : TypeChecker.M Expr)
    let recPre := mkAppN (mkAppN (mkAppN (.const recName lvls) stats.params) motives) minors
    -- (2) Each computation rule must preserve types.
    for ctor in indType.ctors do
      mkRecInfos.loopCtorArgs stats ctor.type fun t bu _ => do
        let (_, itIndices) := getIIndices stats t
        let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
        let lhs := (mkAppN recPre itIndices).app introApp
        let expected ← inferType lhs
        let reduct ← whnf lhs
        let actual ← inferType reduct
        unless ← isDefEq actual expected do
          throw <| .other s!"generated recursor computation rule for '{ctor.name
            }' is not type-preserving"

def run (nparams : Nat) (types : List InductiveType) (numNested : Nat) : M Environment := do
  let isUnsafe := (← read).safety != .safe
  let indTypes := types.toArray
  let {lparams, ..} ← read
  Environment.checkDuplicatedUnivParams lparams
  checkInductiveTypes nparams indTypes fun stats => do
  withEnv (← declareInductiveTypes stats nparams indTypes numNested isUnsafe) do
  checkConstructors indTypes stats isUnsafe
  withEnv (← declareConstructors stats indTypes isUnsafe) do
  let elimLevel ← getElimLevel stats indTypes
  mkRecInfos stats indTypes elimLevel fun recInfos => do
  let motives := recInfos.map (·.motive)
  let minors := recInfos.flatMap (·.minors)
  let numMinors := minors.size
  let numMotives := motives.size
  let all := indTypes.map (·.name) |>.toList
  let lctx ← getLCtx
  let k ← isKTarget stats indTypes
  let isUnsafe := (← read).safety != .safe
  StateT.run' (s := 0) do
  let mut env ← getEnv
  let {allowPrimitive, ..} ← read
  for h : dIdx in [:indTypes.size] do
    let indType := indTypes[dIdx]
    let info := recInfos[dIdx]!
    let ty :=
      lctx.mkForall stats.params <|
      lctx.mkForall motives <|
      lctx.mkForall minors <|
      lctx.mkForall info.indices <|
      lctx.mkForall #[info.major] <|
      .app (mkAppN info.motive info.indices) info.major
    let rules ← mkRecRules indTypes elimLevel stats dIdx motives minors
    let name := mkRecName indType.name
    env.checkName name allowPrimitive
    env := env.add <| .recInfo {
      levelParams := getRecLevelParams elimLevel lparams
      type := ty.inferImplicit 1000 false -- note: flag has reversed polarity from C++
      numParams := stats.params.size
      numIndices := stats.nindices[dIdx]!
      name, all, numMotives, numMinors, rules, k, isUnsafe
    }
  withEnv env <| checkRecursors indTypes elimLevel stats motives minors
  pure env

end AddInductive

namespace ElimNestedInductive

structure Result where
  ngen : NameGenerator
  nparams : Nat
  lctx : LocalContext
  params : Array Expr -- the fvars declared in `lctx`
  aux2nested : NameMap Expr -- exprs are open over `params`, like the C++ `m_aux2nested`
  types : List InductiveType

instance [MonadStateOf NameGenerator m] : MonadNameGenerator m where
  getNGen := get
  setNGen := set

namespace Result

def getNestedIfAuxCtor (r : Result) (env' : Environment) (c : Name) : Option (Expr × Name) := do
  let .ctorInfo { induct, .. } ← env'.find? c | none
  return (← r.aux2nested.find? induct, induct)

def restoreCtorName (r : Result) (env' : Environment) (c : Name) : Name := Id.run do
  let (e, name) := (r.getNestedIfAuxCtor env' c).get!
  let .const I _ := e.getAppFn | unreachable!
  c.replacePrefix name I

def restoreNested (r : Result) (env' : Environment) (e : Expr)
    (auxRec : NameMap Name := {}) : Expr :=
  Id.run <| StateT.run' (s := { namePrefix := `_nested_fresh : NameGenerator }) do
  let pi := e.isForall
  let mut e := e
  let mut As := #[]
  let mut lctx : LocalContext := {}
  for _ in [:r.nparams] do
    match e with
    | .forallE name dom body bi | .lam name dom body bi =>
      let id := ⟨← mkFreshId⟩
      lctx := lctx.mkLocalDecl id name dom bi
      let arg := .fvar id
      e := body.instantiate1 arg
      As := As.push arg
    | _ => unreachable!
  e := e.replace fun t => do
    if let .const c ls := t then
      if let some recName := auxRec.find? c then
        return .const recName ls
    let .const c _ := t.getAppFn | none
    if let some nested := r.aux2nested.find? c then
      let args := t.getAppArgs
      assert! args.size ≥ r.nparams
      return mkAppRange ((nested.abstract r.params).instantiateRev As) r.nparams args.size args
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    let nested' := (nested.abstract r.params).instantiateRev As
    nested'.withApp fun I I_args => do
    let .const I_c I_ls := I | unreachable!
    let c' := .const (c.replacePrefix auxI_name I_c) I_ls
    return mkAppRange (mkAppN c' I_args) r.nparams args.size args
  return if pi then lctx.mkForall As e else lctx.mkLambda As e

end Result

structure State where
  ngen : NameGenerator := { namePrefix := `_nested_fresh }
  nestedAux : Array (Expr × Name) := {}
  lvls : List Level
  newTypes : Array InductiveType
  nextIdx : Nat := 1
  deriving Inhabited

abbrev M := ReaderT Environment <| StateT State <| Except Exception

instance : MonadNameGenerator M where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

-- TODO: remove partial
partial def mkUniqueName (n : Name) : M Name := fun env s =>
  let rec loop i :=
    let r := n.appendIndexAfter i
    if env.contains r then
      loop (i + 1)
    else
      pure (r, { s with nextIdx := i + 1 })
  loop s.nextIdx

def illFormed : Exception :=
  .other "invalid nested inductive datatype, ill-formed declaration"

def replaceParams (params : Array Expr) (e : Expr) (As : Array Expr) : M Expr := do
  assert! As.size == params.size
  return (e.abstract As).instantiateRev params

/-- IF `e` is of the form `I Ds is` where
  1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
  2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
THEN return the `inductive_val` in the `constant_info` associated with `I`.
Otherwise, return none. -/
def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  let env ← read
  let some (.inductInfo ci) := env.find? fn | return none
  let args := e.getAppArgs
  if ci.numParams > args.size then return none
  let mut isNested := false
  let mut looseBVars := false
  for i in [0:ci.numParams] do
    if args[i]!.hasLooseBVars then
      looseBVars := true
    let newTypes := (← get).newTypes
    if let some _ := args[i]!.find? fun
      | .const t _ => newTypes.any fun ty => t == ty.name
      | _ => false
    then
      isNested := true
  if !isNested then return none
  if looseBVars then
    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."
  return some ci

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except Exception Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

/-- If `e` is a nested occurrence `I Ds is`, return `Iaux As is` -/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args => do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IAs := mkAppRange fn 0 I_nparams args -- `I As`
  let Iparams ← replaceParams params IAs As
  let st ← get
  if let some auxI_name := st.nestedAux.findSome? fun (e, n) =>
    if e == Iparams then some n else none
  then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  let mut result := none
  let env ← read
  for J_name in I_val.all do
    let .inductInfo J_info ← env.get J_name | unreachable!
    let J := .const J_name I_lvls
    let JAs := mkAppRange J 0 I_nparams args
    let auxJ_name ← mkUniqueName (`_nested ++ J_name)
    let auxJ_type := J_info.type.instantiateLevelParams J_info.levelParams I_lvls
    let auxJ_type := lctx.mkForall As <| ← instantiateForallParams auxJ_type I_nparams args
    let JAs' ← replaceParams params JAs As
    modify fun st => { st with nestedAux := st.nestedAux.push (JAs', auxJ_name) }
    if J_name == I_name then
      result := some <|
        mkAppRange (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
    let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
      let J_ctor_info ← env.get J_ctor_name
      -- auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it.
      let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
      let auxJ_ctor_type := J_ctor_info.type.instantiateLevelParams J_ctor_info.levelParams I_lvls
      let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
      return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
    let newType := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors }
    modify fun st => { st with newTypes := st.newTypes.push newType }
  assert! result.isSome
  return result

def replaceAllNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M Expr := e.replaceM (replaceIfNested lctx params As)

def withParams (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr → M α) : M α := loop {} type #[] nparams where
  loop lctx type params
  | 0 => k lctx type params
  | i+1 => do
    let .forallE name dom body bi := type
      | throw <| .other "invalid inductive datatype declaration, incorrect number of parameters"
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    loop lctx (body.instantiate1 arg) (params.push arg) i

def run (fuel nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  withParams I.type nparams fun lctx _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    let s ← get
    if _h : i < s.newTypes.size then
      let indType := s.newTypes[i]
      let ctors ← indType.ctors.mapM fun ctor => do
        withParams ctor.type nparams fun lctx ctorType As => do
        assert! As.size == nparams
        return { ctor with type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }
      modify fun s => { s with newTypes := s.newTypes.set! i { indType with ctors } }
      loop (i+1) fuel
    else
      let aux2nested := s.nestedAux.foldl (fun m (e, n) => m.insert n e) {}
      return {
        ngen := s.ngen
        nparams := params.size
        lctx := lctx
        params := params
        aux2nested := aux2nested
        types := s.newTypes.toList }
  loop 0 fuel
end ElimNestedInductive

def mkAuxRecNameMap (env' : Environment) (types : List InductiveType) :
    List Name × NameMap Name := Id.run do
  let mainType :: _ := types | unreachable!
  let ntypes := types.length
  let mainName := mainType.name
  let some (.inductInfo mainInfo) := env'.find? mainName | unreachable!
  let allNames := mainInfo.all
  assert! allNames.length > ntypes
  let mut oldRecNames := #[]
  let mut recMap : NameMap Name := {}
  let mut nextIdx := 1
  for indName in allNames.drop ntypes do
    let oldRecName := mkRecName indName
    let newRecName := (mkRecName mainName).appendIndexAfter nextIdx
    nextIdx := nextIdx + 1
    recMap := recMap.insert oldRecName newRecName
    oldRecNames := oldRecNames.push oldRecName
  return (oldRecNames.toList, recMap)

def checkNoNestedAux (n : Name) (e : Expr) : Except Exception Unit := do
  if (e.find? fun
      | .const c _ => (`_nested).isPrefixOf c
      | .proj s _ _ => (`_nested).isPrefixOf s
      | _ => false).isSome then
    throw <| .other s!"invalid declaration '{n}', it uses the reserved prefix '_nested'"

/-- Checks the occurrence of a datatype being declared at the head of `e`, if there is one.
Returns `true` when the occurrence was checked and `e`'s subterms need not be revisited. -/
def checkUniformIndOcc (lvls : List Level) (indNames : List Name) (nparams : Nat)
    (e : Expr) (offset : Nat) : Except Exception Bool := do
  let .const c ls := e.getAppFn | return false
  unless indNames.contains c do return false
  let args := e.getAppArgs
  -- Over-applied: descend, so that occurrences in the indices are checked too. The parameter
  -- application itself is visited as a subterm of `e` and checked then.
  if args.size > nparams then return false
  let ok := args.size == nparams && offset ≥ nparams && ls == lvls
    && (List.range nparams).all fun i => args[i]! == .bvar (offset - 1 - i)
  unless ok do
    throw <| .other s!"invalid occurrence of datatype '{c}' being declared: it must be applied \
      to the parameters and universe levels of the mutual declaration"
  return true

/-- Checks that every occurrence of a datatype being declared in `e` is applied to the
declaration's universe levels and to its parameters, which at binder depth `offset` are the bound
variables `#(offset-1) … #(offset-nparams)`. That those binders really are the parameters is
established later, by the parameter check in `checkConstructors`. -/
def checkUniformIndOccsIn (lvls : List Level) (indNames : List Name) (nparams : Nat) :
    Expr → Nat → Except Exception Unit
  | e, offset => do
    if ← checkUniformIndOcc lvls indNames nparams e offset then return
    match e with
    | .forallE _ d b _ | .lam _ d b _ =>
      checkUniformIndOccsIn lvls indNames nparams d offset
      checkUniformIndOccsIn lvls indNames nparams b (offset + 1)
    | .letE _ t v b _ =>
      checkUniformIndOccsIn lvls indNames nparams t offset
      checkUniformIndOccsIn lvls indNames nparams v offset
      checkUniformIndOccsIn lvls indNames nparams b (offset + 1)
    | .app f a =>
      checkUniformIndOccsIn lvls indNames nparams f offset
      checkUniformIndOccsIn lvls indNames nparams a offset
    | .mdata _ b => checkUniformIndOccsIn lvls indNames nparams b offset
    | .proj _ _ b => checkUniformIndOccsIn lvls indNames nparams b offset
    | _ => pure ()

/-- Runs `checkUniformIndOccsIn` over every constructor type of the declaration.

Later phases inspect the constructor types modulo `whnf`, which can erase an occurrence (as in
`(fun _ => Unit) (T Nat)`), and the parametric arguments of a nested occurrence are dropped from
the auxiliary declaration altogether, so a non-uniform occurrence could escape checking there.
Reduction never creates an occurrence of a datatype being declared, since those are not yet in the
environment, so checking the syntactic occurrences here covers all of them. -/
def checkUniformIndOccs (lparams : List Name) (nparams : Nat) (types : List InductiveType) :
    Except Exception Unit := do
  let lvls := lparams.map Level.param
  let indNames := types.map (·.name)
  for indType in types do
    for ctor in indType.ctors do
      checkUniformIndOccsIn lvls indNames nparams ctor.type 0

def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  for indType in types do
    env.checkNoMVarNoFVar indType.name indType.type
    for ctor in indType.ctors do
      env.checkNoMVarNoFVar ctor.name ctor.type
      checkNoNestedAux ctor.name ctor.type
  checkUniformIndOccs lparams nparams types
  let res ← ElimNestedInductive.run fuel.inductiveFuel nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  let numNested := res.aux2nested.size
  let safety := if isUnsafe then .unsafe else .safe
  let env' ← AddInductive.run nparams res.types numNested
    { env, allowPrimitive, lparams, fuel, safety }
  if numNested = 0 then return env'
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap env' types
  (·.2) <$> StateT.run (s := env) do
  let processRec recName := do
    let newRecName := recNameMap'.getD recName recName
    let some (.recInfo recInfo) := env'.find? recName | unreachable!
    let newRecType := res.restoreNested env' recInfo.type recNameMap'
    let newRules ← recInfo.rules.mapM fun rule => do
      let newRhs := res.restoreNested env' rule.rhs recNameMap'
      let newCtorName := if newRecName == recName then rule.ctor else
        res.restoreCtorName env' rule.ctor
      return { rule with ctor := newCtorName, rhs := newRhs }
    (← MonadState.get).checkName newRecName allowPrimitive
    modify (·.add <| .recInfo { recInfo with
      name := newRecName, type := newRecType, all := allIndNames, rules := newRules })
  for indType in types do
    let some (.inductInfo ind) := env'.find? indType.name | unreachable!
    (← get).checkName ind.name allowPrimitive
    modify (·.add <| .inductInfo { ind with all := allIndNames })
    for ctorName in ind.ctors do
      let some (.ctorInfo ctor) := env'.find? ctorName | unreachable!
      let newType := res.restoreNested env' ctor.type
      (← get).checkName ctor.name allowPrimitive
      modify (·.add <| .ctorInfo { ctor with type := newType })
    processRec (mkRecName indType.name)
  recNames'.forM processRec
  TypeChecker.M.run (← get) (safety := safety) (lctx := res.lctx)
      (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun _ e => do _ ← TypeChecker.checkType e
