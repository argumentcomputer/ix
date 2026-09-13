/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Verify.Environment.Normalization

open Ix.Theory (VLevel)

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

namespace AddInductive
open TypeChecker

/-!
# Semantic interpretation of constructor validation

This module interprets the operational trace retained by
`Inductive.ValidationTrace`.  It deliberately sits above both the verified
checker and candidate normalization: validation supplies the accepted kernel
path, while normalization supplies the exact analyzer-owned Theory view.
-/

/-- Structural equality of kernel levels is sound after strict translation. -/
theorem levelStructEq_ofLevel
    (equal : levelStructEq lhs rhs = true)
    (lhs_tr : VLevel.ofLevel Us lhs = some lhs')
    (rhs_tr : VLevel.ofLevel Us rhs = some rhs') :
    lhs' = rhs' := by
  induction lhs generalizing rhs lhs' rhs' with
  | zero =>
      cases rhs <;> simp_all [levelStructEq, VLevel.ofLevel]
  | succ lhs ih =>
      cases rhs with
      | succ rhs =>
          simp only [levelStructEq] at equal
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at lhs_tr rhs_tr
          obtain ⟨lhs'', lhs_inner_tr, lhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp lhs_tr
          obtain ⟨rhs'', rhs_inner_tr, rhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp rhs_tr
          change some lhs''.succ = some lhs' at lhs'_eq
          change some rhs''.succ = some rhs' at rhs'_eq
          injection lhs'_eq with lhs'_eq
          injection rhs'_eq with rhs'_eq
          subst lhs'
          subst rhs'
          rw [ih equal lhs_inner_tr rhs_inner_tr]
      | zero | max _ _ | imax _ _ | param _ | mvar _ =>
          simp_all [levelStructEq]
  | max lhs₁ lhs₂ ih₁ ih₂ =>
      cases rhs with
      | max rhs₁ rhs₂ =>
          simp only [levelStructEq, Bool.and_eq_true] at equal
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at lhs_tr rhs_tr
          obtain ⟨lhs₁', lhs₁_tr, lhsTail⟩ :=
            Option.bind_eq_some_iff.mp lhs_tr
          obtain ⟨lhs₂', lhs₂_tr, lhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp lhsTail
          obtain ⟨rhs₁', rhs₁_tr, rhsTail⟩ :=
            Option.bind_eq_some_iff.mp rhs_tr
          obtain ⟨rhs₂', rhs₂_tr, rhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp rhsTail
          change some (.max lhs₁' lhs₂') = some lhs' at lhs'_eq
          change some (.max rhs₁' rhs₂') = some rhs' at rhs'_eq
          injection lhs'_eq with lhs'_eq
          injection rhs'_eq with rhs'_eq
          subst lhs'
          subst rhs'
          rw [ih₁ equal.1 lhs₁_tr rhs₁_tr,
            ih₂ equal.2 lhs₂_tr rhs₂_tr]
      | zero | succ _ | imax _ _ | param _ | mvar _ =>
          simp_all [levelStructEq]
  | imax lhs₁ lhs₂ ih₁ ih₂ =>
      cases rhs with
      | imax rhs₁ rhs₂ =>
          simp only [levelStructEq, Bool.and_eq_true] at equal
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at lhs_tr rhs_tr
          obtain ⟨lhs₁', lhs₁_tr, lhsTail⟩ :=
            Option.bind_eq_some_iff.mp lhs_tr
          obtain ⟨lhs₂', lhs₂_tr, lhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp lhsTail
          obtain ⟨rhs₁', rhs₁_tr, rhsTail⟩ :=
            Option.bind_eq_some_iff.mp rhs_tr
          obtain ⟨rhs₂', rhs₂_tr, rhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp rhsTail
          change some (.imax lhs₁' lhs₂') = some lhs' at lhs'_eq
          change some (.imax rhs₁' rhs₂') = some rhs' at rhs'_eq
          injection lhs'_eq with lhs'_eq
          injection rhs'_eq with rhs'_eq
          subst lhs'
          subst rhs'
          rw [ih₁ equal.1 lhs₁_tr rhs₁_tr,
            ih₂ equal.2 lhs₂_tr rhs₂_tr]
      | zero | succ _ | max _ _ | param _ | mvar _ =>
          simp_all [levelStructEq]
  | param lhsName =>
      cases rhs <;> simp_all [levelStructEq, VLevel.ofLevel]
  | mvar lhsId =>
      simp [VLevel.ofLevel] at lhs_tr

/-- The transparent fast path used by constructor validation implies the
Theory universe inequality required by `fieldsWF`. -/
theorem levelStructGe_ofLevel
    (greater : levelStructGe result field = true)
    (result_tr : VLevel.ofLevel Us result = some result')
    (field_tr : VLevel.ofLevel Us field = some field') :
    field' ≤ result' := by
  induction result generalizing field result' field' with
  | zero =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some result' at result_tr
          change some (.zero : VLevel) = some field' at field_tr
          injection result_tr with result_tr
          injection field_tr with field_tr
          subst result'
          subst field'
          exact VLevel.le_refl _
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          simp_all [levelStructGe, levelStructEq]
  | succ result ih =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ field =>
          simp only [levelStructGe] at greater
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at result_tr field_tr
          obtain ⟨result'', result_inner_tr, result'_eq⟩ :=
            Option.bind_eq_some_iff.mp result_tr
          obtain ⟨field'', field_inner_tr, field'_eq⟩ :=
            Option.bind_eq_some_iff.mp field_tr
          change some result''.succ = some result' at result'_eq
          change some field''.succ = some field' at field'_eq
          injection result'_eq with result'_eq
          injection field'_eq with field'_eq
          subst result'
          subst field'
          exact VLevel.succ_le_succ
            (ih greater result_inner_tr field_inner_tr)
      | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | max result₁ result₂ ih₁ ih₂ =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | imax result₁ result₂ ih₁ ih₂ =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | param resultName =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | mvar resultId =>
      simp [VLevel.ofLevel] at result_tr

/-- The impredicative fallback is exact: a kernel level recognized as zero
translates to Theory's zero level. -/
theorem ofLevel_eq_zero_of_isZero
    (zero : level.isZero = true)
    (level_tr : VLevel.ofLevel Us level = some level') :
    level' = .zero := by
  cases level <;> simp_all [Level.isZero, VLevel.ofLevel]

/-- Executable universe comparison supported by the semantic proof.

The structural and impredicative `Prop` branches mirror the ordinary
validator directly.  A normalized non-`Prop` comparison is admitted only
when Lean's ordinary `Level.geq` decision and the verified project `geq'`
decision both succeed.  The former preserves the kernel-facing acceptance
boundary; the latter supplies the semantic inequality without trusting
Lean's opaque normalizer. -/
def constructorUniverseSemanticGe (resultLevel fieldLevel : Level) : Bool :=
  levelStructGe resultLevel fieldLevel ||
    (resultLevel.isZero ||
      (resultLevel.geq fieldLevel && resultLevel.geq' fieldLevel))

/-- Replay just the universe-bearing part of one constructor telescope.

The traversal deliberately follows the validator's parameter substitution,
ordinary-field local contexts, annotation consumption, and recursion fuel.
Unlike `checkConstructorType`, its normalized fallback also requires the
proved project comparison above.  Running this audit in addition to the
ordinary validator is therefore an executable verified intersection, not a
replacement validator and not a proof-only semantic premise. -/
def checkConstructorUniverseSemantics (stats : InductiveStats) (t : Expr) :
    M Unit := do
  loop t 0 (← readThe Context).fuel.inductiveFuel
where
  loop (t : Expr) (i : Nat) : Nat → M Unit
    | 0 => throw .deepRecursion
    | fuel + 1 => do
      if let .forallE name domain body binderInfo := t then
        if let some parameter := stats.params[i]? then
          loop (body.instantiate1 parameter) (i + 1) fuel
        else
          let sortResult ← ensureType domain
          unless constructorUniverseSemanticGe stats.resultLevel
              sortResult.sortLevel! do
            throw <| .other
              "constructor universe lies outside the verified semantic subset"
          withLocalDecl name binderInfo (consumeTypeAnnotations domain) fun arg =>
            loop (body.instantiate1 arg) (i + 1) fuel

/-- Source-ordered universe audit for every constructor in one singleton
family.  Constructor names and types come from the same indexed source list
as `ConstructorListValidationTrace`; all non-universe validation remains in
that retained ordinary trace. -/
def checkConstructorUniverseListSemantics (stats : InductiveStats) :
    List Constructor → M Unit
  | [] => pure ()
  | constructor :: constructors => do
      checkConstructorUniverseSemantics stats constructor.type
      checkConstructorUniverseListSemantics stats constructors

/-- The executable semantic decision at the exact universe node retained by
ordinary constructor validation. -/
def ConstructorUniverseTrace.semantic
    (_trace : ConstructorUniverseTrace resultLevel fieldLevel) : Bool :=
  constructorUniverseSemanticGe resultLevel fieldLevel

/-- Conjunction of the semantic universe decisions in one exact constructor
telescope. Parameter and terminal nodes contribute no universe obligation. -/
def ConstructorTypeValidationTrace.universeSemantics
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) : Bool :=
  match trace with
  | .parameter _ _ _ _ _ _ _ _ _ _ _ _ tail =>
      tail.universeSemantics
  | .ordinary _ _ _ _ _ _ _ _ _ _ universeTrace _ tail =>
      universeTrace.semantic && tail.universeSemantics
  | .terminal _ _ _ _ _ _ => true

/-- Source-ordered conjunction of every constructor telescope's semantic
universe decisions. -/
def ConstructorListValidationTrace.universeSemantics
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) : Bool :=
  match trace with
  | .nil _ => true
  | .cons _ _ _ _ _ _ typeTrace tailTrace =>
      typeTrace.universeSemantics && tailTrace.universeSemantics

/-- The complete semantic-universe gate attached to one retained ordinary
constructor-validation run. -/
def ConstructorValidationRun.universeSemantics
    (validation : ConstructorValidationRun indType stats isUnsafe context) :
    Bool :=
  validation.trace.universeSemantics

/-- Recover the state-bearing verified-checker execution erased by the
ordinary constructor validator's `ensureType` observation. -/
theorem ConstructorEnsureTypeStep.innerRun
    (step : ConstructorEnsureTypeStep) (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.ensureType step.source step.context.toTypeChecker
          ({} : TypeChecker.State) = .ok (step.result, state) := by
  unfold ConstructorEnsureTypeStep.Valid TypeChecker.M.run at hvalid
  cases hrun : TypeChecker.ensureType step.source
      { env := step.context.env
        lctx := step.context.lctx
        safety := step.context.safety
        lparams := step.context.lparams
        fuel := step.context.fuel }
      ({} : TypeChecker.State) with
  | error err =>
      simp [StateT.run', Functor.map, Except.map, hrun] at hvalid
  | ok pair =>
      rcases pair with ⟨result, state⟩
      have result_eq : result = step.result := by
        simpa [StateT.run', Functor.map, Except.map, hrun] using hvalid
      subst result
      exact ⟨state, by simpa [Context.toTypeChecker] using hrun⟩

/-- Theory interpretation of the exact `ensureType` execution retained for
an ordinary constructor field. -/
structure TypeChecker.EnsureTypeRun (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (source result : Expr) (source' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  source_tr : TrExprS env Us Δ source source'
  resultLevel : Level
  resultLevel' : VLevel
  result_eq : result = .sort resultLevel
  resultLevel_tr : VLevel.ofLevel Us resultLevel = some resultLevel'
  source_type : env.HasType Us.length Δ.toCtx source' (.sort resultLevel')
  run_eq : ∃ state : State,
    ensureType source context.toContext ({} : State) = .ok (result, state)

/-- Attach verified Theory meaning to one retained ordinary-field
`ensureType` step in its exact post-family context. -/
theorem TypeChecker.EnsureTypeRun.exists_ofConstructorStep
    (step : ConstructorEnsureTypeStep) (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS step.source source') :
    Nonempty (EnsureTypeRun contextRun.context.venv
      contextRun.context.lparams contextRun.context.vlctx
      step.source step.result source') := by
  obtain ⟨state, run⟩ := step.innerRun hvalid
  rw [← contextRun.context_eq] at run
  obtain ⟨_, _, _, _, translated, translated_tr, u, u', result_eq,
      level_tr, source_type⟩ :=
    (ensureType.WF source_tr) contextRun.state_wf step.result state run
  have translated_def := translated_tr.uniq contextRun.context.Ewf
    (.refl contextRun.context.Ewf contextRun.context.Δwf) source_tr
  have source_type' := source_type.defeqU_l contextRun.context.Ewf
    contextRun.context.Δwf translated_def
  exact ⟨{
    context := contextRun.context
    venv_eq := rfl
    lparams_eq := rfl
    vlctx_eq := rfl
    state_wf := contextRun.state_wf
    source_tr := source_tr
    resultLevel := u
    resultLevel' := u'
    result_eq := result_eq
    resultLevel_tr := level_tr
    source_type := source_type'
    run_eq := ⟨state, run⟩ }⟩

/-!
## Exact post-family view alignment

Constructor validation and constructor-candidate construction deliberately
allocate their ordinary-field free variables from different reader states.
The following audit therefore never compares those identifiers.  It follows
the already-retained validation trace and instantiates the exact candidate
view with the *validation* parameter/field expression at each position.
Every comparison consequently happens in the real post-family local context,
while the candidate itself still owns the view being inspected.
-/

/-- Number of parameter/ordinary binders consumed by one exact constructor
validation trace. -/
def ConstructorTypeValidationTrace.spineLength
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) : Nat :=
  match trace with
  | .parameter _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.spineLength + 1
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.spineLength + 1
  | .terminal .. => 0

/-- Every local declaration entered by a retained positivity traversal uses
an identifier absent from the exact incoming local context.  This is an
executable structural condition, not a semantic premise. -/
def ConstructorPositivityTrace.freshNames
    (trace : ConstructorPositivityTrace stats ctor argIdx context source fuel) :
    Bool :=
  match trace with
  | .absent .. => true
  | .forallE context _ _ _ _ _ _ _ _ _ tail =>
      (context.lctx.find? context.freshFVarId).isNone && tail.freshNames
  | .target .. => true

def ConstructorPositivityModeTrace.freshNames
    (trace : ConstructorPositivityModeTrace stats isUnsafe ctor argIdx
      context source) : Bool :=
  match trace with
  | .skipped .. => true
  | .safe _ trace => trace.freshNames

/-- One exact full-check observation together with the syntactic premise used
by the verified checker refinement.  Keeping the premise at the operational
boundary avoids reconstructing free-variable membership later from binder
names or from a parallel telescope. -/
structure ConstructorCheckedExpr (context : Context) (source : Expr) where
  fvars : source.FVarsIn
    (fun fv => (context.lctx.find? fv).isSome = true)
  observation : CandidateCheckTypeObservation context source

/-- Retain an already verified full-check execution together with a structural
scope proof for its exact source expression. -/
def ConstructorCheckedExpr.ofRun
    (fvars : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true))
    (run : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩) :
    ConstructorCheckedExpr context source :=
  ⟨fvars, ⟨inferred, run⟩⟩

private theorem constructorClosed_hasMVar_false
    {env : Kernel.Environment} {name : Name} {source : Expr}
    (closed : env.checkNoMVarNoFVar name source = .ok ()) :
    source.hasMVar = false := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar at closed
  cases hmvars : source.hasMVar
  · rfl
  · simp [hmvars, Bind.bind, Except.bind] at closed

private theorem constructorClosed_hasFVar_false
    {env : Kernel.Environment} {name : Name} {source : Expr}
    (closed : env.checkNoMVarNoFVar name source = .ok ()) :
    source.hasFVar = false := by
  have hmvars := constructorClosed_hasMVar_false closed
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar at closed
  cases hfvars : source.hasFVar
  · rfl
  · simp [hmvars, hfvars, Bind.bind, Except.bind, Pure.pure,
      Except.pure] at closed

/-- Constructor metadata accepted by the validator is closed, so its retained
empty-context full-check observation directly supplies the D2 root scope. -/
def ConstructorCheckedExpr.ofClosedRoot
    {context : Context} {name : Name} {source : Expr}
    (closed : context.env.checkNoMVarNoFVar name source = .ok ())
    (observation : CandidateCheckTypeObservation
      context.withEmptyLocalContext source) :
    ConstructorCheckedExpr context.withEmptyLocalContext source where
  fvars := fvarsIn_iff.2 ⟨by
    intro fv present
    have empty := fvarsList_eq_nil.mpr
      (constructorClosed_hasFVar_false closed)
    rw [empty] at present
    contradiction,
    fvarsIn_iff_hasMVar.2 (constructorClosed_hasMVar_false closed)⟩
  observation := observation

/-- Execute a full check only after confirming that every free variable of
the exact source belongs to the retained implementation context. -/
def checkConstructorAlignedExpr (context : Context) (source : Expr) :
    Except Exception (ConstructorCheckedExpr context source) := do
  if hfvars : source.fvarsList.all
      (fun fv => (context.lctx.find? fv).isSome) = true then
    if hmvars : source.hasMVar = false then
      have fvars : source.FVarsIn
          (fun fv => (context.lctx.find? fv).isSome = true) :=
        fvarsIn_iff.2 ⟨by
          intro fv hfv
          have h := List.all_eq_true.mp hfvars fv hfv
          exact h,
        fvarsIn_iff_hasMVar.2 hmvars⟩
      let observation ← observeCandidateCheckType context source
      pure ⟨fvars, observation⟩
    else
      throw <| .other "constructor alignment source contains a metavariable"
  else
    throw <| .other "constructor alignment source escaped its local context"

/-- Reuse an exact full-check execution to expose the successful result of
the supplemental scope-aware checker boundary. -/
theorem checkConstructorAlignedExpr.exists_of_run
    (hfvars : source.fvarsList.all
      (fun fv => (context.lctx.find? fv).isSome) = true)
    (hmvars : source.hasMVar = false)
    (hrun : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩) :
    ∃ checked : ConstructorCheckedExpr context source,
      checkConstructorAlignedExpr context source = .ok checked := by
  unfold checkConstructorAlignedExpr
  rw [dif_pos hfvars, dif_pos hmvars]
  rw [observeCandidateCheckType_of_run context source inferred hrun]
  exact ⟨_, rfl⟩

/-- Re-executing the supplemental scope/full-check boundary reproduces any
retained successful observation.  The only reconstructed fields are proofs,
so proof irrelevance identifies the executable result with the retained
value itself. -/
theorem ConstructorCheckedExpr.check_eq
    (checked : ConstructorCheckedExpr context source) :
    checkConstructorAlignedExpr context source = .ok checked := by
  have hfvars : source.fvarsList.all
      (fun fv => (context.lctx.find? fv).isSome) = true := by
    apply List.all_eq_true.mpr
    intro fv present
    exact (fvarsIn_iff.mp checked.fvars).1 fv present
  have hmvars : source.hasMVar = false :=
    fvarsIn_iff_hasMVar.mp (fvarsIn_iff.mp checked.fvars).2
  unfold checkConstructorAlignedExpr
  rw [dif_pos hfvars, dif_pos hmvars]
  rw [observeCandidateCheckType_of_run context source
    checked.observation.inferred checked.observation.valid]
  cases checked
  rfl

/-- Determinism of the erased implementation run pins a retained full-check
observation to any independently proved result of that same exact check. -/
theorem ConstructorCheckedExpr.inferred_eq_of_run
    (checked : ConstructorCheckedExpr context source)
    (hrun : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩) :
    checked.observation.inferred = inferred := by
  have retained := checked.observation.valid
  unfold CandidateCheckTypeStep.Valid at retained hrun
  rw [hrun] at retained
  exact (Except.ok.inj retained).symm

/-- Re-executing a retained equality observation returns that same
observation; its sole field is proof-valued. -/
theorem CandidateIsDefEqObservation.observe_eq
    (observation : CandidateIsDefEqObservation context lhs rhs) :
    observeCandidateIsDefEq context lhs rhs = .ok observation := by
  rw [observeCandidateIsDefEq_of_run context lhs rhs observation.valid]

/-- The verified implementation equality checker accepts a syntactically
identical pair without inspecting or extending its success cache. -/
theorem candidateIsDefEqRefl
    (context : Context) (source : Expr) :
    CandidateIsDefEqStep.Valid ⟨context, source, source⟩ := by
  unfold CandidateIsDefEqStep.Valid TypeChecker.M.run TypeChecker.isDefEq
    TypeChecker.RecM.run TypeChecker.Inner.isDefEq
  simp [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
    StateT.bind, Except.bind, StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rfl

/-- Convert the executable implementation-context scope check to the exact
Theory free-variable premise used by verified `checkType` refinement. -/
theorem ConstructorCheckedExpr.fvarsIn
    (checked : ConstructorCheckedExpr context source)
    (contextRun : TypeChecker.CandidateContextRun context) :
    source.FVarsIn (· ∈ contextRun.context.vlctx.fvars) := by
  apply checked.fvars.mono
  intro fv present
  have implementationPresent :
      ∃ declaration, context.lctx.find? fv = some declaration := by
    simpa only [Option.isSome_iff_exists] using present
  have verifiedPresent :
      ∃ declaration, contextRun.context.lctx.find? fv = some declaration := by
    simpa only [contextRun.context_lctx] using implementationPresent
  apply contextRun.context.trlctx.find?_eq_some.mp
  change ∃ declaration,
    contextRun.context.mlctx.lctx.find? fv = some declaration
  rw [contextRun.context.lctx_eq]
  exact verifiedPresent

/-- Verified meaning of one full check retained by the alignment audit.  Both
Theory endpoints are selected by the checker refinement; callers cannot
substitute an unrelated translation for the exact source position. -/
structure ConstructorCheckedExpr.Run
    (checked : ConstructorCheckedExpr context source)
    (contextRun : TypeChecker.CandidateContextRun context) where
  source' : VExpr
  inferred' : VExpr
  check : TypeChecker.CheckTypeRun contextRun.context.venv
    contextRun.context.lparams contextRun.context.vlctx source
    checked.observation.inferred source' inferred'

/-- Interpret an aligned full-check observation in its exact verified
post-family context. -/
theorem ConstructorCheckedExpr.Run.exists
    (checked : ConstructorCheckedExpr context source)
    (contextRun : TypeChecker.CandidateContextRun context) :
    Nonempty (ConstructorCheckedExpr.Run checked contextRun) := by
  obtain ⟨source', inferred', ⟨check⟩⟩ :=
    TypeChecker.CheckTypeRun.exists_ofCandidateStepFVars
      ⟨context, source, checked.observation.inferred⟩
      checked.observation.valid contextRun (checked.fvarsIn contextRun)
  exact ⟨⟨source', inferred', check⟩⟩

/-- A retained full check whose implementation result is syntactically a
sort supplies the exact Theory `IsType` premise needed to extend the local
context. -/
theorem ConstructorCheckedExpr.Run.isType_of_inferredSort
    (run : ConstructorCheckedExpr.Run checked contextRun)
    (inferred_eq : checked.observation.inferred = .sort u) :
    contextRun.context.IsType run.source' := by
  rcases run with ⟨source', inferred', check⟩
  have inferred_tr := check.inferred_tr
  rw [inferred_eq] at inferred_tr
  cases inferred_tr
  exact check.isType

/-- Reuse a proved scope boundary with the exact full-check observation owned
by another retained execution of the same source expression. -/
def ConstructorCheckedExpr.withObservation
    (scope : ConstructorCheckedExpr context source)
    (observation : CandidateCheckTypeObservation context source) :
    ConstructorCheckedExpr context source :=
  ⟨scope.fvars, observation⟩

/-- Interpret one retained equality observation at the exact Theory
translations selected by the two aligned full checks. -/
def ConstructorCheckedExpr.Run.isDefEq
    {context : Context} {lhs rhs : Expr}
    {lhsCheck : ConstructorCheckedExpr context lhs}
    {rhsCheck : ConstructorCheckedExpr context rhs}
    {contextRun : TypeChecker.CandidateContextRun context}
    (lhsRun : ConstructorCheckedExpr.Run lhsCheck contextRun)
    (rhsRun : ConstructorCheckedExpr.Run rhsCheck contextRun)
    (observation : CandidateIsDefEqObservation context lhs rhs) :
    TypeChecker.IsDefEqRun contextRun.context.venv
      contextRun.context.lparams contextRun.context.vlctx lhs rhs
      lhsRun.source' rhsRun.source' :=
  TypeChecker.IsDefEqRun.ofCandidateStep
    ⟨context, lhs, rhs⟩ observation.valid contextRun.context
    contextRun.context_eq rfl rfl rfl contextRun.state_wf
    lhsRun.check.expr_tr rhsRun.check.expr_tr context.fuel.recDepth rfl

/-- A validation-local verified context pinned to the one post-family Theory
environment and universe-parameter list used by the whole constructor list. -/
structure ConstructorContextRun (env : VEnv) (Us : List Name)
    (context : Context) where
  candidate : TypeChecker.CandidateContextRun context
  venv_eq : candidate.context.venv = env
  lparams_eq : candidate.context.lparams = Us

def ConstructorContextRun.withEmptyLocalContext
    (run : ConstructorContextRun env Us context) :
    ConstructorContextRun env Us context.withEmptyLocalContext where
  candidate := run.candidate.withEmptyLocalContext
  venv_eq := run.venv_eq
  lparams_eq := run.lparams_eq

/-- Extend the actual post-family verified context by exactly one retained
validation local declaration. -/
def ConstructorContextRun.pushLocalDecl
    (run : ConstructorContextRun env Us context)
    (name : Name) (binderInfo : BinderInfo) (domain : Expr)
    (fresh : context.lctx.find? context.freshFVarId = none)
    (domain' : VExpr)
    (domain_tr : run.candidate.context.TrExprS domain domain')
    (domain_type : run.candidate.context.IsType domain') :
    ConstructorContextRun env Us
      (context.pushLocalDecl name binderInfo domain) := by
  let candidate := run.candidate.pushLocalDecl name binderInfo domain fresh
    domain' domain_tr domain_type
  refine ⟨candidate, ?_, ?_⟩
  · calc
      candidate.context.venv = run.candidate.context.venv := by
        simp [candidate]
      _ = env := run.venv_eq
  · calc
      candidate.context.lparams = run.candidate.context.lparams := by
        simp [candidate, AddInductive.Context.pushLocalDecl]
      _ = Us := run.lparams_eq

/-- Verified interpretation of one exact retained WHNF operation, sharing the
source translation already selected by its aligned full check. -/
structure ConstructorWhnfRun
    {context : Context} {source : Expr}
    {sourceCheck : ConstructorCheckedExpr context source}
    (contextRun : TypeChecker.CandidateContextRun context)
    (sourceRun : ConstructorCheckedExpr.Run sourceCheck contextRun)
    (result : Expr) where
  result' : VExpr
  result_tr : contextRun.context.TrExprS result result'
  whnf : TypeChecker.WhnfRun contextRun.context.venv
    contextRun.context.lparams contextRun.context.vlctx source result
    sourceRun.source' result'

theorem ConstructorWhnfRun.exists
    {context : Context} {source result : Expr}
    {sourceCheck : ConstructorCheckedExpr context source}
    (contextRun : TypeChecker.CandidateContextRun context)
    (sourceRun : ConstructorCheckedExpr.Run sourceCheck contextRun)
    (valid : CandidateWhnfStep.Valid ⟨context, source, result⟩)
    (recursionFuel : Nat)
    (depth : context.fuel.recDepth = recursionFuel + 1) :
    Nonempty (ConstructorWhnfRun contextRun sourceRun result) := by
  obtain ⟨result', result_tr, ⟨whnf⟩⟩ :=
    TypeChecker.WhnfRun.exists_ofCandidateStep
      ⟨context, source, result⟩ valid contextRun sourceRun.source'
      sourceRun.check.expr_tr recursionFuel depth
  exact ⟨⟨result', result_tr, whnf⟩⟩

/-- Retained operational evidence for the supplemental nested-positivity
alignment.  The ordinary positivity trace continues to own every WHNF,
occurrence decision, and accepted recursive target.  This trace adds the full
checks and annotation equality needed to interpret those exact operations in
the verified checker. -/
inductive ConstructorPositivityAlignmentTrace :
    {stats : InductiveStats} → {ctor : Name} → {argIdx : Nat} →
    {context : Context} → {source : Expr} → {fuel : Nat} →
    ConstructorPositivityTrace stats ctor argIdx context source fuel → Type where
  | absent
      (sourceCheck : ConstructorCheckedExpr context source) :
      ConstructorPositivityAlignmentTrace
        (.absent context source result fuel whnfStep occurs)
  | forallE
      (sourceCheck : ConstructorCheckedExpr context source)
      (domainCheck : ConstructorCheckedExpr context domain)
      (consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain))
      (consumedLevel : Level)
      (consumedInferred : consumedCheck.observation.inferred =
        .sort consumedLevel)
      (fresh : context.lctx.find? context.freshFVarId = none)
      (annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain))
      (tailTrace : ConstructorPositivityTrace stats ctor argIdx
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel)
      (tail : ConstructorPositivityAlignmentTrace tailTrace) :
      ConstructorPositivityAlignmentTrace
        (.forallE context source fuel name domain body binderInfo whnfStep occurs
          domainFree tailTrace)
  | target
      (sourceCheck : ConstructorCheckedExpr context source) :
      ConstructorPositivityAlignmentTrace
        (.target context source result fuel targetIdx whnfStep occurs terminal
          valid)

namespace ConstructorPositivityAlignmentTrace

def build :
    (positivityTrace : ConstructorPositivityTrace stats ctor argIdx context
      source fuel) →
      Except Exception (ConstructorPositivityAlignmentTrace positivityTrace)
  | .absent context source _ fuel whnfStep occurs => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      pure <| .absent sourceCheck
  | .forallE context source fuel _ domain _ _ _ occurs
      domainFree tailTrace => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      let domainCheck ← checkConstructorAlignedExpr context domain
      let consumedCheck ← checkConstructorAlignedExpr context
        (consumeTypeAnnotations domain)
      match consumedInferred : consumedCheck.observation.inferred with
      | .sort consumedLevel =>
        if fresh : context.lctx.find? context.freshFVarId = none then
          let annotations ← observeCandidateIsDefEq context domain
            (consumeTypeAnnotations domain)
          let tail ← build tailTrace
          pure <| .forallE sourceCheck domainCheck consumedCheck consumedLevel
            consumedInferred fresh annotations tailTrace tail
        else
          throw <| .other "positivity traversal reused a local identifier"
      | _ =>
        throw <| .other
          "consumed positivity domain did not check as a type"
  | .target context source _ fuel _ _ occurs terminal
      valid => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      pure <| .target sourceCheck

/-- Executable erasure of the retained positivity alignment. -/
def check (positivityTrace : ConstructorPositivityTrace stats ctor argIdx
    context source fuel) : M Unit := fun _ =>
  (ConstructorPositivityAlignmentTrace.build positivityTrace).map fun _ => ()

theorem nonempty_of_check
    {positivityTrace : ConstructorPositivityTrace stats ctor argIdx context
      source fuel}
    (success : ConstructorPositivityAlignmentTrace.check positivityTrace
      context = .ok ()) :
    Nonempty (ConstructorPositivityAlignmentTrace positivityTrace) := by
  unfold check at success
  cases h : ConstructorPositivityAlignmentTrace.build positivityTrace with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

end ConstructorPositivityAlignmentTrace

inductive ConstructorPositivityModeAlignmentTrace :
    {stats : InductiveStats} → {isUnsafe : Bool} → {ctor : Name} →
    {argIdx : Nat} → {context : Context} → {source : Expr} →
    ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source →
      Type where
  | skipped : ConstructorPositivityModeAlignmentTrace (.skipped unsafeEq)
  | safe (alignment : ConstructorPositivityAlignmentTrace positivityTrace) :
      ConstructorPositivityModeAlignmentTrace (.safe unsafeEq positivityTrace)

namespace ConstructorPositivityModeAlignmentTrace

def build :
    (positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
      argIdx context source) →
      Except Exception
        (ConstructorPositivityModeAlignmentTrace positivityTrace)
  | .skipped _ => pure <| .skipped
  | .safe _ positivityTrace => do
      let alignment ← ConstructorPositivityAlignmentTrace.build
        positivityTrace
      pure <| .safe alignment

def check (positivityTrace : ConstructorPositivityModeTrace stats isUnsafe
    ctor argIdx context source) : M Unit := fun _ =>
  (ConstructorPositivityModeAlignmentTrace.build positivityTrace).map fun _ => ()

theorem nonempty_of_check
    {positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
      argIdx context source}
    (success : ConstructorPositivityModeAlignmentTrace.check positivityTrace
      context = .ok ()) :
    Nonempty (ConstructorPositivityModeAlignmentTrace positivityTrace) := by
  unfold check at success
  cases h : ConstructorPositivityModeAlignmentTrace.build positivityTrace with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

end ConstructorPositivityModeAlignmentTrace

/-- Exact operational alignment between one retained validation telescope and
the analyzer-owned kernel view.  The recursive indices instantiate the view
with validation-owned parameters and fields, so no equality between the
producer's and validator's fresh free-variable identifiers is assumed. -/
inductive ConstructorViewAlignmentTrace :
    {stats : InductiveStats} → {isUnsafe : Bool} → {familyIdx : Nat} →
    {ctor : Name} → {context : Context} → {source : Expr} →
    {argIdx fuel : Nat} →
    ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor context
      source argIdx fuel →
    (view : Expr) → Type where
  | parameter
      (domainCheck : ConstructorCheckedExpr context domain)
      (viewDomainCheck : ConstructorCheckedExpr context viewDomain)
      (parameterTypeCheck : ConstructorCheckedExpr context parameterType)
      (parameterShape : param = .fvar fv)
      (parameterPresent : (context.lctx.find? fv).isSome = true)
      (tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (body.instantiate1 param) (argIdx + 1) fuel)
      (tail : ConstructorViewAlignmentTrace tailTrace
        (viewBody.instantiate1 param)) :
      ConstructorViewAlignmentTrace
        (.parameter context fuel argIdx name domain body binderInfo param
          parameterType parameterAt parameterTypeRun validationDefEq tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | ordinary
      (domainCheck : ConstructorCheckedExpr context domain)
      (viewDomainCheck : ConstructorCheckedExpr context viewDomain)
      (viewEquality : CandidateIsDefEqObservation context domain viewDomain)
      (consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain))
      (positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
        argIdx context domain)
      (positivityAlignment :
        ConstructorPositivityModeAlignmentTrace positivityTrace)
      (fresh : context.lctx.find? context.freshFVarId = none)
      (annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain))
      (tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) fuel)
      (tail : ConstructorViewAlignmentTrace tailTrace
        (viewBody.instantiate1 context.freshExpr)) :
      ConstructorViewAlignmentTrace
        (.ordinary context fuel argIdx name domain body binderInfo sortResult
          noParameter ensureTypeStep universeTrace positivityTrace tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | terminal
      (sourceCheck : ConstructorCheckedExpr context source)
      (viewCheck : ConstructorCheckedExpr context view)
      (viewTerminal : view.isForall = false)
      (viewValid : isValidIndAppIdx stats view familyIdx = true) :
      ConstructorViewAlignmentTrace
        (.terminal context source fuel argIdx sourceTerminal sourceValid) view

namespace ConstructorViewAlignmentTrace

/-- Execute the exact component audit and retain every successful checker
observation.  This is intentionally not a second `checkConstructors` run: the
raw branch shape, parameter selection, universe decision, positivity target,
and raw terminal acceptance remain owned by the ordinary validation trace. -/
def build :
    (validationTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
      ctor context source argIdx fuel) →
    (view : Expr) →
      Except Exception (ConstructorViewAlignmentTrace validationTrace view)
  | .parameter context parameterFuel parameterArgIdx parameterName domain
      parameterBody parameterBinderInfo param parameterType _
      _ _ tailTrace,
      .forallE viewName viewDomain viewBody viewBinderInfo => do
      let domainCheck ← checkConstructorAlignedExpr context domain
      let viewDomainCheck ← checkConstructorAlignedExpr context viewDomain
      let parameterTypeCheck ← checkConstructorAlignedExpr context
        parameterType
      match hparam : param with
      | .fvar fv =>
        if parameterPresent : (context.lctx.find? fv).isSome = true then
          let tail ← build tailTrace
            (viewBody.instantiate1 param)
          pure <| .parameter domainCheck viewDomainCheck parameterTypeCheck
            hparam parameterPresent tailTrace tail
        else
          throw <| .other
            "constructor parameter is absent from validation context"
      | _ =>
        throw <| .other "constructor parameter is not a local variable"
  | .parameter .., _ =>
      throw <| .other "candidate and validation constructor telescopes differ"
  | .ordinary context ordinaryFuel ordinaryArgIdx name domain body binderInfo
      _ _ _ _ positivityTrace tailTrace,
      .forallE viewName viewDomain viewBody viewBinderInfo => do
      let domainCheck ← checkConstructorAlignedExpr context domain
      let viewDomainCheck ← checkConstructorAlignedExpr context viewDomain
      let viewEquality ← observeCandidateIsDefEq context domain viewDomain
      let consumedCheck ← checkConstructorAlignedExpr context
        (consumeTypeAnnotations domain)
      let positivityAlignment ←
        ConstructorPositivityModeAlignmentTrace.build positivityTrace
      if fresh : context.lctx.find? context.freshFVarId = none then
        let annotations ← observeCandidateIsDefEq context domain
          (consumeTypeAnnotations domain)
        let tail ← build tailTrace
          (viewBody.instantiate1 context.freshExpr)
        pure <| .ordinary domainCheck viewDomainCheck viewEquality consumedCheck
          positivityTrace positivityAlignment fresh annotations tailTrace tail
      else
        throw <| .other "constructor validation reused a local identifier"
  | .ordinary .., _ =>
      throw <| .other "candidate and validation constructor telescopes differ"
  | .terminal context source fuel argIdx sourceTerminal sourceValid, view => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      let viewCheck ← checkConstructorAlignedExpr context view
      if viewTerminal : view.isForall = false then
        if viewValid : isValidIndAppIdx stats view familyIdx = true then
          pure <| .terminal sourceCheck viewCheck viewTerminal viewValid
        else
          throw <| .other
            "candidate view changed the terminal family application"
      else
        throw <| .other "candidate view has an extra constructor field"

def check (validationTrace : ConstructorTypeValidationTrace stats isUnsafe
    familyIdx ctor context source argIdx fuel) (view : Expr) : M Unit :=
  fun _ => (build validationTrace view).map fun _ => ()

theorem nonempty_of_check
    {validationTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
      ctor context source argIdx fuel}
    (success : check validationTrace view context = .ok ()) :
    Nonempty (ConstructorViewAlignmentTrace validationTrace view) := by
  unfold check at success
  cases h : build validationTrace view with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

end ConstructorViewAlignmentTrace

/-- Supplemental checker audit for the exact analyzer-owned view of one
constructor.  It follows the validation telescope and instantiates the view
with validation-owned locals; successful execution retains no rewritten
declaration and claims no independent view acceptance. -/
def ConstructorTypeValidationTrace.checkViewAlignment
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) (view : Expr) : M Unit :=
  ConstructorViewAlignmentTrace.check trace view

/-- Source-ordered retained alignment for the complete constructor list.
The source indices make omission, duplication, and reordering unrepresentable.
Each node also retains the closed-root scope check needed to interpret the
validator's original empty-local-context `checkType` observation. -/
inductive ConstructorCandidateAlignmentTrace
    (stats : InductiveStats) (isUnsafe : Bool) (familyIdx : Nat)
    (context : Context) :
    {seen : NameSet} → {constructors : List Constructor} →
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) →
    AddInductive.CandidateList AddInductive.CandidateConstructor constructors →
      Type where
  | nil (seen : NameSet) :
      ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
        (.nil seen) .nil
  | cons
      {seen : NameSet} {head : Constructor} {tail : List Constructor}
      {fresh : seen.contains head.name = false}
      {closed : context.env.checkNoMVarNoFVar head.name head.type = .ok ()}
      {rootCheck : CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type}
      {typeTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
        head.name context head.type 0 context.fuel.inductiveFuel}
      {tailTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail}
      {candidate : AddInductive.CandidateConstructor head}
      {candidates : AddInductive.CandidateList
        AddInductive.CandidateConstructor tail}
      (rootScope : ConstructorCheckedExpr context.withEmptyLocalContext
        head.type)
      (storedSpine : candidate.type.trace.storedSpine = true)
      (spineLength : candidate.type.trace.spineLength =
        typeTrace.spineLength)
      (candidateDepth : candidate.type.context.fuel.recDepth =
        context.fuel.recDepth)
      (headAlignment : ConstructorViewAlignmentTrace typeTrace
        candidate.type.view)
      (tailAlignment : ConstructorCandidateAlignmentTrace stats isUnsafe
        familyIdx context tailTrace candidates) :
      ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
        (.cons seen head tail fresh closed rootCheck typeTrace tailTrace)
        (.cons candidate candidates)

namespace ConstructorCandidateAlignmentTrace

/-- Execute the source-ordered constructor alignment and retain all successful
component checks.  The candidate list's dependent source index selects the
same constructor at every recursive position as the validation trace. -/
def build :
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) →
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) →
      Except Exception
        (ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
          validationTrace candidates)
  | .nil seen, .nil => pure <| .nil seen
  | .cons seen head tail _ _ _ typeTrace tailTrace,
      .cons candidate candidates => do
      let rootScope ← checkConstructorAlignedExpr
        context.withEmptyLocalContext head.type
      if storedSpine : candidate.type.trace.storedSpine = true then
        if spineLength : candidate.type.trace.spineLength =
            typeTrace.spineLength then
          if candidateDepth : candidate.type.context.fuel.recDepth =
              context.fuel.recDepth then
            let headAlignment ← ConstructorViewAlignmentTrace.build typeTrace
              candidate.type.view
            let tailAlignment ← build tailTrace candidates
            pure <| .cons rootScope storedSpine spineLength candidateDepth
              headAlignment tailAlignment
          else
            throw <| .other
              "candidate and validation checker depths differ"
        else
          throw <| .other
            "candidate and validation constructor lengths differ"
      else
        throw <| .other
          "candidate constructor did not preserve its stored spine"

def check
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) : M Unit :=
  fun _ => (build validationTrace candidates).map fun _ => ()

theorem nonempty_of_check
    {validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors}
    (success : check validationTrace candidates context = .ok ()) :
    Nonempty (ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx
      context validationTrace candidates) := by
  unfold check at success
  cases h : build validationTrace candidates with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

/-- A successful alignment audit guarantees the retained builder returns its
trace, so audit owners can replay `build` instead of choosing from
`Nonempty`. -/
theorem build_ok_of_check
    {validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors}
    (success : check validationTrace candidates context = .ok ()) :
    ∃ alignment, build validationTrace candidates = .ok alignment := by
  unfold check at success
  cases h : build validationTrace candidates with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment, rfl⟩

end ConstructorCandidateAlignmentTrace

/-- Source-ordered supplemental alignment audit for every exact constructor
candidate selected by the producer.  The dependent list indices rule out
truncation, reordering, duplication, or a view from another source position.
The Boolean gates additionally pin the candidate main-spine length to the
retained validation telescope. -/
def ConstructorListValidationTrace.checkCandidateAlignment
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) : M Unit :=
  ConstructorCandidateAlignmentTrace.check trace candidates

/-!
## Verified interpretation of the aligned validation telescope

The following semantic traces contain only executions refined by the verified
checker.  Their indices still carry the ordinary validator's branch choices
and exact candidate view, while `ConstructorContextRun` fixes every recursive
local context to the actual post-family Theory environment.
-/

/-- Verified interpretation of every exact WHNF and nested binder visited by
one retained positivity traversal. -/
inductive ConstructorPositivitySemanticRun
    (env : VEnv) (Us : List Name) (whnfFuel : Nat) :
    {stats : InductiveStats} → {ctor : Name} → {argIdx : Nat} →
    {context : Context} → {source : Expr} → {fuel : Nat} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorPositivityTrace stats ctor argIdx context source fuel → Type where
  | absent
      {stats : InductiveStats} {ctor : Name} {argIdx : Nat}
      {context : Context} {source result : Expr} {fuel : Nat}
      {whnfStep : CandidateWhnfStep.Valid ⟨context, source, result⟩}
      {occurs : hasIndOcc stats.indConsts result = false}
      {sourceCheck : ConstructorCheckedExpr context source}
      {contextRun : ConstructorContextRun env Us context}
      (depth : context.fuel.recDepth = whnfFuel + 1)
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (whnfRun : ConstructorWhnfRun contextRun.candidate sourceRun result) :
      ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        (.absent context source result fuel whnfStep occurs)
  | forallE
      {stats : InductiveStats} {ctor : Name} {argIdx : Nat}
      {context : Context} {source : Expr} {fuel : Nat}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {whnfStep : CandidateWhnfStep.Valid
        ⟨context, source, .forallE name domain body binderInfo⟩}
      {occurs : hasIndOcc stats.indConsts
        (.forallE name domain body binderInfo) = true}
      {domainFree : hasIndOcc stats.indConsts domain = false}
      {tailTrace : ConstructorPositivityTrace stats ctor argIdx
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel}
      {sourceCheck : ConstructorCheckedExpr context source}
      {domainCheck : ConstructorCheckedExpr context domain}
      {consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain)}
      {consumedLevel : Level}
      {consumedInferred : consumedCheck.observation.inferred =
        .sort consumedLevel}
      {fresh : context.lctx.find? context.freshFVarId = none}
      {contextRun : ConstructorContextRun env Us context}
      (depth : context.fuel.recDepth = whnfFuel + 1)
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (whnfRun : ConstructorWhnfRun contextRun.candidate sourceRun
        (.forallE name domain body binderInfo))
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (consumedRun : ConstructorCheckedExpr.Run consumedCheck
        contextRun.candidate)
      (annotationsRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain
        (consumeTypeAnnotations domain) domainRun.source'
        consumedRun.source')
      (consumedType : contextRun.candidate.context.IsType
        consumedRun.source')
      (tail : ConstructorPositivitySemanticRun env Us whnfFuel
        (contextRun.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain) fresh consumedRun.source'
          consumedRun.check.expr_tr consumedType)
        tailTrace) :
      ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        (.forallE context source fuel name domain body binderInfo whnfStep
          occurs domainFree tailTrace)
  | target
      {stats : InductiveStats} {ctor : Name} {argIdx : Nat}
      {context : Context} {source result : Expr} {fuel targetIdx : Nat}
      {whnfStep : CandidateWhnfStep.Valid ⟨context, source, result⟩}
      {occurs : hasIndOcc stats.indConsts result = true}
      {terminal : result.isForall = false}
      {valid : isValidIndApp? stats result = some targetIdx}
      {sourceCheck : ConstructorCheckedExpr context source}
      {contextRun : ConstructorContextRun env Us context}
      (depth : context.fuel.recDepth = whnfFuel + 1)
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (whnfRun : ConstructorWhnfRun contextRun.candidate sourceRun result) :
      ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        (.target context source result fuel targetIdx whnfStep occurs terminal
          valid)

namespace ConstructorPositivitySemanticRun

theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    (depth : context.fuel.recDepth = whnfFuel + 1)
    {trace : ConstructorPositivityTrace stats ctor argIdx context source fuel}
    (alignment : ConstructorPositivityAlignmentTrace trace) :
    Nonempty (ConstructorPositivitySemanticRun env Us whnfFuel contextRun
      trace) := by
  induction trace with
  | absent context source result fuel whnfStep occurs =>
      cases alignment with
      | absent sourceCheck =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨whnfRun⟩ := ConstructorWhnfRun.exists
            contextRun.candidate sourceRun whnfStep whnfFuel depth
          exact ⟨ConstructorPositivitySemanticRun.absent
            (stats := stats) (ctor := ctor) (argIdx := argIdx)
            depth sourceRun whnfRun⟩
  | forallE context source fuel name domain body binderInfo whnfStep occurs
      domainFree tailTrace ih =>
      cases alignment with
      | forallE sourceCheck domainCheck consumedCheck consumedLevel
          consumedInferred fresh annotations _ tailAlignment =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨whnfRun⟩ := ConstructorWhnfRun.exists
            contextRun.candidate sourceRun whnfStep whnfFuel depth
          obtain ⟨domainRun⟩ :=
            ConstructorCheckedExpr.Run.exists domainCheck contextRun.candidate
          obtain ⟨consumedRun⟩ :=
            ConstructorCheckedExpr.Run.exists consumedCheck
              contextRun.candidate
          let annotationsRun := domainRun.isDefEq consumedRun annotations
          have consumedType : contextRun.candidate.context.IsType
              consumedRun.source' :=
            consumedRun.isType_of_inferredSort consumedInferred
          let tailContext := contextRun.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain) fresh consumedRun.source'
            consumedRun.check.expr_tr consumedType
          have tailDepth :
              (context.pushLocalDecl name binderInfo
                (consumeTypeAnnotations domain)).fuel.recDepth =
                  whnfFuel + 1 := by
            simpa [AddInductive.Context.pushLocalDecl] using depth
          obtain ⟨tail⟩ := ih tailContext tailDepth tailAlignment
          exact ⟨ConstructorPositivitySemanticRun.forallE
            (stats := stats) (ctor := ctor) (argIdx := argIdx)
            (consumedLevel := consumedLevel)
            (consumedInferred := consumedInferred)
            depth sourceRun whnfRun domainRun consumedRun annotationsRun
            consumedType tail⟩
  | target context source result fuel targetIdx whnfStep occurs terminal valid =>
      cases alignment with
      | target sourceCheck =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨whnfRun⟩ := ConstructorWhnfRun.exists
            contextRun.candidate sourceRun whnfStep whnfFuel depth
          exact ⟨ConstructorPositivitySemanticRun.target
            (stats := stats) (ctor := ctor) (argIdx := argIdx)
            depth sourceRun whnfRun⟩

end ConstructorPositivitySemanticRun

/-- Verified meaning of the exact safe/unsafe positivity branch retained by
ordinary constructor validation. -/
inductive ConstructorPositivityModeSemanticRun
    (env : VEnv) (Us : List Name) (whnfFuel : Nat) :
    {stats : InductiveStats} → {isUnsafe : Bool} → {ctor : Name} →
    {argIdx : Nat} → {context : Context} → {source : Expr} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source →
      Type where
  | skipped :
      {stats : InductiveStats} → {isUnsafe : Bool} → {ctor : Name} →
      {argIdx : Nat} → {context : Context} → {source : Expr} →
      {unsafeEq : isUnsafe = true} →
      {contextRun : ConstructorContextRun env Us context} →
      ConstructorPositivityModeSemanticRun env Us whnfFuel contextRun
        (@ConstructorPositivityModeTrace.skipped stats isUnsafe ctor argIdx
          context source unsafeEq)
  | safe
      {stats : InductiveStats} {isUnsafe : Bool} {ctor : Name}
      {argIdx : Nat} {context : Context} {source : Expr}
      {unsafeEq : isUnsafe = false}
      {positivityTrace : ConstructorPositivityTrace stats ctor argIdx context
        source context.fuel.inductiveFuel}
      {contextRun : ConstructorContextRun env Us context}
      (semantic : ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        positivityTrace) :
      ConstructorPositivityModeSemanticRun env Us whnfFuel contextRun
        (@ConstructorPositivityModeTrace.safe stats isUnsafe ctor argIdx
          context source unsafeEq positivityTrace)

namespace ConstructorPositivityModeSemanticRun

theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    (depth : context.fuel.recDepth = whnfFuel + 1)
    {trace : ConstructorPositivityModeTrace stats isUnsafe ctor argIdx
      context source}
    (alignment : ConstructorPositivityModeAlignmentTrace trace) :
    Nonempty (ConstructorPositivityModeSemanticRun env Us whnfFuel contextRun
      trace) := by
  cases alignment with
  | @skipped unsafeEq =>
      exact ⟨ConstructorPositivityModeSemanticRun.skipped
        (env := env) (Us := Us) (whnfFuel := whnfFuel)
        (stats := stats) (isUnsafe := isUnsafe) (ctor := ctor)
        (argIdx := argIdx) (context := context) (source := source)
        (unsafeEq := unsafeEq) (contextRun := contextRun)⟩
  | safe positivityAlignment =>
      obtain ⟨semantic⟩ :=
        ConstructorPositivitySemanticRun.nonempty_of_alignment contextRun depth
          positivityAlignment
      exact ⟨.safe semantic⟩

end ConstructorPositivityModeSemanticRun

/-- Verified, componentwise interpretation of one aligned constructor
telescope.  The view is followed at validation-owned parameter and field
locals; no equality between candidate and validator fresh identifiers is
required or asserted. -/
inductive ConstructorViewSemanticRun
    (env : VEnv) (Us : List Name) (whnfFuel : Nat) :
    {stats : InductiveStats} → {isUnsafe : Bool} → {familyIdx : Nat} →
    {ctor : Name} → {context : Context} → {source : Expr} →
    {argIdx fuel : Nat} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor context
      source argIdx fuel →
    (view : Expr) → Type where
  | parameter
      {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
      {ctor : Name} {context : Context} {fuel argIdx : Nat}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {param parameterType : Expr}
      {parameterAt : stats.params[argIdx]? = some param}
      {parameterTypeGet : getType param context = .ok parameterType}
      {validationDefEq : CandidateIsDefEqStep.Valid
        ⟨context, domain, parameterType⟩}
      {tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (body.instantiate1 param) (argIdx + 1) fuel}
      {viewName : Name} {viewDomain viewBody : Expr}
      {viewBinderInfo : BinderInfo}
      {domainCheck : ConstructorCheckedExpr context domain}
      {viewDomainCheck : ConstructorCheckedExpr context viewDomain}
      {parameterTypeCheck : ConstructorCheckedExpr context parameterType}
      {contextRun : ConstructorContextRun env Us context}
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (viewDomainRun : ConstructorCheckedExpr.Run viewDomainCheck
        contextRun.candidate)
      (parameterTypeSemantic : ConstructorCheckedExpr.Run parameterTypeCheck
        contextRun.candidate)
      (validationRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain parameterType
        domainRun.source' parameterTypeSemantic.source')
      (tail : ConstructorViewSemanticRun env Us whnfFuel contextRun tailTrace
        (viewBody.instantiate1 param)) :
      ConstructorViewSemanticRun env Us whnfFuel contextRun
        (.parameter context fuel argIdx name domain body binderInfo param
          parameterType parameterAt parameterTypeGet validationDefEq tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | ordinary
      {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
      {ctor : Name} {context : Context} {fuel argIdx : Nat}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {sortResult : Expr} {noParameter : stats.params[argIdx]? = none}
      {ensureTypeStep : ConstructorEnsureTypeStep.Valid
        ⟨context, domain, sortResult⟩}
      {universeTrace : ConstructorUniverseTrace stats.resultLevel
        sortResult.sortLevel!}
      {positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
        argIdx context domain}
      {tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) fuel}
      {viewName : Name} {viewDomain viewBody : Expr}
      {viewBinderInfo : BinderInfo}
      {domainCheck : ConstructorCheckedExpr context domain}
      {viewDomainCheck : ConstructorCheckedExpr context viewDomain}
      {viewEquality : CandidateIsDefEqObservation context domain viewDomain}
      {consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain)}
      {fresh : context.lctx.find? context.freshFVarId = none}
      {contextRun : ConstructorContextRun env Us context}
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (viewDomainRun : ConstructorCheckedExpr.Run viewDomainCheck
        contextRun.candidate)
      (viewEqualityRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain viewDomain
        domainRun.source' viewDomainRun.source')
      (consumedRun : ConstructorCheckedExpr.Run consumedCheck
        contextRun.candidate)
      (ensureTypeRun : TypeChecker.EnsureTypeRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain sortResult
        domainRun.source')
      (positivity : ConstructorPositivityModeSemanticRun env Us whnfFuel
        contextRun positivityTrace)
      (annotationsRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain
        (consumeTypeAnnotations domain) domainRun.source'
        consumedRun.source')
      (consumedType : contextRun.candidate.context.IsType
        consumedRun.source')
      (tail : ConstructorViewSemanticRun env Us whnfFuel
        (contextRun.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain) fresh consumedRun.source'
          consumedRun.check.expr_tr consumedType)
        tailTrace (viewBody.instantiate1 context.freshExpr)) :
      ConstructorViewSemanticRun env Us whnfFuel contextRun
        (.ordinary context fuel argIdx name domain body binderInfo sortResult
          noParameter ensureTypeStep universeTrace positivityTrace tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | terminal
      {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
      {ctor : Name} {context : Context} {source view : Expr}
      {fuel argIdx : Nat} {sourceTerminal : source.isForall = false}
      {sourceValid : isValidIndAppIdx stats source familyIdx = true}
      {sourceCheck : ConstructorCheckedExpr context source}
      {viewCheck : ConstructorCheckedExpr context view}
      {contextRun : ConstructorContextRun env Us context}
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (viewRun : ConstructorCheckedExpr.Run viewCheck contextRun.candidate) :
      ConstructorViewSemanticRun env Us whnfFuel contextRun
        (.terminal context source fuel argIdx sourceTerminal sourceValid) view

namespace ConstructorViewSemanticRun

theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    (depth : context.fuel.recDepth = whnfFuel + 1)
    {validationTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
      ctor context source argIdx fuel}
    {view : Expr}
    (alignment : ConstructorViewAlignmentTrace validationTrace view) :
    Nonempty (ConstructorViewSemanticRun env Us whnfFuel contextRun
      validationTrace view) := by
  induction validationTrace generalizing view with
  | parameter context fuel argIdx name domain body binderInfo param
      parameterType parameterAt parameterTypeGet validationDefEq tailTrace ih =>
      cases alignment with
      | parameter domainCheck viewDomainCheck parameterTypeCheck
          parameterShape parameterPresent _ tailAlignment =>
          obtain ⟨domainRun⟩ :=
            ConstructorCheckedExpr.Run.exists domainCheck contextRun.candidate
          obtain ⟨viewDomainRun⟩ :=
            ConstructorCheckedExpr.Run.exists viewDomainCheck
              contextRun.candidate
          obtain ⟨parameterTypeSemantic⟩ :=
            ConstructorCheckedExpr.Run.exists parameterTypeCheck
              contextRun.candidate
          let validationRun := TypeChecker.IsDefEqRun.ofCandidateStep
            ⟨context, domain, parameterType⟩ validationDefEq
            contextRun.candidate.context contextRun.candidate.context_eq
            rfl rfl rfl contextRun.candidate.state_wf
            domainRun.check.expr_tr parameterTypeSemantic.check.expr_tr
            context.fuel.recDepth rfl
          obtain ⟨tail⟩ := ih contextRun depth tailAlignment
          exact ⟨ConstructorViewSemanticRun.parameter
            domainRun viewDomainRun parameterTypeSemantic validationRun tail⟩
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureTypeStep universeTrace positivityTrace tailTrace ih =>
      cases alignment with
      | ordinary domainCheck viewDomainCheck viewEquality consumedCheck _
          positivityAlignment fresh annotations _ tailAlignment =>
          obtain ⟨domainRun⟩ :=
            ConstructorCheckedExpr.Run.exists domainCheck contextRun.candidate
          obtain ⟨viewDomainRun⟩ :=
            ConstructorCheckedExpr.Run.exists viewDomainCheck
              contextRun.candidate
          let viewEqualityRun := domainRun.isDefEq viewDomainRun viewEquality
          obtain ⟨consumedRun⟩ :=
            ConstructorCheckedExpr.Run.exists consumedCheck
              contextRun.candidate
          obtain ⟨ensureTypeRun⟩ :=
            TypeChecker.EnsureTypeRun.exists_ofConstructorStep
              ⟨context, domain, sortResult⟩ ensureTypeStep
              contextRun.candidate domainRun.source' domainRun.check.expr_tr
          obtain ⟨positivity⟩ :=
            ConstructorPositivityModeSemanticRun.nonempty_of_alignment
              contextRun depth positivityAlignment
          let annotationsRun := domainRun.isDefEq consumedRun annotations
          have consumedType : contextRun.candidate.context.IsType
              consumedRun.source' := by
            have annotationDef := annotationsRun.isDefEqU.of_l
              contextRun.candidate.context.Ewf
              contextRun.candidate.context.Δwf.toCtx
              ensureTypeRun.source_type
            exact ⟨ensureTypeRun.resultLevel', annotationDef.hasType.2⟩
          let tailContext := contextRun.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain) fresh consumedRun.source'
            consumedRun.check.expr_tr consumedType
          have tailDepth :
              (context.pushLocalDecl name binderInfo
                (consumeTypeAnnotations domain)).fuel.recDepth =
                  whnfFuel + 1 := by
            simpa [AddInductive.Context.pushLocalDecl] using depth
          obtain ⟨tail⟩ := ih tailContext tailDepth tailAlignment
          exact ⟨ConstructorViewSemanticRun.ordinary
            (viewEquality := viewEquality)
            domainRun viewDomainRun viewEqualityRun consumedRun ensureTypeRun
            positivity annotationsRun consumedType tail⟩
  | terminal context source fuel argIdx sourceTerminal sourceValid =>
      cases alignment with
      | terminal sourceCheck viewCheck viewTerminal viewValid =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨viewRun⟩ :=
            ConstructorCheckedExpr.Run.exists viewCheck contextRun.candidate
          exact ⟨ConstructorViewSemanticRun.terminal
            (stats := stats) (isUnsafe := isUnsafe)
            (familyIdx := familyIdx) (ctor := ctor)
            sourceRun viewRun⟩

end ConstructorViewSemanticRun

/-!
## Source-ordered post-family constructor semantics

The alignment trace connects the validator's exact source telescope to the
analyzer-owned candidate view.  The semantic list below interprets that trace
alongside the already-produced constructor semantic hierarchy.  Its indices
keep source order, raw constructor order, and the exact candidate view fixed;
its payload retains both validation-local checks and Theory telescope/result
evidence selected by the candidate's recursive checker run.
-/

/-- Complete post-family meaning for every constructor position selected by
one exact validation/candidate alignment.

`root` interprets the validator-owned root `checkType` observation (the
supplemental audit contributes only its scope proof). `telescope` interprets
parameter equality, ordinary-field typing, positivity, and the terminal
family application while following the exact candidate view at
validation-owned locals. `spine` exposes the exact Theory view binders and
terminal result selected by the candidate semantic root. -/
inductive ConstructorPostFamilySemanticListRun
    (env : VEnv) (Us : List Name)
    (stats : InductiveStats) (isUnsafe : Bool) (familyIdx : Nat)
    (context : Context) (contextRun : ConstructorContextRun env Us context) :
    {seen : NameSet} → {constructors : List Constructor} →
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) →
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) →
    {raws : List VConstVal} →
    ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
      validationTrace candidates →
    VInductDecl.CandidateConstructorSemanticListRun env Us candidates raws →
      Type where
  | nil (seen : NameSet) :
      ConstructorPostFamilySemanticListRun env Us stats isUnsafe familyIdx
        context contextRun (.nil seen) .nil (.nil seen) .nil
  | cons
      {seen : NameSet} {head : Constructor} {tail : List Constructor}
      {freshName : seen.contains head.name = false}
      {closed : context.env.checkNoMVarNoFVar head.name head.type = .ok ()}
      {rootCheck : CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type}
      {typeTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
        head.name context head.type 0 context.fuel.inductiveFuel}
      {tailTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail}
      {candidate : AddInductive.CandidateConstructor head}
      {candidates : AddInductive.CandidateList
        AddInductive.CandidateConstructor tail}
      {raw : VConstVal} {raws : List VConstVal}
      {rootScope : ConstructorCheckedExpr context.withEmptyLocalContext
        head.type}
      {storedSpine : candidate.type.trace.storedSpine = true}
      {spineLength : candidate.type.trace.spineLength =
        typeTrace.spineLength}
      {candidateDepth : candidate.type.context.fuel.recDepth =
        context.fuel.recDepth}
      {headAlignment : ConstructorViewAlignmentTrace typeTrace
        candidate.type.view}
      {tailAlignment : ConstructorCandidateAlignmentTrace stats isUnsafe
        familyIdx context tailTrace candidates}
      {headSemantic : VInductDecl.CandidateConstructorSemanticRun env Us
        candidate raw}
      {tailSemantic : VInductDecl.CandidateConstructorSemanticListRun env Us
        candidates raws}
      (root : ConstructorCheckedExpr.Run
        (rootScope.withObservation rootCheck)
        contextRun.withEmptyLocalContext.candidate)
      (telescope : ConstructorViewSemanticRun env Us
        headSemantic.type.whnfFuel contextRun typeTrace candidate.type.view)
      (spine : ∃ resultType,
        TypeChecker.TelResultDefEqEvidence env Us.length []
          (VExpr.telN candidate.type.trace.spineLength raw.type)
          (VExpr.telN candidate.type.trace.spineLength
            headSemantic.type.view)
          (VExpr.dropN candidate.type.trace.spineLength raw.type)
          (VExpr.dropN candidate.type.trace.spineLength
            headSemantic.type.view)
          resultType)
      (tailRun : ConstructorPostFamilySemanticListRun env Us stats isUnsafe
        familyIdx context contextRun tailTrace candidates
        tailAlignment tailSemantic) :
      ConstructorPostFamilySemanticListRun env Us stats isUnsafe familyIdx
        context contextRun
        (.cons seen head tail freshName closed rootCheck typeTrace tailTrace)
        (.cons candidate candidates)
        (.cons rootScope storedSpine spineLength candidateDepth headAlignment
          tailAlignment)
        (.cons headSemantic tailSemantic)

namespace ConstructorPostFamilySemanticListRun

/-- Interpret an exact source-ordered alignment together with the exact
candidate semantic list produced for the same raw constructor positions. -/
theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    {validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors}
    {raws : List VConstVal}
    (alignment : ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx
      context validationTrace candidates)
    (semantics : VInductDecl.CandidateConstructorSemanticListRun env Us
      candidates raws) :
    Nonempty (ConstructorPostFamilySemanticListRun env Us stats isUnsafe
      familyIdx context contextRun validationTrace candidates alignment
      semantics) := by
  induction alignment generalizing raws with
  | nil seen =>
      cases semantics
      exact ⟨.nil seen⟩
  | @cons seen head tail freshName closed rootCheck typeTrace tailTrace
      candidate candidates rootScope storedSpine spineLength candidateDepth
      headAlignment tailAlignment ih =>
      cases semantics with
      | cons headSemantic tailSemantic =>
          obtain ⟨root⟩ := ConstructorCheckedExpr.Run.exists
            (rootScope.withObservation rootCheck)
            contextRun.withEmptyLocalContext.candidate
          have depth : context.fuel.recDepth =
              headSemantic.type.whnfFuel + 1 := by
            calc
              context.fuel.recDepth =
                  candidate.type.context.fuel.recDepth := candidateDepth.symm
              _ = headSemantic.type.whnfFuel + 1 :=
                headSemantic.type.whnfDepth
          obtain ⟨telescope⟩ :=
            ConstructorViewSemanticRun.nonempty_of_alignment contextRun depth
              headAlignment
          have spine := TypeChecker.CandidateExprSpineRun.evidence
            (headSemantic.type.spine storedSpine)
          obtain ⟨tailRun⟩ := ih tailSemantic
          exact ⟨.cons root telescope spine tailRun⟩

end ConstructorPostFamilySemanticListRun

/-- A retained constructor telescope whose strengthened universe decisions are
all true replays the exact executable universe traversal.  This is the
converse of `universeSemantics_of_loop`: the trace supplies the same parameter
choices and `ensureType` results, while the Boolean supplies only the
additional verified comparison at ordinary fields. -/
theorem ConstructorTypeValidationTrace.universeLoop_of_semantics
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel)
    (semantic : trace.universeSemantics = true) :
    checkConstructorUniverseSemantics.loop stats source argIdx fuel context =
      .ok () := by
  induction trace with
  | parameter context fuel argIdx name domain body binderInfo parameter
      parameterType parameterAt parameterTypeRun defeq tail ih =>
      simp only [universeSemantics] at semantic
      rw [show fuel + 1 = Nat.succ fuel by rfl]
      rw [checkConstructorUniverseSemantics.loop.eq_2]
      rw [parameterAt]
      exact ih semantic
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureType universeTrace positivity tail ih =>
      simp only [universeSemantics, Bool.and_eq_true] at semantic
      rw [show fuel + 1 = Nat.succ fuel by rfl]
      rw [checkConstructorUniverseSemantics.loop.eq_2]
      rw [noParameter]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [ensureType]
      simp only [Except.bind]
      have valid : constructorUniverseSemanticGe stats.resultLevel
          sortResult.sortLevel! = true := by
        simpa only [ConstructorUniverseTrace.semantic] using semantic.1
      rw [valid]
      simp only []
      exact ih semantic.2
  | terminal context source fuel argIdx terminal valid =>
      cases source <;> try rfl
      case forallE =>
        change true = false at terminal
        contradiction

/-- Root form of `universeLoop_of_semantics`, initialized from the same
context fuel as ordinary constructor validation. -/
theorem ConstructorTypeValidationTrace.universeRun_of_semantics
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source 0 context.fuel.inductiveFuel)
    (semantic : trace.universeSemantics = true) :
    checkConstructorUniverseSemantics stats source context = .ok () := by
  unfold checkConstructorUniverseSemantics
  simpa only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure] using trace.universeLoop_of_semantics semantic

/-- A retained source-ordered constructor list whose strengthened universe
decisions are all true replays the exact executable list audit. -/
theorem ConstructorListValidationTrace.universeRun_of_semantics
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (semantic : trace.universeSemantics = true) :
    checkConstructorUniverseListSemantics stats constructors context =
      .ok () := by
  induction trace with
  | nil => rfl
  | cons seen head tail fresh closed rootCheck typeTrace tailTrace ih =>
      simp only [universeSemantics, Bool.and_eq_true] at semantic
      simp only [checkConstructorUniverseListSemantics,
        ReaderT.bind, Bind.bind]
      rw [typeTrace.universeRun_of_semantics semantic.1]
      simp only [Except.bind]
      exact ih semantic.2

/-- Impredicative `Prop` makes every strengthened constructor-universe node
true, independently of the field level selected by the retained checker run. -/
theorem ConstructorUniverseTrace.semantic_of_resultLevel_isZero
    (trace : ConstructorUniverseTrace resultLevel fieldLevel)
    (zero : resultLevel.isZero = true) : trace.semantic = true := by
  simp [ConstructorUniverseTrace.semantic, constructorUniverseSemanticGe,
    zero]

/-- Every universe node in a retained constructor telescope is admitted by
the strengthened audit when the family result is `Prop`. -/
theorem ConstructorTypeValidationTrace.universeSemantics_of_resultLevel_isZero
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel)
    (zero : stats.resultLevel.isZero = true) :
    trace.universeSemantics = true := by
  induction trace with
  | parameter context fuel argIdx name domain body binderInfo parameter
      parameterType parameterAt parameterTypeRun defeq tail ih =>
      simpa only [universeSemantics] using ih
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureType universeTrace positivity tail ih =>
      simp only [universeSemantics, Bool.and_eq_true]
      exact ⟨universeTrace.semantic_of_resultLevel_isZero zero, ih⟩
  | terminal => rfl

/-- Source-list form of
`ConstructorTypeValidationTrace.universeSemantics_of_resultLevel_isZero`. -/
theorem ConstructorListValidationTrace.universeSemantics_of_resultLevel_isZero
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (zero : stats.resultLevel.isZero = true) :
    trace.universeSemantics = true := by
  induction trace with
  | nil => rfl
  | cons seen head tail fresh closed rootCheck typeTrace tailTrace ih =>
      simp only [universeSemantics, Bool.and_eq_true]
      exact ⟨typeTrace.universeSemantics_of_resultLevel_isZero zero, ih⟩

/-- A successful executable universe audit marks every universe node in an
arbitrary retained constructor telescope.  The proof uses determinism of the
same `ensureType` execution retained by the ordinary trace; it cannot change a
field level or skip a source position. -/
theorem ConstructorTypeValidationTrace.universeSemantics_of_loop
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel)
    (success : checkConstructorUniverseSemantics.loop stats source argIdx fuel
      context = .ok ()) :
    trace.universeSemantics = true := by
  induction trace with
  | parameter context fuel argIdx name domain body binderInfo parameter
      parameterType parameterAt parameterTypeRun defeq tail ih =>
      simp only [universeSemantics]
      rw [show fuel + 1 = Nat.succ fuel by rfl] at success
      rw [checkConstructorUniverseSemantics.loop.eq_2] at success
      rw [parameterAt] at success
      exact ih success
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureType universeTrace positivity tail ih =>
      simp only [universeSemantics, Bool.and_eq_true]
      rw [show fuel + 1 = Nat.succ fuel by rfl] at success
      rw [checkConstructorUniverseSemantics.loop.eq_2] at success
      rw [noParameter] at success
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
      rw [ensureType] at success
      simp only [Except.bind] at success
      cases valid : constructorUniverseSemanticGe stats.resultLevel
          sortResult.sortLevel! with
      | false =>
          rw [valid] at success
          change Except.error _ = Except.ok () at success
          cases success
      | true =>
          rw [valid] at success
          simp only [] at success
          exact ⟨valid, ih success⟩
  | terminal => rfl

/-- Root form of `universeSemantics_of_loop`, with the audit initialized from
the exact context fuel just like ordinary constructor validation. -/
theorem ConstructorTypeValidationTrace.universeSemantics_of_run
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source 0 context.fuel.inductiveFuel)
    (success : checkConstructorUniverseSemantics stats source context =
      .ok ()) :
    trace.universeSemantics = true := by
  apply trace.universeSemantics_of_loop
  simpa only [checkConstructorUniverseSemantics, readThe,
    MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
    ReaderT.pure, Pure.pure, Except.bind, Except.pure] using success

/-- A successful source-list audit marks every retained constructor position;
the dependent list indices prevent omission, duplication, or reordering. -/
theorem ConstructorListValidationTrace.universeSemantics_of_run
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (success : checkConstructorUniverseListSemantics stats constructors
      context = .ok ()) :
    trace.universeSemantics = true := by
  induction trace with
  | nil => rfl
  | cons seen head tail fresh closed rootCheck typeTrace tailTrace ih =>
      simp only [universeSemantics, Bool.and_eq_true]
      simp only [checkConstructorUniverseListSemantics,
        ReaderT.bind, Bind.bind] at success
      cases headRun : checkConstructorUniverseSemantics stats head.type
          context with
      | error error =>
          rw [headRun] at success
          cases success
      | ok result =>
          cases result
          rw [headRun] at success
          simp only [Except.bind] at success
          exact ⟨typeTrace.universeSemantics_of_run headRun, ih success⟩

/-- Ordinary constructor validation paired with the executable semantic
universe audit over the identical singleton source list. This record narrows
the accepted package boundary while preserving the ordinary validator result
and every retained non-universe check unchanged. -/
structure ConstructorSemanticValidationRun
    (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) where
  validation : ConstructorValidationRun indType stats isUnsafe context
  universeRun : checkConstructorUniverseListSemantics stats indType.ctors
    context = .ok ()

namespace ConstructorSemanticValidationRun

/-- Forgetting the semantic audit replays the exact ordinary validator, so
the strengthened run cannot widen kernel acceptance. -/
theorem run
    (semantic : ConstructorSemanticValidationRun indType stats isUnsafe
      context) :
    checkConstructors #[indType] stats isUnsafe context = .ok () :=
  semantic.validation.run

/-- Every universe-bearing node of the retained ordinary trace passed the
executable verified universe gate. -/
theorem universeSemantics
    (semantic : ConstructorSemanticValidationRun indType stats isUnsafe
      context) :
    semantic.validation.universeSemantics = true :=
  semantic.validation.trace.universeSemantics_of_run semantic.universeRun

end ConstructorSemanticValidationRun

/-- The semantic universe gate only accepts branches already accepted by the
ordinary constructor validator.  It therefore narrows package construction
without widening kernel validation behavior. -/
theorem ConstructorUniverseTrace.nonempty_of_semanticGe
    (valid : constructorUniverseSemanticGe resultLevel fieldLevel = true) :
    Nonempty (ConstructorUniverseTrace resultLevel fieldLevel) := by
  unfold constructorUniverseSemanticGe at valid
  simp only [Bool.or_eq_true, Bool.and_eq_true] at valid
  rcases valid with structural | prop | ⟨core, _verified⟩
  · exact ⟨.structural structural⟩
  · cases hstruct : levelStructGe resultLevel fieldLevel with
    | true => exact ⟨.structural hstruct⟩
    | false =>
        exact ⟨.fallback hstruct
          (by cases resultLevel <;> simp_all [Level.isZero, Level.isAlwaysZero])⟩
  · cases hstruct : levelStructGe resultLevel fieldLevel with
    | true => exact ⟨.structural hstruct⟩
    | false =>
        exact ⟨.fallback hstruct (by simp [core])⟩

/-- The executable semantic subset implies exactly the disjunct required for
a non-recursive field in `VInductDecl.fieldsWF`: either the family is Prop or
the field universe is bounded by the family universe. -/
theorem constructorUniverseSemanticGe_ofLevel
    (valid : constructorUniverseSemanticGe resultLevel fieldLevel = true)
    (result_tr : VLevel.ofLevel Us resultLevel = some result')
    (field_tr : VLevel.ofLevel Us fieldLevel = some field') :
    result' = .zero ∨ field' ≤ result' := by
  unfold constructorUniverseSemanticGe at valid
  simp only [Bool.or_eq_true, Bool.and_eq_true] at valid
  rcases valid with structural | prop | ⟨_core, verified⟩
  · exact .inr (levelStructGe_ofLevel structural result_tr field_tr)
  · exact .inl (ofLevel_eq_zero_of_isZero prop result_tr)
  · exact .inr (Level.geq'_wf result_tr field_tr verified)

/-- Agreement between the ordinary and verified normalized comparisons opens
the semantic fallback without weakening the ordinary acceptance boundary. -/
theorem constructorUniverseSemanticGe_eq_true_of_geq_agreement
    (core : resultLevel.geq fieldLevel = true)
    (verified : resultLevel.geq' fieldLevel = true) :
    constructorUniverseSemanticGe resultLevel fieldLevel = true := by
  simp [constructorUniverseSemanticGe, core, verified]

private def constructorUniverseComparisonSamples : List Level :=
  [.zero,
   .succ .zero,
   .succ (.succ .zero),
   .param `u,
   .param `v,
   .succ (.param `u),
   .max (.param `u) (.param `v),
   .max (.succ (.param `u)) (.param `v),
   .imax (.param `u) (.param `v),
   .imax (.param `u) (.succ (.param `v)),
   .imax (.max (.param `u) (.param `v)) (.succ .zero),
   .max (.imax (.param `u) (.param `v)) (.succ (.param `v))]

/- Differential audit for the mvar-free surface accepted by constructors.
Every pair in this matrix compares Lean v4.31's core decision with the proved
project decision; the samples exercise zero, successor, maximum, impredicative
maximum, parameters, and nested combinations. -/
#guard constructorUniverseComparisonSamples.all fun resultLevel =>
  constructorUniverseComparisonSamples.all fun fieldLevel =>
    resultLevel.geq fieldLevel == resultLevel.geq' fieldLevel

/- Regression for the former D1 gap: the structural and `Prop` branches both
miss a parameter below a `max`, while core/project normalized comparison
agrees and the verified semantic fallback now accepts it. -/
private def constructorUniverseNormalizedResult : Level :=
  .max (.param `u) (.param `v)

#guard !levelStructGe constructorUniverseNormalizedResult (.param `u)
#guard !constructorUniverseNormalizedResult.isZero
#guard constructorUniverseNormalizedResult.geq (.param `u)
#guard constructorUniverseNormalizedResult.geq' (.param `u)
#guard constructorUniverseSemanticGe constructorUniverseNormalizedResult
  (.param `u)

/- The universe bridge stays within Lean's standard logical basis.  In
particular it does not inherit the project's pending sorries, a custom axiom,
or a semantic premise for Lean's opaque `Level.geq` implementation. -/
#guard_named_axioms Ix.Theory.Named.AddInductive.levelStructEq_ofLevel [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.levelStructGe_ofLevel [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.constructorUniverseSemanticGe_ofLevel [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Std.TreeMap.all_eq_all_toList]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorUniverseTrace.nonempty_of_semanticGe [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorSemanticValidationRun.universeSemantics [propext, Classical.choice, Quot.sound]

/- The reverse executable bridge and its impredicative-Prop specialization
have the same standard-only closure as the forward universe interpretation.
In particular, replaying a retained validator trace does not inherit a
fixture computation oracle. -/
#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorTypeValidationTrace.universeLoop_of_semantics [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorTypeValidationTrace.universeRun_of_semantics [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorListValidationTrace.universeRun_of_semantics [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorUniverseTrace.semantic_of_resultLevel_isZero [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorTypeValidationTrace.universeSemantics_of_resultLevel_isZero [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorListValidationTrace.universeSemantics_of_resultLevel_isZero [propext, Classical.choice, Quot.sound]

/-!
## Executable pre-family safety and replay

The post-family validator introduces a local declaration for every constructor
field.  A recursive field's local type mentions the family being defined, so
that declaration cannot be reproduced in the pre-family verifier context.
For the current singleton subset we omit such locals, advance the validator's
fresh-name supply, and permit later checks only when their source expressions
do not mention an omitted identifier.  Independent ordinary fields may still
follow recursive fields; genuinely dependent uses remain outside this replay.

The traces below are outputs of executable builders.  Their proof fields are
exact `checkType`, `ensureType`, and `isDefEq` executions; they are operational
evidence, not caller-supplied Theory judgments.
-/

/-- Executable fragment on which strict kernel-to-Theory translation has a
syntactically unique endpoint.  Projections are excluded because the current
`TrProj` contract determines their result only up to definitional equality;
projection-bearing inductives require an exact structural projection API
before they can be included in the singleton subset. -/
def theoryTranslationUnique : Expr → Bool
  | .bvar _
  | .fvar _
  | .sort _
  | .const ..
  | .mvar ..
  | .lit _ => true
  | .app fn argument =>
      theoryTranslationUnique fn && theoryTranslationUnique argument
  | .lam _ domain body _
  | .forallE _ domain body _ =>
      theoryTranslationUnique domain && theoryTranslationUnique body
  | .letE _ _ value body _ =>
      theoryTranslationUnique value && theoryTranslationUnique body
  | .mdata _ expression => theoryTranslationUnique expression
  | .proj .. => false

/-- The executable predicate is exactly the structural proposition used by
strict-translation uniqueness. -/
theorem theoryTranslationUnique_sound
    (success : theoryTranslationUnique expression = true) :
    TrExprS.IsUnique expression := by
  induction expression <;>
    simp_all [theoryTranslationUnique, TrExprS.IsUnique]

/-- Abstracting one free variable preserves the projection-free fragment:
the operation changes only free/bound-variable identities and recursively
retains every expression constructor. -/
theorem theoryTranslationUnique_abstract1
    (expression : Expr) (id : FVarId) (depth : Nat) :
    theoryTranslationUnique (Expr.abstract1 id expression depth) =
      theoryTranslationUnique expression := by
  induction expression generalizing depth <;>
    simp [Expr.abstract1, theoryTranslationUnique, *]
  split <;> rfl

/-- Iterated free-variable abstraction likewise preserves the executable
strict-translation fragment. -/
theorem theoryTranslationUnique_abstractList
    (expression : Expr) (ids : List FVarId) (depth : Nat) :
    theoryTranslationUnique (Expr.abstractList expression ids depth) =
      theoryTranslationUnique expression := by
  induction ids generalizing expression with
  | nil => rfl
  | cons id ids ih =>
      simp only [Expr.abstractList, ih,
        theoryTranslationUnique_abstract1]

/-- Array-form abstraction over an explicit list of free variables preserves
the projection-free fragment. -/
theorem theoryTranslationUnique_abstractFVars
    (expression : Expr) (ids : List FVarId) :
    theoryTranslationUnique
        (expression.abstract ⟨ids.map Expr.fvar⟩) =
      theoryTranslationUnique expression := by
  rw [Expr.abstract_eq]
  exact theoryTranslationUnique_abstractList expression ids 0

/-- Every syntax fragment contributing to a recursively reconstructed
candidate view has a unique strict Theory endpoint.  Checking recursive body
views as well as their stored abstractions supplies precisely the induction
hypotheses consumed by `CandidateExprRun.view_tr_strict`. -/
def CandidateExprTrace.viewTranslationUnique :
    {context : Context} → {source : Expr} →
      CandidateExprTrace context source → Bool
  | _, _, .terminal _ _ _ result _ _ => theoryTranslationUnique result
  | _, _, .forallE context _ _ _ _ _ _ _ _ _ _ _ domain body =>
      domain.viewTranslationUnique &&
        (body.viewTranslationUnique &&
          theoryTranslationUnique
            (body.view.abstract #[context.freshExpr]))

/-- The recursive check is extensionally the projection-free check on the
reconstructed analyzer view. Its explicit body clause supplies the induction
hypothesis consumed by the strict-view proof. -/
theorem CandidateExprTrace.viewTranslationUnique_eq
    (trace : CandidateExprTrace context source) :
    trace.viewTranslationUnique = theoryTranslationUnique trace.view := by
  induction trace with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainTrace bodyTrace
      domainIH bodyIH =>
    simp only [viewTranslationUnique, CandidateExprTrace.view,
      theoryTranslationUnique, domainIH, bodyIH]
    rw [show #[context.freshExpr] =
      ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl,
      theoryTranslationUnique_abstractFVars]
    simp

/-- A successful recursive executable check supplies the exact proposition
required by strict candidate-view translation. -/
theorem CandidateExprTrace.viewTranslationUnique_sound
    (trace : CandidateExprTrace context source)
    (success : trace.viewTranslationUnique = true) :
    TypeChecker.CandidateExprTraceViewIsUnique trace := by
  induction trace with
  | terminal => exact theoryTranslationUnique_sound success
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainTrace bodyTrace
      domainIH bodyIH =>
    simp only [viewTranslationUnique, Bool.and_eq_true] at success
    exact ⟨domainIH success.1, bodyIH success.2.1,
      theoryTranslationUnique_sound success.2.2⟩

/-- Source-ordered strict-view check for an exact dependent constructor
candidate list. -/
def CandidateList.viewTranslationUnique :
    {constructors : List Constructor} →
      CandidateList CandidateConstructor constructors → Bool
  | _, .nil => true
  | _, .cons candidate candidates =>
      candidate.type.trace.viewTranslationUnique &&
        candidates.viewTranslationUnique

/-- Proof-level source-ordered counterpart of
`CandidateList.viewTranslationUnique`. -/
def CandidateList.ViewTranslationUnique :
    {constructors : List Constructor} →
      CandidateList CandidateConstructor constructors → Prop
  | _, .nil => True
  | _, .cons candidate candidates =>
      TypeChecker.CandidateExprTraceViewIsUnique candidate.type.trace ∧
        candidates.ViewTranslationUnique

theorem CandidateList.viewTranslationUnique_sound
    (candidates : CandidateList CandidateConstructor constructors)
    (success : candidates.viewTranslationUnique = true) :
    candidates.ViewTranslationUnique := by
  induction candidates with
  | nil => trivial
  | cons candidate candidates ih =>
    simp only [viewTranslationUnique, Bool.and_eq_true] at success
    exact ⟨candidate.type.trace.viewTranslationUnique_sound success.1,
      ih success.2⟩

/-- Advance the constructor traversal's fresh-name supply without adding the
family-dependent local declaration for a recursive outer field. -/
def Context.advanceFresh (context : Context) : Context :=
  { context with ngen := context.ngen.next }

/-- Advancing an omitted recursive field changes only the candidate name
generator.  The verified checker context and its empty-state certificate remain
the same because `Context.toTypeChecker` deliberately has no name-generator
field. -/
def advanceCandidateContextRun
    (run : TypeChecker.CandidateContextRun context) :
    TypeChecker.CandidateContextRun context.advanceFresh := by
  refine ⟨run.context, ?_, run.state_wf, ?_⟩
  · simpa [Context.advanceFresh, Context.toTypeChecker] using run.context_eq
  · simpa [Context.advanceFresh, NameGenerator.next] using run.namePrefix_ne

/-- Keep the fixed pre-family Theory environment/universe indices while the
operational traversal advances past an omitted recursive outer field. -/
def ConstructorContextRun.advanceFresh
    (run : ConstructorContextRun env Us context) :
    ConstructorContextRun env Us context.advanceFresh where
  candidate := advanceCandidateContextRun run.candidate
  venv_eq := run.venv_eq
  lparams_eq := run.lparams_eq

/-- Syntactic independence from the recursive outer-field locals omitted by
the pre-family replay context. -/
def constructorIndependentOf (source : Expr) (removed : List FVarId) : Bool :=
  source.fvarsList.all fun fv => !removed.contains fv

/-- Instantiate the analyzer-owned family view with the exact parameter FVars
selected by family validation, leaving the index telescope exposed. -/
def instantiateFamilyParameters : Expr → List Expr → Except Exception Expr
  | familyType, [] => pure familyType
  | .forallE _ _ body _, parameter :: parameters =>
      instantiateFamilyParameters (body.instantiate1 parameter) parameters
  | _, _ :: _ =>
      throw <| .other
        "candidate family view has fewer binders than retained parameters"

/-- Exact successful pre-family `ensureType` observation. -/
structure ConstructorEnsureTypeObservation
    (context : Context) (source : Expr) where
  result : Expr
  valid : ConstructorEnsureTypeStep.Valid ⟨context, source, result⟩

def observeConstructorEnsureType (context : Context) (source : Expr) :
    Except Exception (ConstructorEnsureTypeObservation context source) :=
  match hrun : TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.ensureType source) with
  | .error error => .error error
  | .ok result => .ok ⟨result, hrun⟩

theorem observeConstructorEnsureType_of_run
    (run : ConstructorEnsureTypeStep.Valid ⟨context, source, result⟩) :
    observeConstructorEnsureType context source = .ok ⟨result, run⟩ := by
  change TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.ensureType source) =
    .ok result at run
  unfold observeConstructorEnsureType
  split
  · simp_all
  · rename_i observed hobserved
    have : observed = result := by simp_all
    subst observed
    rfl

theorem ConstructorEnsureTypeObservation.observe_eq
    (observation : ConstructorEnsureTypeObservation context source) :
    observeConstructorEnsureType context source = .ok observation := by
  rw [observeConstructorEnsureType_of_run observation.valid]

/-- One pre-family index argument checked against the corresponding binder of
the parameter-instantiated family view. -/
structure ConstructorPreFamilyIndexStep
    (context : Context) (argument expected : Expr) where
  argumentCheck : ConstructorCheckedExpr context argument
  expectedCheck : ConstructorCheckedExpr context expected
  comparison : CandidateIsDefEqObservation context
    argumentCheck.observation.inferred expected

/-- Source-ordered executable replay of a constructor result/recursive-target
index spine against the analyzer-owned family index telescope. -/
inductive ConstructorPreFamilyIndexSpineTrace :
    (context : Context) → (expected : Expr) → List Expr → Type where
  | nil
      (context : Context) (expected : Expr)
      (expectedCheck : ConstructorCheckedExpr context expected)
      (terminal : expected.isForall = false) :
      ConstructorPreFamilyIndexSpineTrace context expected []
  | cons
      (context : Context) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo) (argument : Expr) (arguments : List Expr)
      (expectedCheck : ConstructorCheckedExpr context
        (.forallE name domain body binderInfo))
      (step : ConstructorPreFamilyIndexStep context argument domain)
      (tail : ConstructorPreFamilyIndexSpineTrace context
        (body.instantiate1 argument) arguments) :
      ConstructorPreFamilyIndexSpineTrace context
        (.forallE name domain body binderInfo) (argument :: arguments)

namespace ConstructorPreFamilyIndexSpineTrace

def build : (context : Context) → (expected : Expr) →
    (arguments : List Expr) →
    Except Exception
      (ConstructorPreFamilyIndexSpineTrace context expected arguments)
  | context, expected, [] =>
      if terminal : expected.isForall = false then do
        let expectedCheck ← checkConstructorAlignedExpr context expected
        pure <| .nil context expected expectedCheck terminal
      else
        throw <| .other
          "constructor target supplies too few family indices"
  | context, .forallE name domain body binderInfo, argument :: arguments => do
      let telescopeCheck ← checkConstructorAlignedExpr context
        (.forallE name domain body binderInfo)
      let argumentCheck ← checkConstructorAlignedExpr context argument
      let domainCheck ← checkConstructorAlignedExpr context domain
      let comparison ← observeCandidateIsDefEq context
        argumentCheck.observation.inferred domain
      let tail ← build context (body.instantiate1 argument) arguments
      pure <| .cons context name domain body binderInfo argument arguments
        telescopeCheck ⟨argumentCheck, domainCheck, comparison⟩ tail
  | _, _, _ :: _ =>
      throw <| .other
        "constructor target supplies too many family indices"

end ConstructorPreFamilyIndexSpineTrace

theorem ConstructorPreFamilyIndexSpineTrace.build_eq
    (trace : ConstructorPreFamilyIndexSpineTrace context expected arguments) :
    ConstructorPreFamilyIndexSpineTrace.build context expected arguments =
      .ok trace := by
  induction trace with
  | nil expected expectedCheck terminal =>
      simp only [ConstructorPreFamilyIndexSpineTrace.build]
      rw [dif_pos terminal, expectedCheck.check_eq]
      rfl
  | cons name domain body binderInfo argument arguments
      expectedCheck step tail ih =>
      simp only [ConstructorPreFamilyIndexSpineTrace.build]
      rw [expectedCheck.check_eq, step.argumentCheck.check_eq,
        step.expectedCheck.check_eq]
      simp only [Bind.bind, Except.bind]
      rw [step.comparison.observe_eq, ih]
      rfl

/-- The exact full check retained at the root of an index-spine replay. -/
def ConstructorPreFamilyIndexSpineTrace.expectedCheck :
    (trace : ConstructorPreFamilyIndexSpineTrace context expected arguments) →
      ConstructorCheckedExpr context expected
  | .nil _ _ expectedCheck _ => expectedCheck
  | .cons _ _ _ _ _ _ _ expectedCheck _ _ => expectedCheck

/-!
### Verified pre-family index spines

The operational trace checks the complete expected family-index telescope at
every recursive position. Its semantic interpretation follows the strict
translation selected at the root, instantiates the translated Pi body with the
translated argument, and therefore constructs an actual Theory `SpineWF`
rather than a pointwise list whose dependencies have been forgotten.
-/

/-- Verified meaning of one pre-family index-spine replay. `expected'` is a
strict translation of the exact parameter-instantiated family telescope in the
current context; `arguments'` and `result'` are forced by the retained checker
executions and dependent Pi instantiation. -/
structure ConstructorPreFamilyIndexSpineSemanticRun
    (env : VEnv) (Us : List Name)
    (context : Context) (contextRun : ConstructorContextRun env Us context)
    {expected : Expr} {arguments : List Expr}
    (trace : ConstructorPreFamilyIndexSpineTrace context expected arguments)
    (expected' : VExpr) where
  expectedInferred' : VExpr
  expectedRun : TypeChecker.CheckTypeRun env Us
    contextRun.candidate.context.vlctx expected
    trace.expectedCheck.observation.inferred expected' expectedInferred'
  arguments' : List VExpr
  result' : VExpr
  arguments_tr : List.Forall₂
    (TrExprS env Us contextRun.candidate.context.vlctx)
    arguments arguments'
  spine : env.SpineWF Us.length contextRun.candidate.context.vlctx.toCtx
    expected' arguments' result'

namespace ConstructorPreFamilyIndexSpineSemanticRun

/-- Interpret a spine at a caller-fixed strict translation of its expected
telescope. Recursive calls receive the translated Pi body instantiated with
the exact checker-selected argument translation. -/
theorem nonempty_at
    (contextRun : ConstructorContextRun env Us context)
    (trace : ConstructorPreFamilyIndexSpineTrace context expected arguments)
    (expected' : VExpr)
    (expected_tr : TrExprS env Us
      contextRun.candidate.context.vlctx expected expected') :
    Nonempty (ConstructorPreFamilyIndexSpineSemanticRun env Us context
      contextRun trace expected') := by
  induction trace generalizing expected' with
  | nil expected expectedCheck terminal =>
      have expected_tr' : contextRun.candidate.context.TrExprS expected
          expected' := by
        simpa only [VContext.TrExprS, contextRun.venv_eq,
          contextRun.lparams_eq] using expected_tr
      obtain ⟨expectedInferred', ⟨expectedRun⟩⟩ :=
        TypeChecker.CheckTypeRun.exists_ofCandidateStep
          ⟨context, expected, expectedCheck.observation.inferred⟩
          expectedCheck.observation.valid contextRun.candidate expected'
          expected_tr'
      exact ⟨{
        expectedInferred' := expectedInferred'
        expectedRun := by
          simpa only [ConstructorPreFamilyIndexSpineTrace.expectedCheck,
            contextRun.venv_eq, contextRun.lparams_eq] using expectedRun
        arguments' := []
        result' := expected'
        arguments_tr := .nil
        spine := .nil }⟩
  | cons name domain body binderInfo argument arguments telescopeCheck
      step tail ih =>
      obtain ⟨domain', body', rfl, domainType, bodyType, domain_tr,
          body_tr⟩ := TypeChecker.TrExprS.forallE_components expected_tr
      have telescope_tr' : contextRun.candidate.context.TrExprS
          (.forallE name domain body binderInfo) (.forallE domain' body') := by
        simpa only [VContext.TrExprS, contextRun.venv_eq,
          contextRun.lparams_eq] using expected_tr
      obtain ⟨expectedInferred', ⟨expectedRun⟩⟩ :=
        TypeChecker.CheckTypeRun.exists_ofCandidateStep
          ⟨context, .forallE name domain body binderInfo,
            telescopeCheck.observation.inferred⟩
          telescopeCheck.observation.valid contextRun.candidate
          (.forallE domain' body') telescope_tr'
      have domain_tr' : contextRun.candidate.context.TrExprS domain domain' := by
        simpa only [VContext.TrExprS, contextRun.venv_eq,
          contextRun.lparams_eq] using domain_tr
      obtain ⟨domainInferred', ⟨domainCheck⟩⟩ :=
        TypeChecker.CheckTypeRun.exists_ofCandidateStep
          ⟨context, domain, step.expectedCheck.observation.inferred⟩
          step.expectedCheck.observation.valid contextRun.candidate domain'
          domain_tr'
      let domainRun : ConstructorCheckedExpr.Run step.expectedCheck
          contextRun.candidate := ⟨domain', domainInferred', domainCheck⟩
      obtain ⟨argumentRun⟩ := ConstructorCheckedExpr.Run.exists
        step.argumentCheck contextRun.candidate
      let comparisonRun := TypeChecker.IsDefEqRun.ofCandidateStep
        ⟨context, step.argumentCheck.observation.inferred, domain⟩
        step.comparison.valid contextRun.candidate.context
        contextRun.candidate.context_eq rfl rfl rfl
        contextRun.candidate.state_wf argumentRun.check.inferred_tr
        domainRun.check.expr_tr context.fuel.recDepth rfl
      have argumentType' : contextRun.candidate.context.HasType
          argumentRun.source' domain' :=
        argumentRun.check.hasType.defeqU_r
          contextRun.candidate.context.Ewf
          contextRun.candidate.context.Δwf.toCtx comparisonRun.isDefEqU
      have argumentType : env.HasType Us.length
          contextRun.candidate.context.vlctx.toCtx argumentRun.source'
          domain' := by
        simpa only [VContext.HasType, contextRun.venv_eq,
          contextRun.lparams_eq] using argumentType'
      have argument_tr : TrExprS env Us
          contextRun.candidate.context.vlctx argument argumentRun.source' := by
        simpa only [contextRun.venv_eq, contextRun.lparams_eq] using
          argumentRun.check.expr_tr
      have henv : VEnv.WF env := by
        simpa only [contextRun.venv_eq] using
          contextRun.candidate.context.Ewf
      have instantiatedBody_tr : TrExprS env Us
          contextRun.candidate.context.vlctx
          (body.instantiate1 argument) (body'.inst argumentRun.source') := by
        simpa only [Expr.instantiate1_eq] using
          body_tr.inst henv.ordered argumentType argument_tr
      obtain ⟨tailRun⟩ := ih (body'.inst argumentRun.source')
        instantiatedBody_tr
      exact ⟨{
        expectedInferred' := expectedInferred'
        expectedRun := by
          simpa only [ConstructorPreFamilyIndexSpineTrace.expectedCheck,
            contextRun.venv_eq, contextRun.lparams_eq] using expectedRun
        arguments' := argumentRun.source' :: tailRun.arguments'
        result' := tailRun.result'
        arguments_tr := .cons argument_tr tailRun.arguments_tr
        spine := .cons argumentType tailRun.spine }⟩

/-- Every successful operational spine trace has a verified interpretation;
the initial strict endpoint is selected by the trace's own root `checkType`. -/
theorem nonempty
    (contextRun : ConstructorContextRun env Us context)
    (trace : ConstructorPreFamilyIndexSpineTrace context expected arguments) :
    ∃ expected', Nonempty
      (ConstructorPreFamilyIndexSpineSemanticRun env Us context contextRun
        trace expected') := by
  obtain ⟨expectedRun⟩ := ConstructorCheckedExpr.Run.exists
    trace.expectedCheck contextRun.candidate
  have expected_tr : TrExprS env Us
      contextRun.candidate.context.vlctx expected expectedRun.source' := by
    simpa only [contextRun.venv_eq, contextRun.lparams_eq] using
      expectedRun.check.expr_tr
  exact ⟨expectedRun.source', nonempty_at contextRun trace _ expected_tr⟩

/-- Strict family translation fixes the expected endpoint chosen by an exact
pre-family index replay, even when the replay context contains a later prefix
of fresh locals. -/
theorem expected_eq_of_family
    {env : VEnv} {Us : List Name} {context : Context}
    {contextRun : ConstructorContextRun env Us context}
    {expected : Expr} {arguments : List Expr}
    {trace : ConstructorPreFamilyIndexSpineTrace context expected arguments}
    {expected' : VExpr}
    (run : ConstructorPreFamilyIndexSpineSemanticRun env Us context
      contextRun trace expected')
    {parameterΔ viewΔ : VLCtx} {expectedBase : VExpr} {n : Nat}
    (familyTr : TrExprS env Us parameterΔ expected expectedBase)
    (unique : TrExprS.IsUnique expected)
    (viewLift : VLCtx.FVLift' parameterΔ viewΔ 0
      (.skipN .refl n) 0)
    (viewDefEq : VLCtx.IsDefEq env Us.length
      contextRun.candidate.context.vlctx viewΔ)
    (viewUnique : TrExprS.IsUniqueCtx
      contextRun.candidate.context.vlctx viewΔ) :
    expected' = expectedBase.liftN n 0 := by
  have henv : VEnv.Ordered env := by
    simpa only [contextRun.venv_eq] using
      contextRun.candidate.context.Ewf.ordered
  have viewWF : VLCtx.WF env Us.length viewΔ :=
    (viewDefEq.symm henv).wf
  have familyAtView : TrExprS env Us viewΔ expected
      (expectedBase.liftN n 0) := by
    simpa only [VExpr.lift'_consN_skipN] using
      familyTr.weakFV' henv viewLift viewWF
  have retained : TrExprS env Us contextRun.candidate.context.vlctx
      expected expected' := run.expectedRun.expr_tr
  exact retained.unique' viewUnique unique familyAtView

/-- Transport the exact pre-family index judgment below an arbitrary later
prefix. This is the proved context weakening used when D4 places the same
spine beneath the remaining constructor fields. -/
theorem spine_weakPrefix
    {expected : Expr} {arguments : List Expr}
    {replay : ConstructorPreFamilyIndexSpineTrace context expected arguments}
    {expected' : VExpr}
    (run : ConstructorPreFamilyIndexSpineSemanticRun env Us context contextRun
      replay expected') (Bs : List VExpr) :
    env.SpineWF Us.length
      (Bs ++ contextRun.candidate.context.vlctx.toCtx)
      (expected'.liftN Bs.length 0)
      (run.arguments'.map fun argument =>
        argument.liftN Bs.length 0)
      (run.result'.liftN Bs.length 0) := by
  have henv : VEnv.WF env := by
    simpa only [contextRun.venv_eq] using contextRun.candidate.context.Ewf
  exact run.spine.weakN henv.ordered
    (Ctx.LiftN.zero (n := Bs.length)
      (Γ := contextRun.candidate.context.vlctx.toCtx) Bs)

end ConstructorPreFamilyIndexSpineSemanticRun

/-- Pre-family replay of the family-free pieces of one recursive field.  Π
domains are checked and introduced normally; the terminal family application
is replaced by an index-spine replay, so the absent family constant is never
looked up. -/
inductive ConstructorPreFamilyRecursiveTrace
    (stats : InductiveStats) (familyIdx : Nat) (familyIndices : Expr) :
    (context : Context) → (source : Expr) → (fuel : Nat) → Type where
  | forallE
      (context : Context) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (domainCheck : ConstructorCheckedExpr context domain)
      (ensureType : ConstructorEnsureTypeObservation context domain)
      (consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain))
      (annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain))
      (fresh : context.lctx.find? context.freshFVarId = none)
      (tail : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel) :
      ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices context
        (.forallE name domain body binderInfo) (fuel + 1)
  | target
      (context : Context) (source : Expr)
      (valid : isValidIndAppIdx stats source familyIdx = true)
      (spine : ConstructorPreFamilyIndexSpineTrace context familyIndices
        (source.getAppArgs.toList.drop stats.params.size)) :
      ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices context
        source (fuel + 1)

namespace ConstructorPreFamilyRecursiveTrace

def build (stats : InductiveStats) (familyIdx : Nat)
    (familyIndices : Expr) :
    (context : Context) → (source : Expr) → (fuel : Nat) →
    Except Exception
      (ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
        context source fuel)
  | _, _, 0 => throw .deepRecursion
  | context, .forallE name domain body binderInfo, fuel + 1 => do
      let domainCheck ← checkConstructorAlignedExpr context domain
      let ensureType ← observeConstructorEnsureType context domain
      let consumedCheck ← checkConstructorAlignedExpr context
        (consumeTypeAnnotations domain)
      let annotations ← observeCandidateIsDefEq context domain
        (consumeTypeAnnotations domain)
      if fresh : context.lctx.find? context.freshFVarId = none then
        let tail ← build stats familyIdx familyIndices
          (context.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain))
          (body.instantiate1 context.freshExpr) fuel
        pure <| .forallE context name domain body binderInfo domainCheck
          ensureType consumedCheck annotations fresh tail
      else
        throw <| .other
          "pre-family recursive replay reused a local identifier"
  | context, source, _ + 1 => do
      if valid : isValidIndAppIdx stats source familyIdx = true then
        let spine ← ConstructorPreFamilyIndexSpineTrace.build context
          familyIndices
          (source.getAppArgs.toList.drop stats.params.size)
        pure <| .target context source valid spine
      else
        throw <| .other
          "pre-family recursive replay reached a non-family target"

end ConstructorPreFamilyRecursiveTrace

theorem ConstructorPreFamilyRecursiveTrace.forallE_build_eq
    (domainCheck : ConstructorCheckedExpr context domain)
    (ensureType : ConstructorEnsureTypeObservation context domain)
    (consumedCheck : ConstructorCheckedExpr context
      (consumeTypeAnnotations domain))
    (annotations : CandidateIsDefEqObservation context domain
      (consumeTypeAnnotations domain))
    (fresh : context.lctx.find? context.freshFVarId = none)
    (tail : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      (context.pushLocalDecl name binderInfo
        (consumeTypeAnnotations domain))
      (body.instantiate1 context.freshExpr) fuel)
    (tailRun : ConstructorPreFamilyRecursiveTrace.build stats familyIdx
      familyIndices
      (context.pushLocalDecl name binderInfo
        (consumeTypeAnnotations domain))
      (body.instantiate1 context.freshExpr) fuel = .ok tail) :
    ConstructorPreFamilyRecursiveTrace.build stats familyIdx familyIndices
        context (.forallE name domain body binderInfo) (fuel + 1) =
      .ok (.forallE context name domain body binderInfo domainCheck ensureType
        consumedCheck annotations fresh tail) := by
  simp only [ConstructorPreFamilyRecursiveTrace.build]
  rw [domainCheck.check_eq, ensureType.observe_eq, consumedCheck.check_eq]
  simp only [Bind.bind, Except.bind]
  rw [annotations.observe_eq]
  simp only []
  rw [dif_pos fresh, tailRun]
  rfl

theorem ConstructorPreFamilyRecursiveTrace.target_build_eq
    (terminal : source.isForall = false)
    (valid : isValidIndAppIdx stats source familyIdx = true)
    (spine : ConstructorPreFamilyIndexSpineTrace context familyIndices
      (source.getAppArgs.toList.drop stats.params.size)) :
    ConstructorPreFamilyRecursiveTrace.build stats familyIdx familyIndices
        context source (fuel + 1) =
      .ok (.target context source valid spine) := by
  cases source <;> simp only [ConstructorPreFamilyRecursiveTrace.build]
  case forallE => simp [Expr.isForall] at terminal
  all_goals
    rw [dif_pos valid, spine.build_eq]
    rfl

/-!
### Verified pre-family recursive fields

Recursive outer-field locals are intentionally absent here. Nested Pi binders
inside the field are family-free, so they are checked, interpreted, and pushed
normally. The terminal family application contributes only its already-verified
index spine.
-/

/-- Componentwise verified interpretation of a recursive field replay. -/
inductive ConstructorPreFamilyRecursiveSemanticRun
    (env : VEnv) (Us : List Name)
    (stats : InductiveStats) (familyIdx : Nat) (familyIndices : Expr) :
    {context : Context} → {source : Expr} → {fuel : Nat} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices context
      source fuel → Type where
  | forallE
      {context : Context} {name : Name} {domain body : Expr}
      {binderInfo : BinderInfo} {fuel : Nat}
      {domainCheck : ConstructorCheckedExpr context domain}
      {ensureType : ConstructorEnsureTypeObservation context domain}
      {consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain)}
      {annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain)}
      {fresh : context.lctx.find? context.freshFVarId = none}
      {tailTrace : ConstructorPreFamilyRecursiveTrace stats familyIdx
        familyIndices
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel}
      {contextRun : ConstructorContextRun env Us context}
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (consumedRun : ConstructorCheckedExpr.Run consumedCheck
        contextRun.candidate)
      (ensureTypeRun : TypeChecker.EnsureTypeRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain ensureType.result
        domainRun.source')
      (annotationsRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain
        (consumeTypeAnnotations domain) domainRun.source'
        consumedRun.source')
      (consumedType : contextRun.candidate.context.IsType
        consumedRun.source')
      (tail : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
        familyIndices
        (contextRun.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain) fresh consumedRun.source'
          consumedRun.check.expr_tr consumedType)
        tailTrace) :
      ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
        familyIndices contextRun
        (.forallE context name domain body binderInfo domainCheck ensureType
          consumedCheck annotations fresh tailTrace)
  | target
      {context : Context} {source : Expr} {fuel : Nat}
      {valid : isValidIndAppIdx stats source familyIdx = true}
      {spineTrace : ConstructorPreFamilyIndexSpineTrace context familyIndices
        (source.getAppArgs.toList.drop stats.params.size)}
      {contextRun : ConstructorContextRun env Us context}
      (expected' : VExpr)
      (spine : ConstructorPreFamilyIndexSpineSemanticRun env Us context
        contextRun spineTrace expected') :
      ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
        familyIndices contextRun (.target context source valid spineTrace)

namespace ConstructorPreFamilyRecursiveSemanticRun

/-- Interpret every retained nested-binder and terminal-index operation in the
exact verified pre-family context. -/
theorem nonempty
    (contextRun : ConstructorContextRun env Us context)
    (trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel) :
    Nonempty (ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) := by
  induction trace with
  | forallE context name domain body binderInfo domainCheck ensureType
      consumedCheck annotations fresh tailTrace ih =>
      obtain ⟨domainRun⟩ := ConstructorCheckedExpr.Run.exists domainCheck
        contextRun.candidate
      obtain ⟨consumedRun⟩ := ConstructorCheckedExpr.Run.exists consumedCheck
        contextRun.candidate
      obtain ⟨ensureTypeRun⟩ :=
        TypeChecker.EnsureTypeRun.exists_ofConstructorStep
          ⟨context, domain, ensureType.result⟩ ensureType.valid
          contextRun.candidate domainRun.source' domainRun.check.expr_tr
      let annotationsRun := domainRun.isDefEq consumedRun annotations
      have consumedType : contextRun.candidate.context.IsType
          consumedRun.source' := by
        have annotationDef := annotationsRun.isDefEqU.of_l
          contextRun.candidate.context.Ewf
          contextRun.candidate.context.Δwf.toCtx ensureTypeRun.source_type
        exact ⟨ensureTypeRun.resultLevel', annotationDef.hasType.2⟩
      let tailContext := contextRun.pushLocalDecl name binderInfo
        (consumeTypeAnnotations domain) fresh consumedRun.source'
        consumedRun.check.expr_tr consumedType
      obtain ⟨tail⟩ := ih tailContext
      exact ⟨.forallE domainRun consumedRun ensureTypeRun annotationsRun
        consumedType tail⟩
  | @target traceFuel context source valid spineTrace =>
      obtain ⟨expected', ⟨spine⟩⟩ :=
        ConstructorPreFamilyIndexSpineSemanticRun.nonempty contextRun spineTrace
      exact ⟨@ConstructorPreFamilyRecursiveSemanticRun.target
        env Us stats familyIdx familyIndices traceFuel
        context source (traceFuel + 1) valid spineTrace contextRun expected' spine⟩

/-- The verified nested Π-binder telescope retained by the recursive field. -/
def binders
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) : List VExpr :=
  match run with
  | .forallE _ consumedRun _ _ _ tail => consumedRun.source' :: tail.binders
  | .target _ _ => []

/-- Translation selected for the analyzer-owned family-index telescope. -/
def expected'
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) : VExpr :=
  match run with
  | .forallE _ _ _ _ _ tail => tail.expected'
  | .target expected' _ => expected'

/-- Translated terminal recursive indices, in source order. -/
def indices'
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) : List VExpr :=
  match run with
  | .forallE _ _ _ _ _ tail => tail.indices'
  | .target _ spine => spine.arguments'

/-- Translated result type of the terminal recursive index application. -/
def result'
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) : VExpr :=
  match run with
  | .forallE _ _ _ _ _ tail => tail.result'
  | .target _ spine => spine.result'

/-- The retained recursive Π domains form a verified Theory telescope in the
exact pre-family context. -/
theorem onTel
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) :
    env.OnTel Us.length contextRun.candidate.context.vlctx.toCtx run.binders := by
  induction run with
  | @forallE context name domain body binderInfo fuel domainCheck ensureType
      consumedCheck annotations fresh tailTrace branchContextRun domainRun
      consumedRun ensureTypeRun annotationsRun consumedType tail ih =>
      constructor
      · simpa only [VContext.IsType, branchContextRun.venv_eq,
          branchContextRun.lparams_eq] using consumedType
      · simpa only [binders, ConstructorContextRun.pushLocalDecl,
          CandidateContextRun.pushLocalDecl_vlctx, VLCtx.toCtx] using ih
  | target => trivial

/-- The terminal recursive indices have the expected analyzer-owned family
index telescope, below all retained nested Π binders. -/
theorem spine
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) :
    env.SpineWF Us.length
      (run.binders.reverse ++ contextRun.candidate.context.vlctx.toCtx)
      run.expected' run.indices' run.result' := by
  induction run with
  | forallE domainRun consumedRun ensureTypeRun annotationsRun consumedType tail ih =>
      simpa only [binders, expected', indices', result', List.reverse_cons,
        List.singleton_append, List.append_assoc,
        ConstructorContextRun.pushLocalDecl,
        CandidateContextRun.pushLocalDecl_vlctx, VLCtx.toCtx] using ih
  | target expectedType spine =>
      simpa only [binders, expected', indices', result', List.reverse_nil,
        List.nil_append] using spine.spine

/-- Weaken the retained recursive Π telescope over a later prefix of omitted
outer recursive fields. -/
theorem onTel_weakPrefix
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) (Bs : List VExpr) :
    env.OnTel Us.length
      (Bs ++ contextRun.candidate.context.vlctx.toCtx)
      (VExpr.liftTelN Bs.length run.binders 0) := by
  have henv : VEnv.WF env := by
    simpa only [contextRun.venv_eq] using contextRun.candidate.context.Ewf
  exact run.onTel.weakN henv.ordered
    (Ctx.LiftN.zero (n := Bs.length)
      (Γ := contextRun.candidate.context.vlctx.toCtx) Bs)

/-- Weaken the terminal recursive index judgment below the same omitted outer
field prefix, preserving the nested Π-binder depths. -/
theorem spine_weakPrefix
    {context : Context} {source : Expr} {fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyRecursiveTrace stats familyIdx familyIndices
      context source fuel}
    (run : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) (Bs : List VExpr) :
    env.SpineWF Us.length
      ((VExpr.liftTelN Bs.length run.binders 0).reverse ++
        Bs ++ contextRun.candidate.context.vlctx.toCtx)
      (run.expected'.liftN Bs.length run.binders.length)
      (run.indices'.map fun index =>
        index.liftN Bs.length run.binders.length)
      (run.result'.liftN Bs.length run.binders.length) := by
  have henv : VEnv.WF env := by
    simpa only [contextRun.venv_eq] using contextRun.candidate.context.Ewf
  simpa only [List.append_assoc, Nat.add_zero] using
    run.spine.weakN henv.ordered
      (Ctx.LiftN.consTel run.binders
        (Ctx.LiftN.zero (n := Bs.length)
          (Γ := contextRun.candidate.context.vlctx.toCtx) Bs))

end ConstructorPreFamilyRecursiveSemanticRun

/-- Exact executable pre-family replay for one analyzer-owned constructor view.

`removed` contains precisely the validation FVars allocated for recursive
outer fields that were not inserted into the pre-family checker context.
`recursiveStarted` records whether such a field has been crossed; later
ordinary fields are admitted exactly when they are independent of `removed`. -/
inductive ConstructorPreFamilyViewTrace
    (stats : InductiveStats) (familyIdx : Nat) (familyIndices : Expr) :
    (context : Context) → (view : Expr) → (argIdx : Nat) →
      (removed : List FVarId) → (recursiveStarted : Bool) → Type where
  | parameter
      (context : Context) (argIdx : Nat) (removed : List FVarId)
      (recursiveStarted : Bool)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (parameter : Expr)
      (parameterAt : stats.params[argIdx]? = some parameter)
      (tail : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        context (body.instantiate1 parameter) (argIdx + 1) removed
        recursiveStarted) :
      ConstructorPreFamilyViewTrace stats familyIdx familyIndices context
        (.forallE name domain body binderInfo) argIdx removed recursiveStarted
  | ordinary
      (context : Context) (argIdx : Nat) (removed : List FVarId)
      (recursiveStarted : Bool)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (noParameter : stats.params[argIdx]? = none)
      (nonrecursive : hasIndOcc stats.indConsts domain = false)
      (independent : constructorIndependentOf domain removed = true)
      (domainCheck : ConstructorCheckedExpr context domain)
      (ensureType : ConstructorEnsureTypeObservation context domain)
      (consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain))
      (annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain))
      (fresh : context.lctx.find? context.freshFVarId = none)
      (tail : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) removed
        recursiveStarted) :
      ConstructorPreFamilyViewTrace stats familyIdx familyIndices context
        (.forallE name domain body binderInfo) argIdx removed recursiveStarted
  | recursive
      (context : Context) (argIdx : Nat) (removed : List FVarId)
      (recursiveStarted : Bool)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (noParameter : stats.params[argIdx]? = none)
      (isRecursive : hasIndOcc stats.indConsts domain = true)
      (independent : constructorIndependentOf domain removed = true)
      (field : ConstructorPreFamilyRecursiveTrace stats familyIdx
        familyIndices context domain context.fuel.inductiveFuel)
      (fresh : context.lctx.find? context.freshFVarId = none)
      (tail : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        context.advanceFresh (body.instantiate1 context.freshExpr)
        (argIdx + 1) (context.freshFVarId :: removed) true) :
      ConstructorPreFamilyViewTrace stats familyIdx familyIndices context
        (.forallE name domain body binderInfo) argIdx removed recursiveStarted
  | terminal
      (context : Context) (source : Expr) (argIdx : Nat)
      (removed : List FVarId) (recursiveStarted : Bool)
      (valid : isValidIndAppIdx stats source familyIdx = true)
      (independent : constructorIndependentOf source removed = true)
      (spine : ConstructorPreFamilyIndexSpineTrace context familyIndices
        (source.getAppArgs.toList.drop stats.params.size)) :
      ConstructorPreFamilyViewTrace stats familyIdx familyIndices context
        source argIdx removed recursiveStarted

namespace ConstructorPreFamilyViewTrace

def build (stats : InductiveStats) (familyIdx : Nat)
    (familyIndices : Expr) :
    (context : Context) → (view : Expr) → (argIdx : Nat) →
    (removed : List FVarId) → (recursiveStarted : Bool) → (fuel : Nat) →
    Except Exception
      (ConstructorPreFamilyViewTrace stats familyIdx familyIndices context view
        argIdx removed recursiveStarted)
  | _, _, _, _, _, 0 => throw .deepRecursion
  | context, .forallE name domain body binderInfo, argIdx, removed,
      recursiveStarted, fuel + 1 =>
      match parameterAt : stats.params[argIdx]? with
      | some param => do
          let tail ← build stats familyIdx familyIndices context
            (body.instantiate1 param) (argIdx + 1) removed
            recursiveStarted fuel
          pure <| .parameter context argIdx removed recursiveStarted name domain
            body binderInfo param parameterAt tail
      | none => do
          match recursive : hasIndOcc stats.indConsts domain with
          | false =>
              if independent : constructorIndependentOf domain removed = true then
                let domainCheck ← checkConstructorAlignedExpr context domain
                let ensureType ← observeConstructorEnsureType context domain
                let consumedCheck ← checkConstructorAlignedExpr context
                  (consumeTypeAnnotations domain)
                let annotations ← observeCandidateIsDefEq context domain
                  (consumeTypeAnnotations domain)
                if fresh : context.lctx.find? context.freshFVarId = none then
                  let tail ← build stats familyIdx familyIndices
                    (context.pushLocalDecl name binderInfo
                      (consumeTypeAnnotations domain))
                    (body.instantiate1 context.freshExpr) (argIdx + 1)
                    removed recursiveStarted fuel
                  pure <| .ordinary context argIdx removed recursiveStarted
                    name domain body binderInfo parameterAt recursive independent domainCheck
                    ensureType consumedCheck annotations fresh tail
                else
                  throw <| .other
                    "pre-family ordinary replay reused a local identifier"
              else
                throw <| .other
                  "constructor depends on an omitted recursive local"
          | true =>
              if independent : constructorIndependentOf domain removed = true then
                let field ← ConstructorPreFamilyRecursiveTrace.build stats
                  familyIdx familyIndices context domain
                  context.fuel.inductiveFuel
                if fresh : context.lctx.find? context.freshFVarId = none then
                  let tail ← build stats familyIdx familyIndices
                    context.advanceFresh
                    (body.instantiate1 context.freshExpr) (argIdx + 1)
                    (context.freshFVarId :: removed) true fuel
                  pure <| .recursive context argIdx removed recursiveStarted
                    name domain body binderInfo parameterAt recursive independent
                    field fresh tail
                else
                  throw <| .other
                    "pre-family recursive replay reused a local identifier"
              else
                throw <| .other
                  "constructor depends on an omitted recursive local"
  | context, source, argIdx, removed, recursiveStarted, _ + 1 => do
      if valid : isValidIndAppIdx stats source familyIdx = true then
        if independent : constructorIndependentOf source removed = true then
          let spine ← ConstructorPreFamilyIndexSpineTrace.build context
            familyIndices
            (source.getAppArgs.toList.drop stats.params.size)
          pure <| .terminal context source argIdx removed recursiveStarted valid
            independent spine
        else
          throw <| .other
            "constructor result depends on an omitted recursive local"
      else
        throw <| .other
          "pre-family replay reached a non-family constructor result"

end ConstructorPreFamilyViewTrace

theorem ConstructorPreFamilyViewTrace.terminal_build_eq
    (terminal : source.isForall = false)
    (valid : isValidIndAppIdx stats source familyIdx = true)
    (independent : constructorIndependentOf source removed = true)
    (spine : ConstructorPreFamilyIndexSpineTrace context familyIndices
      (source.getAppArgs.toList.drop stats.params.size)) :
    ConstructorPreFamilyViewTrace.build stats familyIdx familyIndices
        context source argIdx removed recursiveStarted (fuel + 1) =
      .ok (.terminal context source argIdx removed recursiveStarted valid
        independent spine) := by
  cases source <;> simp only [ConstructorPreFamilyViewTrace.build]
  case forallE => simp [Expr.isForall] at terminal
  all_goals
    rw [dif_pos valid, dif_pos independent, spine.build_eq]
    rfl

/-!
### Verified pre-family constructor views

This interpretation follows the exact executable D3 trace. Ordinary fields
are checked and pushed in the pre-family context, recursive outer fields are
omitted while their family-free nested binders and indices are retained, and
the terminal result contributes its verified index spine.
-/

/-- Verified meaning of every family-free operation retained by one exact
pre-family constructor-view replay. -/
inductive ConstructorPreFamilyViewSemanticRun
    (env : VEnv) (Us : List Name)
    (stats : InductiveStats) (familyIdx : Nat) (familyIndices : Expr) :
    {context : Context} → {view : Expr} → {argIdx : Nat} →
    {removed : List FVarId} → {recursiveStarted : Bool} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorPreFamilyViewTrace stats familyIdx familyIndices context view
      argIdx removed recursiveStarted → Type where
  | parameter
      {context : Context} {argIdx : Nat} {removed : List FVarId}
      {recursiveStarted : Bool}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {parameter : Expr}
      {parameterAt : stats.params[argIdx]? = some parameter}
      {tailTrace : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        context (body.instantiate1 parameter) (argIdx + 1) removed
        recursiveStarted}
      {contextRun : ConstructorContextRun env Us context}
      (tail : ConstructorPreFamilyViewSemanticRun env Us stats familyIdx
        familyIndices contextRun tailTrace) :
      ConstructorPreFamilyViewSemanticRun env Us stats familyIdx familyIndices
        contextRun
        (.parameter context argIdx removed recursiveStarted name domain body
          binderInfo parameter parameterAt tailTrace)
  | ordinary
      {context : Context} {argIdx : Nat} {removed : List FVarId}
      {recursiveStarted : Bool}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {noParameter : stats.params[argIdx]? = none}
      {nonrecursive : hasIndOcc stats.indConsts domain = false}
      {independent : constructorIndependentOf domain removed = true}
      {domainCheck : ConstructorCheckedExpr context domain}
      {ensureType : ConstructorEnsureTypeObservation context domain}
      {consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain)}
      {annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain)}
      {fresh : context.lctx.find? context.freshFVarId = none}
      {tailTrace : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) removed
        recursiveStarted}
      {contextRun : ConstructorContextRun env Us context}
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (consumedRun : ConstructorCheckedExpr.Run consumedCheck
        contextRun.candidate)
      (ensureTypeRun : TypeChecker.EnsureTypeRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain ensureType.result
        domainRun.source')
      (annotationsRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain
        (consumeTypeAnnotations domain) domainRun.source'
        consumedRun.source')
      (consumedType : contextRun.candidate.context.IsType
        consumedRun.source')
      (tail : ConstructorPreFamilyViewSemanticRun env Us stats familyIdx
        familyIndices
        (contextRun.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain) fresh consumedRun.source'
          consumedRun.check.expr_tr consumedType)
        tailTrace) :
      ConstructorPreFamilyViewSemanticRun env Us stats familyIdx familyIndices
        contextRun
        (.ordinary context argIdx removed recursiveStarted name domain body
          binderInfo noParameter nonrecursive independent domainCheck ensureType
          consumedCheck annotations fresh tailTrace)
  | recursive
      {context : Context} {argIdx : Nat} {removed : List FVarId}
      {recursiveStarted : Bool}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {noParameter : stats.params[argIdx]? = none}
      {isRecursive : hasIndOcc stats.indConsts domain = true}
      {independent : constructorIndependentOf domain removed = true}
      {fieldTrace : ConstructorPreFamilyRecursiveTrace stats familyIdx
        familyIndices context domain context.fuel.inductiveFuel}
      {fresh : context.lctx.find? context.freshFVarId = none}
      {tailTrace : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        context.advanceFresh (body.instantiate1 context.freshExpr)
        (argIdx + 1) (context.freshFVarId :: removed) true}
      {contextRun : ConstructorContextRun env Us context}
      (field : ConstructorPreFamilyRecursiveSemanticRun env Us stats familyIdx
        familyIndices contextRun fieldTrace)
      (tail : ConstructorPreFamilyViewSemanticRun env Us stats familyIdx
        familyIndices contextRun.advanceFresh tailTrace) :
      ConstructorPreFamilyViewSemanticRun env Us stats familyIdx familyIndices
        contextRun
        (.recursive context argIdx removed recursiveStarted name domain body
          binderInfo noParameter isRecursive independent fieldTrace fresh
          tailTrace)
  | terminal
      {context : Context} {source : Expr} {argIdx : Nat}
      {removed : List FVarId} {recursiveStarted : Bool}
      {valid : isValidIndAppIdx stats source familyIdx = true}
      {independent : constructorIndependentOf source removed = true}
      {spineTrace : ConstructorPreFamilyIndexSpineTrace context familyIndices
        (source.getAppArgs.toList.drop stats.params.size)}
      {contextRun : ConstructorContextRun env Us context}
      (expected' : VExpr)
      (spine : ConstructorPreFamilyIndexSpineSemanticRun env Us context
        contextRun spineTrace expected') :
      ConstructorPreFamilyViewSemanticRun env Us stats familyIdx familyIndices
        contextRun
        (.terminal context source argIdx removed recursiveStarted valid
          independent spineTrace)

namespace ConstructorPreFamilyViewSemanticRun

/-- Interpret every exact family-free checker observation in a successful
constructor-view replay. -/
theorem nonempty
    (contextRun : ConstructorContextRun env Us context)
    (trace : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
      context view argIdx removed recursiveStarted) :
    Nonempty (ConstructorPreFamilyViewSemanticRun env Us stats familyIdx
      familyIndices contextRun trace) := by
  induction trace with
  | parameter context argIdx removed recursiveStarted name domain body
      binderInfo parameter parameterAt tailTrace ih =>
      obtain ⟨tail⟩ := ih contextRun
      exact ⟨.parameter tail⟩
  | ordinary context argIdx removed recursiveStarted name domain body
      binderInfo noParameter nonrecursive independent domainCheck ensureType
      consumedCheck annotations fresh tailTrace ih =>
      obtain ⟨domainRun⟩ := ConstructorCheckedExpr.Run.exists domainCheck
        contextRun.candidate
      obtain ⟨consumedRun⟩ := ConstructorCheckedExpr.Run.exists consumedCheck
        contextRun.candidate
      obtain ⟨ensureTypeRun⟩ :=
        TypeChecker.EnsureTypeRun.exists_ofConstructorStep
          ⟨context, domain, ensureType.result⟩ ensureType.valid
          contextRun.candidate domainRun.source' domainRun.check.expr_tr
      let annotationsRun := domainRun.isDefEq consumedRun annotations
      have consumedType : contextRun.candidate.context.IsType
          consumedRun.source' := by
        have annotationDef := annotationsRun.isDefEqU.of_l
          contextRun.candidate.context.Ewf
          contextRun.candidate.context.Δwf.toCtx ensureTypeRun.source_type
        exact ⟨ensureTypeRun.resultLevel', annotationDef.hasType.2⟩
      let tailContext := contextRun.pushLocalDecl name binderInfo
        (consumeTypeAnnotations domain) fresh consumedRun.source'
        consumedRun.check.expr_tr consumedType
      obtain ⟨tail⟩ := ih tailContext
      exact ⟨.ordinary domainRun consumedRun ensureTypeRun annotationsRun
        consumedType tail⟩
  | recursive context argIdx removed recursiveStarted name domain body
      binderInfo noParameter isRecursive independent fieldTrace fresh
      tailTrace tailIH =>
      obtain ⟨field⟩ :=
        ConstructorPreFamilyRecursiveSemanticRun.nonempty contextRun fieldTrace
      obtain ⟨tail⟩ := tailIH contextRun.advanceFresh
      exact ⟨.recursive field tail⟩
  | terminal context source argIdx removed recursiveStarted valid independent
      spineTrace =>
      obtain ⟨expected', ⟨spine⟩⟩ :=
        ConstructorPreFamilyIndexSpineSemanticRun.nonempty contextRun spineTrace
      exact ⟨.terminal expected' spine⟩

end ConstructorPreFamilyViewSemanticRun

private theorem drop_eq_cons_of_getElem?_eq_some
    {values : List α} {index : Nat} {value : α}
    (atIndex : values[index]? = some value) :
    values.drop index = value :: values.drop (index + 1) := by
  induction values generalizing index with
  | nil => simp at atIndex
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at atIndex
          simp [atIndex]
      | succ index =>
          simp at atIndex ⊢
          simpa [Nat.add_assoc, Nat.add_comm 1] using ih atIndex

private theorem eq_length_of_getElem?_eq_none
    {values : List α} {index : Nat}
    (atIndex : values[index]? = none)
    (indexLe : index ≤ values.length) :
    index = values.length := by
  induction values generalizing index with
  | nil => simp_all
  | cons head tail ih =>
      cases index with
      | zero => simp at atIndex
      | succ index =>
          simp at atIndex
          simp only [List.length_cons, Nat.succ_le_succ_iff] at indexLe
          have indexEq : index = tail.length :=
            Nat.le_antisymm indexLe atIndex
          simp [indexEq]

/-- The exact D3 suffix after consuming every validator-owned parameter.
The context is unchanged because parameter branches instantiate existing
locals rather than pushing constructor fields. -/
structure ConstructorPreFamilyParameterSuffix
    {env : VEnv} {Us : List Name}
    {stats : InductiveStats} {familyIndices : Expr}
    {context : Context}
    {removed : List FVarId} {recursiveStarted : Bool}
    {contextRun : ConstructorContextRun env Us context}
    (rest : Expr) where
  trace : ConstructorPreFamilyViewTrace stats 0 familyIndices
    context rest stats.params.size removed recursiveStarted
  semantic : ConstructorPreFamilyViewSemanticRun env Us stats 0
    familyIndices contextRun trace

namespace ConstructorPreFamilyViewSemanticRun

/-- Strip the exact validator-owned parameter prefix from a verified D3
view trace.  The successful executable instantiation equation excludes an
early terminal, while the indexed parameter lookups exclude an early field. -/
theorem afterParameters
    {env : VEnv} {Us : List Name}
    {stats : InductiveStats} {familyIndices : Expr}
    {familyName : Name} {levels : List Level}
    {context : Context} {view rest : Expr} {argIdx : Nat}
    {removed : List FVarId} {recursiveStarted : Bool}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorPreFamilyViewTrace stats 0 familyIndices
      context view argIdx removed recursiveStarted}
    (semantic : ConstructorPreFamilyViewSemanticRun env Us stats 0
      familyIndices contextRun trace)
    (indConsts : stats.indConsts = #[.const familyName levels])
    (argIdxLe : argIdx ≤ stats.params.size)
    (instantiation : instantiateFamilyParameters view
      (stats.params.toList.drop argIdx) = .ok rest) :
    Nonempty (ConstructorPreFamilyParameterSuffix
      (env := env) (Us := Us) (stats := stats)
      (familyIndices := familyIndices) (context := context)
      (removed := removed) (recursiveStarted := recursiveStarted)
      (contextRun := contextRun) rest) := by
  induction semantic generalizing rest with
  | @parameter context argIdx removed recursiveStarted name domain body
      binderInfo parameter parameterAt tailTrace contextRun tail ih =>
      have atList : stats.params.toList[argIdx]? = some parameter := by
        simpa only [← Array.getElem?_toList] using parameterAt
      have dropped := drop_eq_cons_of_getElem?_eq_some atList
      rw [dropped] at instantiation
      simp only [instantiateFamilyParameters] at instantiation
      have argIdxLt : argIdx < stats.params.size := by
        by_contra notLt
        have argIdxEq : argIdx = stats.params.size := by omega
        subst argIdx
        simp at parameterAt
      exact ih (by omega) instantiation
  | @ordinary context argIdx removed recursiveStarted name domain body
      binderInfo noParameter nonrecursive independent domainCheck ensureType
      consumedCheck annotations fresh tailTrace contextRun domainRun consumedRun
      ensureTypeRun annotationsRun consumedType tail =>
      have noParameterList : stats.params.toList[argIdx]? = none := by
        simpa only [← Array.getElem?_toList] using noParameter
      have argIdxEq : argIdx = stats.params.toList.length :=
        eq_length_of_getElem?_eq_none noParameterList (by simpa using argIdxLe)
      have sizeEq : stats.params.toList.length = stats.params.size := by simp
      rw [sizeEq] at argIdxEq
      subst argIdx
      have dropEq : stats.params.toList.drop stats.params.size = [] := by
        simp
      rw [dropEq] at instantiation
      have viewEq : (.forallE name domain body binderInfo) = rest :=
        Except.ok.inj (by
          change Except.ok (.forallE name domain body binderInfo) =
            Except.ok rest at instantiation
          exact instantiation)
      subst rest
      let suffixTrace := ConstructorPreFamilyViewTrace.ordinary context
        stats.params.size removed recursiveStarted name domain body binderInfo
        noParameter nonrecursive independent domainCheck ensureType consumedCheck
        annotations fresh tailTrace
      exact ⟨⟨suffixTrace,
        ConstructorPreFamilyViewSemanticRun.ordinary domainRun consumedRun
          ensureTypeRun annotationsRun consumedType tail⟩⟩
  | @recursive context argIdx removed recursiveStarted name domain body
      binderInfo noParameter isRecursive independent fieldTrace fresh tailTrace
      contextRun field tail =>
      have noParameterList : stats.params.toList[argIdx]? = none := by
        simpa only [← Array.getElem?_toList] using noParameter
      have argIdxEq : argIdx = stats.params.toList.length :=
        eq_length_of_getElem?_eq_none noParameterList (by simpa using argIdxLe)
      have sizeEq : stats.params.toList.length = stats.params.size := by simp
      rw [sizeEq] at argIdxEq
      subst argIdx
      have dropEq : stats.params.toList.drop stats.params.size = [] := by
        simp
      rw [dropEq] at instantiation
      have viewEq : (.forallE name domain body binderInfo) = rest :=
        Except.ok.inj (by
          change Except.ok (.forallE name domain body binderInfo) =
            Except.ok rest at instantiation
          exact instantiation)
      subst rest
      let suffixTrace := ConstructorPreFamilyViewTrace.recursive context
        stats.params.size removed recursiveStarted name domain body binderInfo
        noParameter isRecursive independent fieldTrace fresh tailTrace
      exact ⟨⟨suffixTrace,
        ConstructorPreFamilyViewSemanticRun.recursive field tail⟩⟩
  | @terminal context source argIdx removed recursiveStarted valid independent
      spineTrace contextRun expected spine =>
      by_cases argIdxEq : argIdx = stats.params.size
      · subst argIdx
        have dropEq : stats.params.toList.drop stats.params.size = [] := by
          simp
        rw [dropEq] at instantiation
        have viewEq : source = rest :=
          Except.ok.inj (by
            change Except.ok source = Except.ok rest at instantiation
            exact instantiation)
        subst rest
        let suffixTrace := ConstructorPreFamilyViewTrace.terminal context source
          stats.params.size removed recursiveStarted valid independent
          spineTrace
        exact ⟨⟨suffixTrace,
          ConstructorPreFamilyViewSemanticRun.terminal expected spine⟩⟩
      · have argIdxLt : argIdx < stats.params.size := by omega
        obtain ⟨parameter, parameterAt⟩ :
            ∃ parameter, stats.params.toList[argIdx]? = some parameter := by
          have listLt : argIdx < stats.params.toList.length := by
            simpa using argIdxLt
          exact ⟨stats.params.toList[argIdx], by
            simp only [List.getElem?_eq_getElem listLt]⟩
        have dropped := drop_eq_cons_of_getElem?_eq_some parameterAt
        rw [dropped] at instantiation
        cases source <;>
          simp only [instantiateFamilyParameters] at instantiation
        case forallE binderName binderType body binderInfo =>
          unfold isValidIndAppIdx at valid
          rw [indConsts] at valid
          simp only [Expr.withApp_eq, Expr.getAppFn] at valid
          cases headEq :
              ((.forallE binderName binderType body binderInfo : Expr) ==
                .const familyName levels) with
          | false => simp [headEq] at valid
          | true =>
              change Expr.eqv
                (.forallE binderName binderType body binderInfo)
                (.const familyName levels) = true at headEq
              rw [Expr.eqv_eq] at headEq
              simp [Expr.eqv'] at headEq
        all_goals exact nomatch instantiation

end ConstructorPreFamilyViewSemanticRun

/-- The exact D2 suffix after consuming every validator-owned parameter.
Both the executable alignment and its verified semantic interpretation are
retained at the first ordinary field or terminal result. -/
structure ConstructorViewParameterSuffix
    {env : VEnv} {Us : List Name} {whnfFuel : Nat}
    {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
    {ctor : Name} {context : Context}
    {contextRun : ConstructorContextRun env Us context}
    (rest : Expr) where
  source : Expr
  fuel : Nat
  trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
    context source stats.params.size fuel
  alignment : ConstructorViewAlignmentTrace trace rest
  semantic : ConstructorViewSemanticRun env Us whnfFuel contextRun trace rest

namespace ConstructorViewSemanticRun

/-- Strip the exact parameter prefix shared by D2's validation trace and
analyzer view alignment. Parameter lookups exclude an early ordinary field;
the alignment's retained non-Pi fact excludes an early terminal. -/
theorem afterParameters
    {env : VEnv} {Us : List Name} {whnfFuel : Nat}
    {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
    {ctor : Name} {context : Context} {source view rest : Expr}
    {argIdx fuel : Nat}
    {contextRun : ConstructorContextRun env Us context}
    {trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel}
    (alignment : ConstructorViewAlignmentTrace trace view)
    (semantic : ConstructorViewSemanticRun env Us whnfFuel contextRun trace
      view)
    (argIdxLe : argIdx ≤ stats.params.size)
    (instantiation : instantiateFamilyParameters view
      (stats.params.toList.drop argIdx) = .ok rest) :
    ∃ suffix : ConstructorViewParameterSuffix
      (env := env) (Us := Us) (whnfFuel := whnfFuel)
      (stats := stats) (isUnsafe := isUnsafe) (familyIdx := familyIdx)
      (ctor := ctor) (context := context) (contextRun := contextRun) rest,
      suffix.trace.universeSemantics = trace.universeSemantics := by
  induction trace generalizing view rest with
  | parameter context fuel argIdx name domain body binderInfo param
      parameterType parameterAt parameterTypeRun validationDefEq tailTrace ih =>
      cases alignment with
      | parameter domainCheck viewDomainCheck parameterTypeCheck
          parameterShape parameterPresent _ tailAlignment =>
        cases semantic with
        | parameter domainRun viewDomainRun parameterTypeSemantic validationRun
            tail =>
          have atList : stats.params.toList[argIdx]? = some param := by
            simpa only [← Array.getElem?_toList] using parameterAt
          have dropped := drop_eq_cons_of_getElem?_eq_some atList
          rw [dropped] at instantiation
          simp only [instantiateFamilyParameters] at instantiation
          obtain ⟨suffix, suffixUniverse⟩ := ih tailAlignment tail (by
            have argIdxLt : argIdx < stats.params.size := by
              by_contra notLt
              have argIdxEq : argIdx = stats.params.size := by omega
              subst argIdx
              simp at parameterAt
            omega) instantiation
          exact ⟨suffix, by
            simpa only [ConstructorTypeValidationTrace.universeSemantics]
              using suffixUniverse⟩
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureTypeStep universeTrace positivityTrace tailTrace ih =>
      cases alignment with
      | @ordinary _ _ viewDomain _ _ _ _ _ _ _ _ _ _ _ _ _ viewName
          viewBody viewBinderInfo domainCheck viewDomainCheck viewEquality
          consumedCheck _ positivityAlignment fresh annotations _
          tailAlignment =>
        cases semantic with
        | ordinary domainRun viewDomainRun viewEqualityRun consumedRun
            ensureTypeRun positivity annotationsRun consumedType tail =>
          have noParameterList : stats.params.toList[argIdx]? = none := by
            simpa only [← Array.getElem?_toList] using noParameter
          have argIdxEq : argIdx = stats.params.toList.length :=
            eq_length_of_getElem?_eq_none noParameterList
              (by simpa using argIdxLe)
          have sizeEq : stats.params.toList.length = stats.params.size := by
            simp
          rw [sizeEq] at argIdxEq
          subst argIdx
          have dropEq : stats.params.toList.drop stats.params.size = [] := by
            simp
          rw [dropEq] at instantiation
          injection instantiation with restEq
          subst rest
          let suffixTrace := ConstructorTypeValidationTrace.ordinary context
            fuel stats.params.size name domain body binderInfo sortResult
            noParameter ensureTypeStep universeTrace positivityTrace tailTrace
          have suffixAlignment : ConstructorViewAlignmentTrace suffixTrace
              (.forallE viewName viewDomain viewBody viewBinderInfo) :=
            ConstructorViewAlignmentTrace.ordinary domainCheck
              viewDomainCheck viewEquality consumedCheck positivityTrace
              positivityAlignment fresh annotations tailTrace tailAlignment
          have suffixSemantic : ConstructorViewSemanticRun env Us whnfFuel
              contextRun suffixTrace
                (.forallE viewName viewDomain viewBody viewBinderInfo) :=
            ConstructorViewSemanticRun.ordinary
              (viewEquality := viewEquality) domainRun viewDomainRun
              viewEqualityRun consumedRun ensureTypeRun positivity
              annotationsRun consumedType tail
          exact ⟨⟨_, fuel + 1, suffixTrace, suffixAlignment,
            suffixSemantic⟩, rfl⟩
  | terminal context source fuel argIdx sourceTerminal sourceValid =>
      cases alignment with
      | terminal sourceCheck viewCheck viewTerminal viewValid =>
        cases semantic with
        | terminal sourceRun viewRun =>
          by_cases argIdxEq : argIdx = stats.params.size
          · subst argIdx
            have dropEq : stats.params.toList.drop stats.params.size = [] := by
              simp
            rw [dropEq] at instantiation
            have viewEq : view = rest := Except.ok.inj instantiation
            subst rest
            let suffixTrace : ConstructorTypeValidationTrace stats isUnsafe
                familyIdx ctor context source stats.params.size (fuel + 1) :=
              ConstructorTypeValidationTrace.terminal context source fuel
                stats.params.size sourceTerminal sourceValid
            have suffixAlignment : ConstructorViewAlignmentTrace suffixTrace
                view :=
              ConstructorViewAlignmentTrace.terminal sourceCheck viewCheck
                viewTerminal viewValid
            have suffixSemantic : ConstructorViewSemanticRun env Us whnfFuel
                contextRun suffixTrace view :=
              ConstructorViewSemanticRun.terminal (isUnsafe := isUnsafe)
                (ctor := ctor) sourceRun viewRun
            exact ⟨⟨source, fuel + 1, suffixTrace, suffixAlignment,
              suffixSemantic⟩, rfl⟩
          · have argIdxLt : argIdx < stats.params.size := by omega
            obtain ⟨parameter, parameterAt⟩ :
                ∃ parameter, stats.params.toList[argIdx]? = some parameter := by
              have listLt : argIdx < stats.params.toList.length := by
                simpa using argIdxLt
              exact ⟨stats.params.toList[argIdx], by
                simp only [List.getElem?_eq_getElem listLt]⟩
            have dropped := drop_eq_cons_of_getElem?_eq_some parameterAt
            rw [dropped] at instantiation
            cases view <;>
              simp_all [instantiateFamilyParameters, Expr.isForall]

end ConstructorViewSemanticRun

private def candidateForallDepth : Expr → Nat
  | .forallE _ _ body _ => candidateForallDepth body + 1
  | _ => 0

private theorem candidateForallDepth_le_instantiate1'
    (expression argument : Expr) (depth : Nat) :
    candidateForallDepth expression ≤
      candidateForallDepth (expression.instantiate1' argument depth) := by
  induction expression generalizing depth <;>
    simp [candidateForallDepth, Expr.instantiate1', *]

private theorem candidateForallDepth_abstract1
    (expression : Expr) (id : FVarId) (depth : Nat) :
    candidateForallDepth (Expr.abstract1 id expression depth) =
      candidateForallDepth expression := by
  induction expression generalizing depth <;>
    simp [candidateForallDepth, Expr.abstract1, *]
  split <;> rfl

private theorem candidateForallDepth_abstractList
    (expression : Expr) (ids : List FVarId) (depth : Nat) :
    candidateForallDepth (Expr.abstractList expression ids depth) =
      candidateForallDepth expression := by
  induction ids generalizing expression with
  | nil => rfl
  | cons id ids ih =>
      simp only [Expr.abstractList, ih, candidateForallDepth_abstract1]

private theorem candidateForallDepth_abstract
    (expression : Expr) (ids : List FVarId) :
    candidateForallDepth (expression.abstract ⟨ids.map Expr.fvar⟩) =
      candidateForallDepth expression := by
  rw [Expr.abstract_eq]
  exact candidateForallDepth_abstractList expression ids 0

private theorem candidateView_forallDepth
    (trace : CandidateExprTrace context source) :
    trace.spineLength ≤ candidateForallDepth trace.view := by
  induction trace with
  | terminal => exact Nat.zero_le _
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate domainIH bodyIH =>
      simp only [CandidateExprTrace.view, candidateForallDepth,
        CandidateExprTrace.spineLength]
      rw [show #[context.freshExpr] =
        ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl,
        candidateForallDepth_abstract]
      omega

private theorem instantiateFamilyParameters_exists_of_forallDepth
    (length : parameters.length ≤ candidateForallDepth source) :
    ∃ rest, instantiateFamilyParameters source parameters = .ok rest := by
  induction parameters generalizing source with
  | nil => exact ⟨source, rfl⟩
  | cons parameter parameters ih =>
      cases source <;> simp [candidateForallDepth] at length
      case forallE name domain body binderInfo =>
        have bodyLength : parameters.length ≤ candidateForallDepth
            (body.instantiate1 parameter) := by
          rw [Expr.instantiate1_eq]
          exact Nat.le_trans
            (by omega : parameters.length ≤ candidateForallDepth body)
            (candidateForallDepth_le_instantiate1' body parameter 0)
        obtain ⟨rest, restEq⟩ := ih bodyLength
        exact ⟨rest, restEq⟩

/-- A reconstructed candidate view can instantiate any parameter list no
longer than its retained main Pi spine.  This is only a syntactic success
fact; the exact Theory endpoint is supplied separately by strict translation. -/
theorem CandidateExprTrace.instantiateViewParameters
    (trace : CandidateExprTrace context source)
    (parameters : List Expr)
    (length : parameters.length ≤ trace.spineLength) :
    ∃ rest, instantiateFamilyParameters trace.view parameters = .ok rest := by
  apply instantiateFamilyParameters_exists_of_forallDepth
  exact Nat.le_trans length (candidateView_forallDepth trace)

namespace ConstructorPreFamilyViewSemanticRun

/-- Weaken an exact ordinary-field type over any later field prefix. -/
theorem ordinaryType_weakPrefix
    (contextRun : ConstructorContextRun env Us context)
    {fieldType : VExpr}
    (fieldTypeWF : contextRun.candidate.context.IsType fieldType)
    (Bs : List VExpr) :
    env.IsType Us.length
      (Bs ++ contextRun.candidate.context.vlctx.toCtx)
      (fieldType.liftN Bs.length 0) := by
  have henv : VEnv.WF env := by
    simpa only [contextRun.venv_eq] using contextRun.candidate.context.Ewf
  have fieldTypeWF' : env.IsType Us.length
      contextRun.candidate.context.vlctx.toCtx fieldType := by
    simpa only [VContext.IsType, contextRun.venv_eq,
      contextRun.lparams_eq] using fieldTypeWF
  exact fieldTypeWF'.weakN henv.ordered
    (Ctx.LiftN.zero (n := Bs.length)
      (Γ := contextRun.candidate.context.vlctx.toCtx) Bs)

end ConstructorPreFamilyViewSemanticRun

/-- Source-ordered D3 traces for the exact dependent constructor candidate
list selected by the producer. -/
inductive ConstructorPreFamilyListTrace
    (stats : InductiveStats) (familyIdx : Nat) (familyIndices : Expr)
    (context : Context) :
    {constructors : List Constructor} →
    AddInductive.CandidateList AddInductive.CandidateConstructor constructors →
      Type where
  | nil : ConstructorPreFamilyListTrace stats familyIdx familyIndices context
      .nil
  | cons
      (head : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        context candidate.type.view 0 [] false)
      (tail : ConstructorPreFamilyListTrace stats familyIdx familyIndices
        context candidates) :
      ConstructorPreFamilyListTrace stats familyIdx familyIndices context
        (.cons candidate candidates)

namespace ConstructorPreFamilyListTrace

def build (stats : InductiveStats) (familyIdx : Nat)
    (familyIndices : Expr) (context : Context) :
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) →
    Except Exception
      (ConstructorPreFamilyListTrace stats familyIdx familyIndices context
        candidates)
  | .nil => pure .nil
  | .cons head tail => do
      let headTrace ← ConstructorPreFamilyViewTrace.build stats familyIdx
        familyIndices context head.type.view 0 [] false
        context.fuel.inductiveFuel
      let tailTrace ← build stats familyIdx familyIndices context tail
      pure <| .cons headTrace tailTrace

end ConstructorPreFamilyListTrace

theorem ConstructorPreFamilyListTrace.cons_build_eq
    (head : ConstructorPreFamilyViewTrace stats familyIdx familyIndices context
      candidate.type.view 0 [] false)
    (headRun : ConstructorPreFamilyViewTrace.build stats familyIdx
      familyIndices context candidate.type.view 0 [] false
      context.fuel.inductiveFuel = .ok head)
    (tail : ConstructorPreFamilyListTrace stats familyIdx familyIndices context
      candidates)
    (tailRun : ConstructorPreFamilyListTrace.build stats familyIdx
      familyIndices context candidates = .ok tail) :
    ConstructorPreFamilyListTrace.build stats familyIdx familyIndices context
        (.cons candidate candidates) = .ok (.cons head tail) := by
  simp only [ConstructorPreFamilyListTrace.build]
  rw [headRun]
  simp only [Bind.bind, Except.bind]
  rw [tailRun]
  rfl

/-- Source-ordered verified pre-family meaning for every analyzer-owned
constructor candidate selected by the executable D3 gate. -/
inductive ConstructorPreFamilyListSemanticRun
    (env : VEnv) (Us : List Name)
    (stats : InductiveStats) (familyIdx : Nat) (familyIndices : Expr)
    (context : Context) (contextRun : ConstructorContextRun env Us context) :
    {constructors : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors} →
    ConstructorPreFamilyListTrace stats familyIdx familyIndices context
      candidates → Type where
  | nil : ConstructorPreFamilyListSemanticRun env Us stats familyIdx
      familyIndices context contextRun (.nil)
  | cons
      {candidate : AddInductive.CandidateConstructor constructor}
      {candidates : AddInductive.CandidateList
        AddInductive.CandidateConstructor constructors}
      {headTrace : ConstructorPreFamilyViewTrace stats familyIdx familyIndices
        context candidate.type.view 0 [] false}
      {tailTrace : ConstructorPreFamilyListTrace stats familyIdx familyIndices
        context candidates}
      (head : ConstructorPreFamilyViewSemanticRun env Us stats familyIdx
        familyIndices contextRun headTrace)
      (tail : ConstructorPreFamilyListSemanticRun env Us stats familyIdx
        familyIndices context contextRun tailTrace) :
      ConstructorPreFamilyListSemanticRun env Us stats familyIdx
        familyIndices context contextRun (.cons headTrace tailTrace)

namespace ConstructorPreFamilyListSemanticRun

/-- Interpret every constructor position retained by a successful executable
D3 list trace in the same verified pre-family context. -/
theorem nonempty
    (contextRun : ConstructorContextRun env Us context)
    (trace : ConstructorPreFamilyListTrace stats familyIdx familyIndices
      context candidates) :
    Nonempty (ConstructorPreFamilyListSemanticRun env Us stats familyIdx
      familyIndices context contextRun trace) := by
  induction trace with
  | nil => exact ⟨.nil⟩
  | cons headTrace tailTrace ih =>
      obtain ⟨head⟩ := ConstructorPreFamilyViewSemanticRun.nonempty contextRun
        headTrace
      obtain ⟨tail⟩ := ih
      exact ⟨.cons head tail⟩

end ConstructorPreFamilyListSemanticRun

/-- Exact output of the executable D3 gate. -/
structure ConstructorPreFamilySafetyTrace
    (stats : InductiveStats) (familyView : Expr)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors)
    (context : Context) where
  translationUnique :
    (theoryTranslationUnique familyView &&
      candidates.viewTranslationUnique) = true
  familyIndices : Expr
  parameters : instantiateFamilyParameters familyView stats.params.toList =
    .ok familyIndices
  constructors : ConstructorPreFamilyListTrace stats 0 familyIndices context
    candidates

theorem ConstructorPreFamilySafetyTrace.familyTranslationUnique
    (trace : ConstructorPreFamilySafetyTrace stats familyView candidates
      context) :
    TrExprS.IsUnique familyView :=
  by
    have unique := trace.translationUnique
    simp only [Bool.and_eq_true] at unique
    exact theoryTranslationUnique_sound unique.1

theorem ConstructorPreFamilySafetyTrace.constructorTranslationUnique
    (trace : ConstructorPreFamilySafetyTrace stats familyView candidates
      context) :
    candidates.ViewTranslationUnique :=
  by
    have unique := trace.translationUnique
    simp only [Bool.and_eq_true] at unique
    exact candidates.viewTranslationUnique_sound unique.2

/-- Build the complete D3 trace or return the first structural/checker
failure. -/
def buildConstructorPreFamilySafety
    (stats : InductiveStats) (familyView : Expr)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors)
    (context : Context) :
    Except Exception
      (ConstructorPreFamilySafetyTrace stats familyView candidates context) :=
  match translationUnique :
      theoryTranslationUnique familyView &&
        candidates.viewTranslationUnique with
  | false => throw <| .other
      "candidate view contains a projection with no exact Theory endpoint"
  | true =>
      match parameters :
          instantiateFamilyParameters familyView stats.params.toList with
      | .error error => .error error
      | .ok familyIndices => do
          let constructors ← ConstructorPreFamilyListTrace.build stats 0
            familyIndices context candidates
          pure ⟨translationUnique, familyIndices, parameters, constructors⟩

/-! ### Executable pre-family rejection fixtures -/

private def preFamilyNegativeStats : InductiveStats where
  levels := []
  resultLevel := .zero
  nindices := #[0]
  indConsts := #[.const `PreFamilyNegative []]
  params := #[]
  isNotZero := true

private def preFamilyNegativeContext : Context where
  env := Kernel.Environment.ofConstants `_preFamilyNegative
    ({} : ConstMap)
  lparams := []
  safety := .safe
  allowPrimitive := false

/- The traversal begins from the public gate's initial state. Its first
recursive field is omitted from the pre-family context, while the following
ordinary field is independent of that local and is therefore admissible. -/
private def preFamilyOrdinaryAfterRecursiveView : Expr :=
  .forallE `recursive (.const `PreFamilyNegative [])
    (.forallE `ordinary (.sort .zero)
      (.const `PreFamilyNegative []) .default)
    .default

private def preFamilyOrdinaryAfterRecursiveAccepted : Bool :=
  match ConstructorPreFamilyViewTrace.build preFamilyNegativeStats 0
      (.sort (.succ .zero)) preFamilyNegativeContext
      preFamilyOrdinaryAfterRecursiveView 0 [] false
      preFamilyNegativeContext.fuel.inductiveFuel with
  | .ok _ => true
  | .error _ => false

#guard preFamilyOrdinaryAfterRecursiveAccepted

/- The first recursive local is deliberately omitted. Instantiating the next
recursive field exposes that FVar in its domain, so the dependency gate must
reject it before attempting the recursive-field replay. -/
private def preFamilyRecursiveLocalDependencyView : Expr :=
  .forallE `recursive (.const `PreFamilyNegative [])
    (.forallE `dependent
      (.app (.const `PreFamilyNegative []) (.bvar 0))
      (.const `PreFamilyNegative []) .default)
    .default

private def preFamilyRecursiveLocalDependencyRejected : Bool :=
  match ConstructorPreFamilyViewTrace.build preFamilyNegativeStats 0
      (.sort (.succ .zero)) preFamilyNegativeContext
      preFamilyRecursiveLocalDependencyView 0 [] false
      preFamilyNegativeContext.fuel.inductiveFuel with
  | .error (.other message) =>
      message == "constructor depends on an omitted recursive local"
  | _ => false

#guard preFamilyRecursiveLocalDependencyRejected

/-- One executable D3 gate for the complete singleton constructor list.  It
both enforces the recursive-suffix/dependency subset and re-runs every
family-free checker operation in the supplied pre-family context. -/
def checkConstructorPreFamilySafety
    (stats : InductiveStats) (familyView : Expr)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) : M Unit := fun context =>
  if theoryTranslationUnique familyView &&
      candidates.viewTranslationUnique then do
    let familyIndices ← instantiateFamilyParameters familyView
      stats.params.toList
    let _ ← ConstructorPreFamilyListTrace.build stats 0 familyIndices context
      candidates
    pure ()
  else
    throw <| .other
      "candidate view contains a projection with no exact Theory endpoint"

/-- A successful executable D3 gate returns its exact parameter-instantiated
family telescope and source-ordered replay trace. -/
theorem ConstructorPreFamilyListTrace.nonempty_of_check
    (success : checkConstructorPreFamilySafety stats familyView candidates
      context = .ok ()) :
    Nonempty (ConstructorPreFamilySafetyTrace stats familyView candidates
      context) := by
  unfold checkConstructorPreFamilySafety at success
  cases translationUnique :
      theoryTranslationUnique familyView &&
        candidates.viewTranslationUnique with
  | false => simp [translationUnique] at success
  | true =>
      cases parameters : instantiateFamilyParameters familyView
          stats.params.toList with
      | error error =>
          simp [translationUnique, parameters, Bind.bind, Except.bind] at success
      | ok familyIndices =>
          cases constructorsRun : ConstructorPreFamilyListTrace.build stats 0
              familyIndices context candidates with
          | error error =>
              simp [translationUnique, parameters, constructorsRun,
                Bind.bind, Except.bind] at success
          | ok constructors =>
              exact ⟨⟨translationUnique, familyIndices, parameters,
                constructors⟩⟩

/-- A successful executable D3 gate guarantees the retained builder returns
its trace, so gate owners can replay `buildConstructorPreFamilySafety`
instead of choosing from `Nonempty`. -/
theorem buildConstructorPreFamilySafety_ok_of_check
    (success : checkConstructorPreFamilySafety stats familyView candidates
      context = .ok ()) :
    ∃ trace, buildConstructorPreFamilySafety stats familyView candidates
      context = .ok trace := by
  unfold checkConstructorPreFamilySafety at success
  unfold buildConstructorPreFamilySafety
  split
  next translationUnique =>
    simp [translationUnique] at success
  next translationUnique =>
    split
    next error parameters =>
      simp [translationUnique, parameters, Bind.bind, Except.bind] at success
    next familyIndices parameters =>
      cases hbuild : ConstructorPreFamilyListTrace.build stats 0 familyIndices
          context candidates with
      | error error =>
          simp [translationUnique, parameters, hbuild,
            Bind.bind, Except.bind] at success
      | ok constructors =>
          exact ⟨_, rfl⟩

end AddInductive

namespace TypeChecker
open AddInductive

private theorem abstract1_instantiate_self
    (expression : Expr) (id : FVarId) (depth : Nat) :
    Closed expression depth →
    (expression.abstract1 id depth).instantiate1' (.fvar id) depth =
      expression := by
  induction expression generalizing depth <;>
    simp_all [Closed, Expr.abstract1, Expr.instantiate1', beq_iff_eq]
  split <;>
    simp_all [Expr.instantiate1', Expr.liftLooseBVars']

private theorem abstract_instantiate_self
    (expression : Expr) (id : FVarId) (closed : Closed expression) :
    (expression.abstract #[.fvar id]).instantiate1 (.fvar id) =
      expression := by
  rw [show #[Expr.fvar id] = ⟨[id].map Expr.fvar⟩ by rfl]
  simp only [Expr.abstract_eq, Expr.abstractList, Expr.instantiate1_eq]
  exact abstract1_instantiate_self expression id 0 closed

/-- A source-ordered list of kernel parameter FVars builds an exact verified
local telescope.  The final context is obtained by pushing each parameter in
order; dependency metadata is retained but never guessed by consumers. -/
inductive CandidateParameterContext :
    VLCtx → List Expr → List VExpr → VLCtx → Prop where
  | nil : CandidateParameterContext base [] [] base
  | cons
      (tail : CandidateParameterContext
        ((some (fv, deps), .vlam A) :: base) parameters types final) :
      CandidateParameterContext base (.fvar fv :: parameters)
        (A :: types) final

/-- A completed analyzer-owned parameter telescope also certifies every
earlier context in that telescope. -/
theorem CandidateParameterContext.initialWF
    (params : CandidateParameterContext base parameters types final)
    (finalWF : VLCtx.WF env U final) :
    VLCtx.WF env U base := by
  induction params with
  | nil => exact finalWF
  | cons tail ih => exact (ih finalWF).1

/-- The source parameter list and analyzer telescope carried by an exact
parameter context have the same number of entries. -/
theorem CandidateParameterContext.length_eq
    (params : CandidateParameterContext base parameters types final) :
    parameters.length = types.length := by
  induction params with
  | nil => rfl
  | cons tail ih => simp only [List.length_cons, ih]

/-- Replay a successful kernel parameter instantiation against the exact
analyzer-owned Theory parameter telescope.  Each source Pi body is opened by
the corresponding retained FVar; no whole-Pi injectivity or caller-selected
endpoint is used. -/
theorem CandidateParameterContext.instantiateForall
    (params : CandidateParameterContext base parameters types final)
    (henv : VEnv.Ordered env)
    (finalWF : VLCtx.WF env Us.length final)
    (instantiation : instantiateFamilyParameters source parameters = .ok rest)
    (tr : TrExprS env Us base source (VExpr.forallN types result)) :
    TrExprS env Us final rest result := by
  induction params generalizing source rest with
  | nil =>
      have source_eq : source = rest := Except.ok.inj instantiation
      subst rest
      simpa only [VExpr.forallN] using tr
  | @cons fv deps A base parameters types final tail ih =>
      cases source <;> simp only [instantiateFamilyParameters] at instantiation
      case forallE name domain body binderInfo =>
        obtain ⟨domain', body', targetEq, domainType, bodyType, domainTr,
            bodyTr⟩ := TrExprS.forallE_components tr
        simp only [VExpr.forallN, VExpr.forallE.injEq] at targetEq
        obtain ⟨rfl, rfl⟩ := targetEq
        have nextWF : VLCtx.WF env Us.length
            ((some (fv, deps), .vlam A) :: base) :=
          tail.initialWF finalWF
        exact ih finalWF instantiation (by
          simpa only [Expr.instantiate1_eq] using
            bodyTr.inst_fvar henv nextWF)
      all_goals exact nomatch instantiation

/-- Consume an exact prefix of a strictly translated candidate view and keep
the terminal candidate context tied to the corresponding view telescope.

The resulting `parameterContext` is the analyzer-owned prefix context.  The
final `FVLift'` is over precisely the unconsumed suffix, so a strict
translation in the parameter context can be weakened to the same terminal
context used by pre-family constructor replay. -/
theorem CandidateExprRun.parameterViewTerminal
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (contextRun : CandidateContextRun candidateContext)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = Δ)
    (unique : CandidateExprTraceViewIsUnique trace)
    (count : Nat) (hcount : count ≤ trace.spineLength)
    {viewΔ : VLCtx}
    (viewDefEq : VLCtx.IsDefEq env Us.length Δ viewΔ)
    (viewContext : TrExprS.IsUniqueCtx Δ viewΔ)
    (noBV : Δ.NoBV) :
    ∃ (parameterΔ : VLCtx) (rest : Expr)
        (terminalRun : CandidateContextRun trace.terminalContext)
        (viewTerminal : VLCtx),
      instantiateFamilyParameters trace.view (trace.parameterList count) =
        .ok rest ∧
      TrExprS env Us parameterΔ rest (VExpr.dropN count view') ∧
      parameterΔ.toCtx =
        (VExpr.telN count view').reverse ++ viewΔ.toCtx ∧
      CandidateParameterContext viewΔ (trace.parameterList count)
        (VExpr.telN count view') parameterΔ ∧
      parameterΔ.fvars.map Expr.fvar =
        (trace.parameterList count).reverse ++
          viewΔ.fvars.map Expr.fvar ∧
      parameterΔ.NoBV ∧
      VLCtx.WF env Us.length parameterΔ ∧
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      VLCtx.IsDefEq env Us.length terminalRun.context.vlctx viewTerminal ∧
      TrExprS.IsUniqueCtx terminalRun.context.vlctx viewTerminal ∧
      VLCtx.FVLift' parameterΔ viewTerminal 0
        (.skipN .refl (trace.spineLength - count)) 0 ∧
      viewTerminal.toCtx =
        (VExpr.telN (trace.spineLength - count)
          (VExpr.dropN count view')).reverse ++ parameterΔ.toCtx := by
  induction run generalizing count viewΔ with
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
    simp only [AddInductive.CandidateExprTrace.spineLength] at hcount
    have count_eq : count = 0 := Nat.eq_zero_of_le_zero hcount
    subst count
    have strict :=
      CandidateExprRun.view_tr_strict
        (CandidateExprRun.terminal node) unique
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    obtain ⟨moved, movedTr⟩ := strict.defeqDFC henv viewDefEq
    have moved_eq : result' = moved :=
      strict.unique' viewContext unique movedTr
    subst moved
    obtain ⟨terminalRun, viewTerminal, terminalVenv, terminalLparams,
        terminalViewDefEq, terminalViewContext, terminalViewLift,
        terminalViewEq⟩ :=
      (CandidateExprRun.terminal node).terminalContextRunView contextRun
        venv_eq lparams_eq vlctx_eq viewDefEq viewContext
    exact ⟨viewΔ, result, terminalRun, viewTerminal, rfl, movedTr, rfl, .nil,
      by simp [AddInductive.CandidateExprTrace.parameterList],
      by simpa only [VLCtx.NoBV, ← viewDefEq.bvars] using noBV,
      (viewDefEq.symm henv.ordered).wf,
      terminalVenv, terminalLparams, terminalViewDefEq, terminalViewContext,
      by simpa only [Nat.sub_zero] using terminalViewLift,
      by simpa only [Nat.sub_zero, VExpr.dropN] using terminalViewEq⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    have currentRun := CandidateExprRun.forallE
      (fresh := fresh) (checked := checked) (normalized := normalized)
      annotations annotationsEq domainCandidate bodyCandidate node domainRun
      annotationsRun bodyRun domainType bodyType bodySource bodyContext
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    have allUnique := unique
    rcases unique with ⟨domainUnique, bodyUnique, abstractUnique⟩
    cases count with
    | zero =>
        have strict := currentRun.view_tr_strict allUnique
        obtain ⟨moved, movedTr⟩ := strict.defeqDFC henv viewDefEq
        have moved_eq : VExpr.forallE domainView' bodyView' = moved :=
          strict.unique' viewContext allUnique.view movedTr
        subst moved
        obtain ⟨terminalRun, viewTerminal, terminalVenv, terminalLparams,
            terminalViewDefEq, terminalViewContext, terminalViewLift,
            terminalViewEq⟩ :=
          currentRun.terminalContextRunView contextRun venv_eq lparams_eq
            vlctx_eq viewDefEq viewContext
        exact ⟨viewΔ, _, terminalRun, viewTerminal, rfl, movedTr, rfl, .nil,
          by simp [AddInductive.CandidateExprTrace.parameterList],
          by simpa only [VLCtx.NoBV, ← viewDefEq.bvars] using noBV,
          (viewDefEq.symm henv.ordered).wf,
          terminalVenv, terminalLparams, terminalViewDefEq,
          terminalViewContext,
          by simpa only [Nat.sub_zero] using terminalViewLift,
          by simpa only [Nat.sub_zero, VExpr.dropN] using terminalViewEq⟩
    | succ count =>
        simp only [AddInductive.CandidateExprTrace.spineLength,
          Nat.succ_le_succ_iff] at hcount
        have domainDef : env.IsDefEq Us.length Δ.toCtx
            domain' domainView' (.sort u) :=
          domainRun.evidence.isDefEq.toU.of_l henv hΔ.toCtx domainType
        have annotationDef : env.IsDefEq Us.length Δ.toCtx
            domain' storedDomain' (.sort u) :=
          annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
        have storedToView : env.IsDefEq Us.length Δ.toCtx
            storedDomain' domainView' (.sort u) :=
          annotationDef.symm.trans domainDef
        have storedDomain_tr : contextRun.context.TrExprS
            annotations.consumed storedDomain' := by
          simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
            annotationsRun.rhs_tr
        have storedDomain_type : env.IsType Us.length Δ.toCtx storedDomain' :=
          ⟨u, annotationDef.hasType.2⟩
        let nextContextRun := contextRun.pushLocalDecl name binderInfo
          annotations.consumed fresh storedDomain' storedDomain_tr (by
            change contextRun.context.venv.IsType
              contextRun.context.lparams.length
              contextRun.context.vlctx.toCtx storedDomain'
            rw [venv_eq, lparams_eq, vlctx_eq]
            exact storedDomain_type)
        have nextVenv : nextContextRun.context.venv = env := by
          simp only [nextContextRun, CandidateContextRun.pushLocalDecl_venv,
            venv_eq]
        have nextLparams : nextContextRun.context.lparams = Us := by
          simp only [nextContextRun, CandidateContextRun.pushLocalDecl_lparams,
            lparams_eq]
        have nextVlctx : nextContextRun.context.vlctx = bodyΔ := by
          simp only [nextContextRun, CandidateContextRun.pushLocalDecl_vlctx]
          rw [vlctx_eq, bodyContext]
        let viewBodyΔ : VLCtx :=
          (some (context.freshFVarId, annotations.consumed.fvarsList),
            .vlam domainView') :: viewΔ
        have bodyWF := bodyRun.context_wf
        rw [bodyContext] at bodyWF
        have bodyViewDefEq : VLCtx.IsDefEq env Us.length bodyΔ viewBodyΔ := by
          rw [bodyContext]
          exact .cons viewDefEq bodyWF.2.1 (.vlam storedToView)
        have bodyViewContext : TrExprS.IsUniqueCtx bodyΔ viewBodyΔ := by
          rw [bodyContext]
          exact viewContext.cons .vlam
        have bodyNoBV : bodyΔ.NoBV := by
          rw [bodyContext]
          simpa only [VLCtx.NoBV, VLCtx.bvars] using noBV
        obtain ⟨parameterΔ, rest, terminalRun, viewTerminal, restEq,
            restTr, parameterCtx, parameterContext, parameterFVars,
            parameterNoBV, parameterWF, terminalVenv,
            terminalLparams, terminalViewDefEq, terminalViewContext,
            terminalViewLift, terminalViewEq⟩ :=
          bodyIH nextContextRun nextVenv nextLparams nextVlctx bodyUnique
            count hcount bodyViewDefEq bodyViewContext bodyNoBV
        have bodyClosed : Closed bodyCandidate.view := by
          have closed := (bodyRun.view_tr_strict bodyUnique).closed
          simpa only [bodyNoBV] using closed
        refine ⟨parameterΔ, rest, terminalRun, viewTerminal, ?_, ?_, ?_,
          ?_, ?_, parameterNoBV, parameterWF, terminalVenv, terminalLparams,
          ?_, ?_, ?_, ?_⟩
        · simp only [AddInductive.CandidateExprTrace.view,
            AddInductive.CandidateExprTrace.parameterList,
            instantiateFamilyParameters]
          change instantiateFamilyParameters
            ((bodyCandidate.view.abstract
              #[.fvar context.freshFVarId]).instantiate1
                (.fvar context.freshFVarId)) _ = _
          rw [abstract_instantiate_self _ _ bodyClosed]
          exact restEq
        · simpa only [VExpr.dropN] using restTr
        · simpa only [AddInductive.CandidateExprTrace.spineLength,
            VExpr.telN, List.reverse_cons, List.singleton_append,
            List.append_assoc, viewBodyΔ, VLCtx.toCtx] using parameterCtx
        · simpa only [AddInductive.CandidateExprTrace.parameterList,
            VExpr.telN, viewBodyΔ, AddInductive.Context.freshExpr] using
            CandidateParameterContext.cons parameterContext
        · simpa [AddInductive.CandidateExprTrace.parameterList,
            List.reverse_cons, List.singleton_append, List.append_assoc,
            viewBodyΔ, VLCtx.fvars, AddInductive.Context.freshExpr] using
            parameterFVars
        · simpa only [AddInductive.CandidateExprTrace.terminalContext] using
            terminalViewDefEq
        · simpa only [AddInductive.CandidateExprTrace.terminalContext] using
            terminalViewContext
        · simpa only [AddInductive.CandidateExprTrace.spineLength,
            Nat.succ_sub_succ_eq_sub] using terminalViewLift
        · simpa only [AddInductive.CandidateExprTrace.spineLength,
            Nat.succ_sub_succ_eq_sub, VExpr.dropN] using terminalViewEq

end TypeChecker

namespace VInductDecl

/-!
## Staged ownership

The ordinary outer producer deliberately remains unchanged: its successful
equation records kernel validation, while this additive wrapper retains the
verified audit of constructor-universe comparisons. The normalized branch
intersects the ordinary core decision with
the proved project comparison, without making bare
`buildNormalizationCandidate` success carry Theory meaning.
-/

/-- A staged singleton semantic input together with the exact executable
constructor-universe audit for the same source list, family-validation stats,
and post-family checker context.

Keeping the ordinary staged input as data preserves the established candidate
and semantic hierarchy.  The dependent `universeRun` field prevents an audit
for another family, constructor ordering, parameter split, or environment from
being reused here. -/
structure StagedNormalizationCandidateUniverseInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  staged : StagedNormalizationCandidateSemanticInput familyContext
    constructorContext env Us candidate rawDecl
  universeRun :
    AddInductive.checkConstructorUniverseListSemantics
        staged.family.validation.stats source.ctors
        { candidate.families.singleton.familyType.type.trace.terminalContext with
          env := constructorContext.env } = .ok ()

/-- Pair the retained ordinary validation trace with its source-indexed
universe audit.  This is the strengthened D1 validation object; forgetting it
recovers exactly the pre-existing staged owner. -/
def StagedNormalizationCandidateUniverseInput.semanticValidation
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl) :
    AddInductive.ConstructorSemanticValidationRun source
      input.staged.family.validation.stats false
      { candidate.families.singleton.familyType.type.trace.terminalContext with
        env := constructorContext.env } where
  validation := input.staged.constructorValidation
  universeRun := input.universeRun

/-- Every universe-bearing node in the staged source-ordered validation trace
passes the verified semantic universe gate. -/
theorem StagedNormalizationCandidateUniverseInput.universeSemantics
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl) :
    input.staged.constructorValidation.universeSemantics = true :=
  input.semanticValidation.universeSemantics

/-- Preserve the existing automatic semantic-hierarchy construction while
retaining the strengthened universe gate in its staged owner. -/
theorem StagedNormalizationCandidateUniverseInput.exists
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl) :
    Nonempty (ProducedNormalizationCandidateSemanticRun familyContext
    constructorContext env Us candidate rawDecl) :=
  input.staged.exists

/-!
## Post-family constructor ownership

This additive D2 owner keeps D1's universe gate and adds the exact executable
alignment between the retained validation telescope and every analyzer-owned
constructor candidate.  It does not replay `checkConstructors` on the view or
claim any pre-family field judgment.
-/

/-- The staged semantic/universe owner together with the source-ordered
post-family constructor alignment audit. -/
structure StagedNormalizationCandidatePostFamilyInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  universeInput : StagedNormalizationCandidateUniverseInput familyContext
    constructorContext env Us candidate rawDecl
  alignment : AddInductive.ConstructorCandidateAlignmentTrace
    universeInput.staged.family.validation.stats false 0
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
    universeInput.staged.constructorValidation.trace
    candidate.families.singleton.constructors

/-- Package a successful executable alignment audit into the staged D2 owner.
The direct `alignment` field also permits proof-oriented clients to assemble
the same indexed trace from already-retained checker observations.  The
retained trace is computed by replaying the alignment builder; the audit
premise only discharges its impossible error branch. -/
def StagedNormalizationCandidatePostFamilyInput.ofRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (universeInput : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl)
    (alignmentRun :
      universeInput.staged.constructorValidation.trace.checkCandidateAlignment
          candidate.families.singleton.constructors
          { candidate.families.singleton.familyType.type.trace.terminalContext with
            env := constructorContext.env } = .ok ()) :
    StagedNormalizationCandidatePostFamilyInput familyContext
      constructorContext env Us candidate rawDecl where
  universeInput := universeInput
  alignment :=
    match h : AddInductive.ConstructorCandidateAlignmentTrace.build
        universeInput.staged.constructorValidation.trace
        candidate.families.singleton.constructors with
    | .ok alignment => alignment
    | .error _ =>
        absurd
          (AddInductive.ConstructorCandidateAlignmentTrace.build_ok_of_check
            alignmentRun)
          (by simp [h])

/-- The exact output of D2: the established produced semantic hierarchy plus
the actual post-family validation context, retained source/candidate
alignment, and a positional semantic interpretation of every exact candidate
view binder and terminal result. -/
structure ProducedNormalizationCandidatePostFamilySemanticRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePostFamilyInput familyContext
      constructorContext env Us candidate rawDecl) where
  produced : ProducedNormalizationCandidateSemanticRun familyContext
    constructorContext env Us candidate rawDecl
  contextRun : AddInductive.ConstructorContextRun
    produced.semantic.family.typeEnv Us
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
  alignment : AddInductive.ConstructorCandidateAlignmentTrace
    input.universeInput.staged.family.validation.stats false 0
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
    input.universeInput.staged.constructorValidation.trace
    candidate.families.singleton.constructors
  constructors : AddInductive.ConstructorPostFamilySemanticListRun
    produced.semantic.family.typeEnv Us
    input.universeInput.staged.family.validation.stats false 0
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
    contextRun input.universeInput.staged.constructorValidation.trace
    candidate.families.singleton.constructors alignment
    produced.semantic.family.constructors

/-- Interpret D2's executable alignment in the exact post-family Theory
environment obtained by the retained raw-family insertion.  The only
existential selections are checker-produced Theory translations already
encapsulated by `Nonempty`; no caller supplies a view. -/
theorem StagedNormalizationCandidatePostFamilyInput.exists
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePostFamilyInput familyContext
      constructorContext env Us candidate rawDecl) :
    Nonempty (ProducedNormalizationCandidatePostFamilySemanticRun input) := by
  obtain ⟨familySemantic⟩ :=
    input.universeInput.staged.semanticInput.family.exists
  let semantic : NormalizationCandidateSemanticRun env Us candidate rawDecl :=
    { raw := input.universeInput.staged.raw
      raw_types_eq := input.universeInput.staged.raw_types_eq
      uvars_eq := input.universeInput.staged.declaration_uvars_eq
      family := familySemantic }
  let produced : ProducedNormalizationCandidateSemanticRun familyContext
      constructorContext env Us candidate rawDecl :=
    { semantic := semantic
      familyTypesProduced :=
        input.universeInput.staged.familyTypesProduced
      familiesProduced := input.universeInput.staged.familiesProduced }
  have typeEnv_eq : familySemantic.typeEnv =
      input.universeInput.staged.family.typeEnv := by
    exact Option.some.inj <|
      familySemantic.addType.symm.trans
        input.universeInput.staged.family.addInduct.env_add
  obtain ⟨candidateContext, venv_eq, lparams_eq⟩ :=
    input.universeInput.staged.family.validationContextRun
      familySemantic.type
  let contextRun : AddInductive.ConstructorContextRun
      produced.semantic.family.typeEnv Us
      { candidate.families.singleton.familyType.type.trace.terminalContext with
        env := constructorContext.env } :=
    ⟨candidateContext, venv_eq.trans typeEnv_eq.symm, lparams_eq⟩
  let alignment := input.alignment
  obtain ⟨constructors⟩ :=
    AddInductive.ConstructorPostFamilySemanticListRun.nonempty_of_alignment
      contextRun alignment produced.semantic.family.constructors
  exact ⟨⟨produced, contextRun, alignment, constructors⟩⟩

/-!
## Pre-family constructor ownership

The D3 owner extends the staged D2 package with the output of one executable
pre-family safety gate. Its semantic result is reconstructed from that exact
trace in the verified context reached by family normalization before the raw
family constant is inserted.
-/

/-- The staged D2 owner together with the exact executable pre-family safety
trace for the same singleton family view and dependent constructor list. -/
structure StagedNormalizationCandidatePreFamilyInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  postFamilyInput : StagedNormalizationCandidatePostFamilyInput familyContext
    constructorContext env Us candidate rawDecl
  safety : AddInductive.ConstructorPreFamilySafetyTrace
    postFamilyInput.universeInput.staged.family.validation.stats
    candidate.families.singleton.familyType.type.view
    candidate.families.singleton.constructors
    candidate.families.singleton.familyType.type.trace.terminalContext

/-- Package a successful executable D3 gate into the staged owner. The gate
itself, rather than a caller-supplied Theory premise, selects the retained
parameter-instantiated family telescope and constructor traces.  The trace
is computed by replaying the safety builder; the gate premise only
discharges its impossible error branch. -/
def StagedNormalizationCandidatePreFamilyInput.ofRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (postFamilyInput : StagedNormalizationCandidatePostFamilyInput
      familyContext constructorContext env Us candidate rawDecl)
    (safetyRun : AddInductive.checkConstructorPreFamilySafety
        postFamilyInput.universeInput.staged.family.validation.stats
        candidate.families.singleton.familyType.type.view
        candidate.families.singleton.constructors
        candidate.families.singleton.familyType.type.trace.terminalContext =
      .ok ()) :
    StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl where
  postFamilyInput := postFamilyInput
  safety :=
    match h : AddInductive.buildConstructorPreFamilySafety
        postFamilyInput.universeInput.staged.family.validation.stats
        candidate.families.singleton.familyType.type.view
        candidate.families.singleton.constructors
        candidate.families.singleton.familyType.type.trace.terminalContext with
    | .ok safety => safety
    | .error _ =>
        absurd
          (AddInductive.buildConstructorPreFamilySafety_ok_of_check safetyRun)
          (by simp [h])

/-- D3's produced meaning: D2's post-family semantics together with the exact
verified pre-family context and source-ordered family-free replay selected by
the executable safety trace. -/
structure ProducedNormalizationCandidatePreFamilySemanticRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl) where
  postFamily : ProducedNormalizationCandidatePostFamilySemanticRun
    input.postFamilyInput
  contextRun : AddInductive.ConstructorContextRun env Us
    candidate.families.singleton.familyType.type.trace.terminalContext
  constructors : AddInductive.ConstructorPreFamilyListSemanticRun env Us
    input.postFamilyInput.universeInput.staged.family.validation.stats 0
    input.safety.familyIndices
    candidate.families.singleton.familyType.type.trace.terminalContext
    contextRun input.safety.constructors

/-- Interpret the executable D3 safety trace in the exact verified pre-family
context recovered from the retained family semantic normalization run. -/
theorem StagedNormalizationCandidatePreFamilyInput.exists
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl) :
    Nonempty (ProducedNormalizationCandidatePreFamilySemanticRun input) := by
  obtain ⟨postFamily⟩ := input.postFamilyInput.exists
  have raw_eq : postFamily.produced.semantic.raw =
      input.postFamilyInput.universeInput.staged.raw := by
    have singleton_eq :=
      postFamily.produced.semantic.raw_types_eq.symm.trans
        input.postFamilyInput.universeInput.staged.raw_types_eq
    injection singleton_eq
  have familyType : TypeChecker.CandidateExprSemanticRootRun env Us
      candidate.families.singleton.familyType.type
      input.postFamilyInput.universeInput.staged.raw.type := by
    rw [← raw_eq]
    exact postFamily.produced.semantic.family.type
  obtain ⟨candidateContext, venv_eq, lparams_eq⟩ :=
    input.postFamilyInput.universeInput.staged.family.preValidationContextRun
      familyType
  let contextRun : AddInductive.ConstructorContextRun env Us
      candidate.families.singleton.familyType.type.trace.terminalContext :=
    ⟨candidateContext, venv_eq, lparams_eq⟩
  obtain ⟨constructors⟩ :=
    AddInductive.ConstructorPreFamilyListSemanticRun.nonempty contextRun
      input.safety.constructors
  exact ⟨⟨postFamily, contextRun, constructors⟩⟩

/-- Invert a verified iterated Pi type into its exact source-ordered
telescope and terminal type. -/
private theorem isType_forallN_inv
    (henv : VEnv.Ordered env) :
    ∀ {As : List VExpr} {U : Nat} {Γ : List VExpr} {B : VExpr},
      env.IsType U Γ (VExpr.forallN As B) →
        env.OnTel U Γ As ∧
          env.IsType U (As.reverse ++ Γ) B
  | [], U, Γ, B, h => by
      change env.IsType _ _ B at h
      exact ⟨trivial, h⟩
  | A :: As, U, Γ, B, h => by
      obtain ⟨hA, hrest⟩ := h.forallE_inv henv
      obtain ⟨hAs, hB⟩ := isType_forallN_inv henv hrest
      exact ⟨⟨hA, hAs⟩, by
        simpa [List.reverse_cons, List.append_assoc] using hB⟩

/-- The family normalization trace and the analyzer's exact generation
equation derive the checked parameter/index telescope. No checked- or
view-well-formedness premise is accepted. -/
theorem StagedNormalizationCandidatePreFamilyInput.familyOnTel
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl)
    (normalization : NormalizationCandidateSemanticRun env Us candidate rawDecl)
    (generation : GenerationChecked rawDecl)
    (analysis : normalization.root.normalization.generation? =
      some generation) :
    env.OnTel rawDecl.uvars []
      (generation.block.checked.params ++ generation.block.checked.indices) := by
  obtain ⟨_, recursive⟩ := normalization.family.type.recursive
  have familyType : env.IsType Us.length [] normalization.family.type.view :=
    recursive.view_isType_of_terminalSort
      input.postFamilyInput.universeInput.staged.family.validation.terminal_eq
  have view_eq : normalization.family.type.view =
      generation.block.checked.type.type := by
    exact (congrArg (fun ty : VInductiveType => ty.type)
      (normalization.root.familyViewType_eq analysis)).symm
  rw [view_eq, generation.block.checked.type_eq,
    ← VExpr.forallN_append] at familyType
  have henv : VEnv.Ordered env := by
    simpa only [normalization.family.type.venv_eq] using
      normalization.family.type.contextRun.context.Ewf.ordered
  have htel := (isType_forallN_inv henv familyType).1
  simpa only [normalization.uvars_eq] using htel

open AddInductive TypeChecker

private theorem familyTelNForallNLength :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.telN As.length (VExpr.forallN As B) = As
  | [], _ => rfl
  | _ :: As, B => by
      simp only [List.length_cons, VExpr.forallN, VExpr.telN,
        familyTelNForallNLength As B]

private theorem familyDropNForallNLength :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.dropN As.length (VExpr.forallN As B) = B
  | [], _ => rfl
  | _ :: As, B => by
      simp only [List.length_cons, VExpr.forallN, VExpr.dropN,
        familyDropNForallNLength As B]

/-- Consume the validator-owned parameter prefix of the retained family
candidate and identify both resulting contexts with the analyzer telescope.

The executable D3 gate selects the residual kernel family expression.  Strict
translation uniqueness, the exact generation shape, and dependent analysis
then identify its Theory endpoint and the terminal local context; neither a
view nor a view-context premise is supplied by the caller. -/
theorem StagedNormalizationCandidatePreFamilyInput.familyParameterTerminal
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl)
    (normalization : NormalizationCandidateSemanticRun env Us candidate rawDecl)
    (generation : GenerationChecked rawDecl)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    let trace := candidate.families.singleton.familyType.type.trace
    ∃ (parameterΔ : VLCtx) (rest : Expr)
        (terminalRun : CandidateContextRun trace.terminalContext)
        (viewTerminal : VLCtx),
      instantiateFamilyParameters trace.view
          (trace.parameterList rawDecl.nparams) = .ok rest ∧
      TrExprS env Us parameterΔ rest
        (VExpr.dropN rawDecl.nparams normalization.family.type.view) ∧
      parameterΔ.toCtx =
        (VExpr.telN rawDecl.nparams normalization.family.type.view).reverse ∧
      CandidateParameterContext [] (trace.parameterList rawDecl.nparams)
        (VExpr.telN rawDecl.nparams normalization.family.type.view)
        parameterΔ ∧
      parameterΔ.fvars.map Expr.fvar =
        (trace.parameterList rawDecl.nparams).reverse ∧
      parameterΔ.NoBV ∧
      VLCtx.WF env Us.length parameterΔ ∧
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      VLCtx.IsDefEq env Us.length terminalRun.context.vlctx viewTerminal ∧
      TrExprS.IsUniqueCtx terminalRun.context.vlctx viewTerminal ∧
      VLCtx.FVLift' parameterΔ viewTerminal 0
        (.skipN .refl generation.block.checked.indices.length) 0 ∧
      viewTerminal.toCtx =
        generation.block.checked.indices.reverse ++ parameterΔ.toCtx := by
  dsimp only
  have familyShape := shape
  simp only [NormalizationCandidateSemanticRun.generationShape,
    normalizationCandidateGenerationShape, Bool.and_eq_true,
    beq_iff_eq] at familyShape
  have spineLength_eq :
      candidate.families.singleton.familyType.type.trace.spineLength =
        (generation.block.checked.params ++
          generation.block.checked.indices).length := by
    calc
      _ = (VExpr.telN rawDecl.nparams normalization.raw.type ++
          ctorFields (VExpr.dropN rawDecl.nparams normalization.raw.type)).length :=
        familyShape.1.2
      _ = (generation.block.rawParams ++
          generation.block.rawIndices).length := by
        simp only [NormalizedChecked.rawParams, NormalizedChecked.rawIndices,
          NormalizationCandidateSemanticRun.root,
          normalization.root.sourceType_eq generation]
      _ = (generation.block.checked.params ++
          generation.block.checked.indices).length := by
        simp only [List.length_append]
        rw [generation.shape.2.1, generation.shape.2.2.1]
  have parameterLength : generation.block.checked.params.length =
      rawDecl.nparams :=
    generation.block.checked.direct_anatomy.2.1.trans
      generation.block.nparams_eq.symm
  have hcount : rawDecl.nparams ≤
      candidate.families.singleton.familyType.type.trace.spineLength := by
    rw [spineLength_eq]
    simpa only [List.length_append, parameterLength] using
      Nat.le_add_right rawDecl.nparams
        generation.block.checked.indices.length
  have unique : CandidateExprTraceViewIsUnique
      candidate.families.singleton.familyType.type.trace := by
    apply CandidateExprTrace.viewTranslationUnique_sound
    rw [CandidateExprTrace.viewTranslationUnique_eq]
    have uniqueGate := input.safety.translationUnique
    simp only [Bool.and_eq_true] at uniqueGate
    exact uniqueGate.1
  obtain ⟨inferred, recursive⟩ := normalization.family.type.recursive
  have rootWF : VLCtx.WF env Us.length ([] : VLCtx) := by
    simpa only [normalization.family.type.venv_eq,
      normalization.family.type.lparams_eq,
      normalization.family.type.vlctx_eq] using
      normalization.family.type.contextRun.context.Δwf
  have henv : VEnv.Ordered env := by
    simpa only [normalization.family.type.venv_eq] using
      normalization.family.type.contextRun.context.Ewf.ordered
  obtain ⟨parameterΔ, rest, terminalRun, viewTerminal, restEq, restTr,
      parameterCtx, parameterContext, parameterFVars, parameterNoBV,
      parameterWF, terminalVenv, terminalLparams,
      terminalViewDefEq, terminalViewContext, terminalViewLift,
      terminalViewEq⟩ :=
    recursive.parameterViewTerminal normalization.family.type.contextRun
      normalization.family.type.venv_eq normalization.family.type.lparams_eq
      normalization.family.type.vlctx_eq unique rawDecl.nparams hcount
      (.refl henv rootWF) .base (by rfl)
  have remaining_eq :
      candidate.families.singleton.familyType.type.trace.spineLength -
          rawDecl.nparams = generation.block.checked.indices.length := by
    rw [spineLength_eq, List.length_append,
      parameterLength, Nat.add_sub_cancel_left]
  have view_eq : normalization.family.type.view =
      generation.block.checked.type.type :=
    (congrArg (fun ty : VInductiveType => ty.type)
      (normalization.root.familyViewType_eq analysis)).symm
  have viewDrop_eq :
      VExpr.dropN rawDecl.nparams normalization.family.type.view =
        VExpr.forallN generation.block.checked.indices
          (.sort generation.block.checked.resultLevel) := by
    rw [view_eq, generation.block.checked.type_eq, ← parameterLength]
    exact familyDropNForallNLength _ _
  refine ⟨parameterΔ, rest, terminalRun, viewTerminal, restEq, restTr, ?_,
    parameterContext, ?_, parameterNoBV, parameterWF, terminalVenv,
    terminalLparams,
    terminalViewDefEq,
    terminalViewContext, ?_, ?_⟩
  · simpa only [VLCtx.toCtx, List.append_nil] using parameterCtx
  · simpa [VLCtx.fvars] using parameterFVars
  · simpa only [remaining_eq] using terminalViewLift
  · rw [remaining_eq, viewDrop_eq,
      familyTelNForallNLength] at terminalViewEq
    exact terminalViewEq

/-- The analyzer-owned family prefix and D3's pre-family terminal context,
with the residual kernel expression fixed to the exact executable safety
trace and every Theory telescope component fixed to dependent analysis. -/
theorem StagedNormalizationCandidatePreFamilyInput.familyContext
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl)
    (normalization : NormalizationCandidateSemanticRun env Us candidate rawDecl)
    (generation : GenerationChecked rawDecl)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    let trace := candidate.families.singleton.familyType.type.trace
    ∃ (parameterΔ : VLCtx)
        (terminalRun : CandidateContextRun trace.terminalContext)
        (viewTerminal : VLCtx),
      instantiateFamilyParameters trace.view
          (trace.parameterList rawDecl.nparams) =
        .ok input.safety.familyIndices ∧
      TrExprS env Us parameterΔ input.safety.familyIndices
        (VExpr.forallN generation.block.checked.indices
          (.sort generation.block.checked.resultLevel)) ∧
      parameterΔ.toCtx = generation.block.checked.params.reverse ∧
      CandidateParameterContext [] (trace.parameterList rawDecl.nparams)
        generation.block.checked.params parameterΔ ∧
      parameterΔ.fvars.map Expr.fvar =
        (trace.parameterList rawDecl.nparams).reverse ∧
      parameterΔ.NoBV ∧
      VLCtx.WF env Us.length parameterΔ ∧
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      VLCtx.IsDefEq env Us.length terminalRun.context.vlctx viewTerminal ∧
      TrExprS.IsUniqueCtx terminalRun.context.vlctx viewTerminal ∧
      VLCtx.FVLift' parameterΔ viewTerminal 0
        (.skipN .refl generation.block.checked.indices.length) 0 ∧
      viewTerminal.toCtx =
        generation.block.checked.indices.reverse ++
          generation.block.checked.params.reverse := by
  dsimp only
  obtain ⟨parameterΔ, rest, terminalRun, viewTerminal, restEq, restTr,
      parameterCtx, parameterContext, parameterFVars, parameterNoBV,
      parameterWF, terminalVenv, terminalLparams,
      terminalViewDefEq, terminalViewContext, terminalViewLift,
      terminalViewEq⟩ := input.familyParameterTerminal normalization
    generation analysis shape
  let validation :=
    input.postFamilyInput.universeInput.staged.family.validation
  have statsParams : validation.stats.params.toList =
      candidate.families.singleton.familyType.type.trace.parameterList
        rawDecl.nparams := by
    rw [validation.stats_eq]
    simp only [CandidateExprTrace.singletonCandidateInductiveStats,
      validation, input.postFamilyInput.universeInput.staged.validation_nparams_eq]
  have safetyParameters := input.safety.parameters
  rw [statsParams] at safetyParameters
  have rest_eq : rest = input.safety.familyIndices := by
    exact Except.ok.inj (restEq.symm.trans safetyParameters)
  subst rest
  have parameterLength : generation.block.checked.params.length =
      rawDecl.nparams :=
    generation.block.checked.direct_anatomy.2.1.trans
      generation.block.nparams_eq.symm
  have view_eq : normalization.family.type.view =
      generation.block.checked.type.type :=
    (congrArg (fun ty : VInductiveType => ty.type)
      (normalization.root.familyViewType_eq analysis)).symm
  have viewDrop_eq :
      VExpr.dropN rawDecl.nparams normalization.family.type.view =
        VExpr.forallN generation.block.checked.indices
          (.sort generation.block.checked.resultLevel) := by
    rw [view_eq, generation.block.checked.type_eq, ← parameterLength]
    exact familyDropNForallNLength _ _
  have parameterTel_eq :
      VExpr.telN rawDecl.nparams normalization.family.type.view =
        generation.block.checked.params := by
    rw [view_eq, generation.block.checked.type_eq, ← parameterLength]
    exact familyTelNForallNLength _ _
  refine ⟨parameterΔ, terminalRun, viewTerminal, restEq, ?_, ?_,
    ?_, parameterFVars, parameterNoBV, parameterWF, terminalVenv,
    terminalLparams,
    terminalViewDefEq,
    terminalViewContext, terminalViewLift, ?_⟩
  · simpa only [viewDrop_eq] using restTr
  · simpa only [parameterTel_eq] using parameterCtx
  · simpa only [parameterTel_eq] using parameterContext
  · simpa only [parameterCtx, parameterTel_eq] using terminalViewEq

/-- Peeling at most `n` binders cannot expose more than `n` telescope
entries. -/
private theorem constructorTelN_length_le (n : Nat) (expression : VExpr) :
    (VExpr.telN n expression).length ≤ n := by
  induction n generalizing expression with
  | zero => simp [VExpr.telN]
  | succ n ih => cases expression <;> simp [VExpr.telN, ih]

/-- Strip the validator-owned parameter prefix from one analyzer-selected
constructor and retain the exact D3 suffix together with its strict Theory
translation.

The source parameter list is fixed by the family validation statistics, the
Theory parameter telescope is fixed by dependent analysis, and the complete
constructor endpoint is fixed by the analyzer-owned raw/view pairing.  Thus
the residual endpoint is precisely the stored view fields followed by the
analyzed result target; no whole-Pi injectivity or caller-selected view is
used. -/
theorem CandidateSemanticNormalizedCtorRun.preFamilySuffix
    {env typeEnv : VEnv} {Us : List Name}
    {source : VInductDecl} {generation : GenerationChecked source}
    {kernelCtor : Constructor}
    {candidateCtor : AddInductive.CandidateConstructor kernelCtor}
    {rawCtor : VConstVal}
    {root : CandidateConstructorSemanticRun typeEnv Us candidateCtor rawCtor}
    {ctor : NormalizedCtor}
    {stats : InductiveStats} {familyIndices : Expr}
    {context : AddInductive.Context}
    {contextRun : AddInductive.ConstructorContextRun env Us context}
    {d3Trace : AddInductive.ConstructorPreFamilyViewTrace stats 0
      familyIndices context candidateCtor.type.view 0 [] false}
    {parameterΔ : VLCtx} {parameters : List Expr}
    (genRun : CandidateSemanticNormalizedCtorRun generation.block typeEnv Us
      root ctor)
    (addType : env ≤ typeEnv)
    (parameterContext : CandidateParameterContext [] parameters
      generation.block.checked.params parameterΔ)
    (parameterWF : VLCtx.WF env Us.length parameterΔ)
    (unique : CandidateExprTraceViewIsUnique candidateCtor.type.trace)
    (d3 : AddInductive.ConstructorPreFamilyViewSemanticRun env Us stats 0
      familyIndices contextRun d3Trace)
    (hctor : ctor ∈ generation.block.ctorPairs)
    (parametersEq : stats.params.toList = parameters)
    {familyName : Name} {levels : List Level}
    (indConsts : stats.indConsts = #[.const familyName levels]) :
    ∃ rest,
      instantiateFamilyParameters candidateCtor.type.view stats.params.toList =
          .ok rest ∧
      Nonempty (AddInductive.ConstructorPreFamilyParameterSuffix
        (env := env) (Us := Us) (stats := stats)
        (familyIndices := familyIndices) (context := context)
        (removed := []) (recursiveStarted := false)
        (contextRun := contextRun) rest) ∧
      TrExprS typeEnv Us parameterΔ rest
        (VExpr.forallN ctor.view.fields
          (ctor.resultTarget generation.block)) := by
  have viewTel := genRun.run.viewTel_eq hctor
  simp only [CandidateConstructorSemanticRun.root,
    NormalizedCtor.viewBinders] at viewTel
  have parameterLengthLe : generation.block.checked.params.length ≤
      candidateCtor.type.trace.spineLength := by
    apply Nat.le_trans (Nat.le_add_right _ ctor.view.fields.length)
    rw [← List.length_append, ← viewTel]
    exact constructorTelN_length_le _ _
  have sourceParameterLength : stats.params.toList.length ≤
      candidateCtor.type.trace.spineLength := by
    rw [parametersEq, parameterContext.length_eq]
    exact parameterLengthLe
  obtain ⟨rest, instantiation⟩ :=
    candidateCtor.type.trace.instantiateViewParameters stats.params.toList
      sourceParameterLength
  obtain ⟨inferred, recursive⟩ := root.type.recursive
  have wholeTr : TrExprS typeEnv Us [] candidateCtor.type.view
      (VExpr.forallN generation.block.checked.params
        (VExpr.forallN ctor.view.fields
          (ctor.resultTarget generation.block))) := by
    have strict := recursive.view_tr_strict unique
    have viewTypeEq : root.type.view = ctor.view.value.type := by
      simpa only [CandidateConstructorSemanticRun.root,
        CandidateConstructorRun.view] using
        (congrArg (fun value : VConstVal => value.type) genRun.view_eq).symm
    rw [viewTypeEq, generation.viewCtorType_eq hctor,
      NormalizedCtor.viewBinders] at strict
    simpa only [CandidateExpr.view, VExpr.forallN_append] using strict
  have parameterWF' : VLCtx.WF typeEnv Us.length parameterΔ :=
    parameterWF.mono addType
  have typeEnvOrdered : typeEnv.Ordered := by
    simpa only [root.type.venv_eq] using
      root.type.contextRun.context.Ewf.ordered
  have suffixTr : TrExprS typeEnv Us parameterΔ rest
      (VExpr.forallN ctor.view.fields
        (ctor.resultTarget generation.block)) := by
    apply parameterContext.instantiateForall typeEnvOrdered parameterWF'
    · simpa only [← parametersEq] using instantiation
    · exact wholeTr
  obtain ⟨suffix⟩ :=
    d3.afterParameters indConsts (by simp) (by
      simpa only [CandidateExpr.view, List.drop_zero] using instantiation)
  exact ⟨rest, instantiation, ⟨suffix⟩, suffixTr⟩

end VInductDecl

namespace ConstructorValidation
open AddInductive TypeChecker VEnv

theorem TrExprS.IsUnique.liftLooseBVars
    (unique : TrExprS.IsUnique expression) :
    TrExprS.IsUnique (expression.liftLooseBVars' start amount) := by
  induction expression generalizing start with
  | bvar index => trivial
  | fvar | mvar | sort | const | lit => trivial
  | app function argument functionIH argumentIH =>
      exact ⟨functionIH unique.1, argumentIH unique.2⟩
  | lam name domain body binderInfo domainIH bodyIH
  | forallE name domain body binderInfo domainIH bodyIH =>
      exact ⟨domainIH unique.1, bodyIH unique.2⟩
  | letE name type value body nondep typeIH valueIH bodyIH =>
      exact ⟨valueIH unique.1, bodyIH unique.2⟩
  | mdata data expression ih => exact ih unique
  | proj => cases unique

theorem TrExprS.IsUnique.instantiate1'
    (expressionUnique : TrExprS.IsUnique expression)
    (argumentUnique : TrExprS.IsUnique argument) :
    TrExprS.IsUnique (expression.instantiate1' argument depth) := by
  induction expression generalizing depth with
  | bvar index =>
      simp only [Expr.instantiate1']
      split
      · trivial
      · split
        · exact liftLooseBVars argumentUnique
        · trivial
  | fvar | mvar | sort | const | lit => trivial
  | app function argument functionIH argumentIH =>
      exact ⟨functionIH expressionUnique.1,
        argumentIH expressionUnique.2⟩
  | lam name domain body binderInfo domainIH bodyIH
  | forallE name domain body binderInfo domainIH bodyIH =>
      exact ⟨domainIH expressionUnique.1,
        bodyIH expressionUnique.2⟩
  | letE name type value body nondep typeIH valueIH bodyIH =>
      exact ⟨valueIH expressionUnique.1,
        bodyIH expressionUnique.2⟩
  | mdata data expression ih => exact ih expressionUnique
  | proj => cases expressionUnique

theorem TrExprS.IsUnique.instantiate1
    (expressionUnique : TrExprS.IsUnique expression)
    (argumentUnique : TrExprS.IsUnique argument) :
    TrExprS.IsUnique (expression.instantiate1 argument) := by
  rw [Expr.instantiate1_eq]
  exact instantiate1' expressionUnique argumentUnique

theorem FVarsIn.consumeTypeAnnotations
    (scope : FVarsIn predicate source) :
    FVarsIn predicate (AddInductive.consumeTypeAnnotations source) := by
  fun_induction AddInductive.consumeTypeAnnotations source <;>
    simp_all [FVarsIn]

theorem instantiateFamilyParameters_unique
    (sourceUnique : TrExprS.IsUnique source)
    (parametersUnique : ∀ parameter ∈ parameters,
      TrExprS.IsUnique parameter)
    (run : AddInductive.instantiateFamilyParameters source parameters =
      .ok rest) :
    TrExprS.IsUnique rest := by
  induction parameters generalizing source with
  | nil =>
      have source_eq : source = rest := Except.ok.inj run
      simpa only [source_eq] using sourceUnique
  | cons parameter parameters ih =>
      cases source <;>
        simp only [AddInductive.instantiateFamilyParameters] at run
      case forallE name domain body binderInfo =>
        exact ih (ConstructorValidation.TrExprS.IsUnique.instantiate1 sourceUnique.2
          (parametersUnique parameter (.head parameters)))
          (fun candidate member =>
            parametersUnique candidate (.tail parameter member)) run
      all_goals exact nomatch run

theorem CandidateParameterContext.parametersUnique
    (parameters : CandidateParameterContext base sources types final) :
    ∀ source ∈ sources, TrExprS.IsUnique source := by
  induction parameters with
  | nil => simp
  | cons tail ih =>
      intro source member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih source member

/-- The semantic context invariants shared while D3 and D2 consume the
ordinary prefix of one analyzer-owned constructor view. -/
structure ConstructorOrdinaryContextState
    (env typeEnv : VEnv) (Us : List Name)
    (base actual view postActual : VLCtx) (lift : Lift) where
  baseWF : VLCtx.WF env Us.length base
  actualWF : VLCtx.WF env Us.length actual
  postWF : VLCtx.WF typeEnv Us.length postActual
  postRelation : VLCtx.IsDefEqFVars typeEnv Us.length actual postActual
  viewDefEq : VLCtx.IsDefEq env Us.length actual view
  viewUnique : TrExprS.IsUniqueCtx actual view
  viewLift : VLCtx.FVLift' base view 0 lift 0

/-- Extend the synchronized ordinary-prefix invariant by the exact analyzer
field selected by strict translation.  D3 and D2 may retain different
dependency metadata, but use the same operational fresh identifier. -/
theorem ConstructorOrdinaryContextState.push
    {env typeEnv : VEnv} {Us : List Name}
    {base actual view postActual : VLCtx} {lift : Lift}
    (state : ConstructorOrdinaryContextState env typeEnv Us
      base actual view postActual lift)
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    {source : Expr} {analyzer actualSource actualConsumed postConsumed : VExpr}
    {fieldLevel consumedLevel : VLevel} {fv : FVarId}
    {deps actualDeps postDeps : List FVarId}
    (sourceUnique : TrExprS.IsUnique source)
    (sourceTr : TrExprS typeEnv Us base source analyzer)
    (actualTr : TrExprS env Us actual source actualSource)
    (actualAnnotations : env.IsDefEqU Us.length actual.toCtx
      actualSource actualConsumed)
    (actualConsumedType : env.HasType Us.length actual.toCtx actualConsumed
      (.sort consumedLevel))
    (analyzerType : env.HasType Us.length base.toCtx analyzer
      (.sort fieldLevel))
    (depsSubset : deps ⊆ base.fvars)
    (actualTailWF : VLCtx.WF env Us.length
      ((some (fv, actualDeps), .vlam actualConsumed) :: actual))
    (actualDeps_eq : actualDeps = deps)
    (postTailWF : VLCtx.WF typeEnv Us.length
      ((some (fv, postDeps), .vlam postConsumed) :: postActual))
    (consumedEq : typeEnv.IsDefEq Us.length actual.toCtx
      actualConsumed postConsumed (.sort consumedLevel)) :
    ConstructorOrdinaryContextState env typeEnv Us
      ((some (fv, deps), .vlam analyzer) :: base)
      ((some (fv, actualDeps), .vlam actualConsumed) :: actual)
      ((some (fv, deps), .vlam (analyzer.lift' lift)) :: view)
      ((some (fv, postDeps), .vlam postConsumed) :: postActual)
      (.consN lift 1) := by
  subst actualDeps
  have viewWF : VLCtx.WF env Us.length view :=
    (state.viewDefEq.symm henv.ordered).wf
  have analyzerAtView : TrExprS typeEnv Us view source
      (analyzer.lift' lift) :=
    sourceTr.weakFV' typeEnvWF.ordered state.viewLift
      (viewWF.mono addType)
  have actualSource_eq : actualSource =
      analyzer.lift' lift :=
    (actualTr.mono addType).unique' state.viewUnique sourceUnique
      analyzerAtView
  have consumedToAnalyzer : env.IsDefEq Us.length actual.toCtx
      actualConsumed (analyzer.lift' lift)
      (.sort consumedLevel) := by
    rw [← actualSource_eq]
    exact (actualAnnotations.of_r henv state.actualWF.toCtx
      actualConsumedType).symm
  have freshBase : fv ∉ base.fvars := by
    intro present
    have presentView : fv ∈ view.fvars :=
      state.viewLift.fvars_sublist.subset present
    have presentActual : fv ∈ actual.fvars := by
      simpa only [state.viewDefEq.fvars] using presentView
    exact (actualTailWF.2.1 fv deps rfl).1 presentActual
  have baseTailWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam analyzer) :: base) :=
    ⟨state.baseWF,
      fun _ _ equality => by
        cases equality
        exact ⟨freshBase, depsSubset⟩,
      ⟨fieldLevel, analyzerType⟩⟩
  have nextViewDefEq : VLCtx.IsDefEq env Us.length
      ((some (fv, deps), .vlam actualConsumed) :: actual)
      ((some (fv, deps), .vlam (analyzer.lift' lift)) :: view) :=
    .cons state.viewDefEq actualTailWF.2.1 (.vlam consumedToAnalyzer)
  exact {
    baseWF := baseTailWF
    actualWF := actualTailWF
    postWF := postTailWF
    postRelation := .cons_fvar state.postRelation (.vlam consumedEq)
    viewDefEq := nextViewDefEq
    viewUnique := state.viewUnique.cons .vlam
    viewLift := state.viewLift.cons_fvar (fv, deps) (.vlam analyzer)
      depsSubset }

private theorem vexpr_appArgs_acc (expression : VExpr) (suffix : List VExpr) :
    VExpr.appArgs expression suffix =
      VExpr.appArgs expression [] ++ suffix := by
  induction expression generalizing suffix with
  | app function argument ihFunction ihArgument =>
      simp only [VExpr.appArgs]
      rw [ihFunction, ihFunction (suffix := [argument])]
      simp
  | bvar | sort | const | lam | forallE => simp [VExpr.appArgs]

private theorem expr_getAppArgsList_acc (expression : Expr)
    (suffix : List Expr) :
    expression.getAppArgsList suffix =
      expression.getAppArgsList [] ++ suffix := by
  induction expression generalizing suffix with
  | app function argument ihFunction ihArgument =>
      simp only [Expr.getAppArgsList]
      rw [ihFunction, ihFunction (suffix := [argument])]
      simp
  | bvar | fvar | mvar | sort | const | lit | mdata | proj | lam | forallE |
      letE => simp [Expr.getAppArgsList]

theorem TrExprS.IsUnique.getAppArgsList
    (unique : TrExprS.IsUnique expression) :
    ∀ argument ∈ expression.getAppArgsList,
      TrExprS.IsUnique argument := by
  induction expression with
  | app function argument functionIH argumentIH =>
      intro candidate member
      rw [Expr.getAppArgsList, expr_getAppArgsList_acc] at member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact functionIH unique.1 candidate member
      · exact unique.2
  | bvar | fvar | mvar | sort | const | lit | mdata | proj | lam | forallE |
      letE => simp [Expr.getAppArgsList]

theorem Closed.getAppArgsList
    (closed : Closed expression depth) :
    ∀ argument ∈ expression.getAppArgsList,
      Closed argument depth := by
  induction expression with
  | app function argument functionIH argumentIH =>
      intro candidate member
      rw [Expr.getAppArgsList, expr_getAppArgsList_acc] at member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact functionIH closed.1 candidate member
      · exact closed.2
  | bvar | fvar | mvar | sort | const | lit | mdata | proj | lam | forallE |
      letE => simp [Expr.getAppArgsList]

private theorem vexpr_appHead_appN (head : VExpr) (arguments : List VExpr) :
    VExpr.appHead (VExpr.appN head arguments) = VExpr.appHead head := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [VExpr.appN]
      rw [ih]
      rfl

private def vexprLiftTel (lift : Lift) : List VExpr → List VExpr
  | [] => []
  | domain :: domains =>
      domain.lift' lift :: vexprLiftTel lift.cons domains

private theorem vexpr_lift'_forallN (lift : Lift) :
    ∀ (domains : List VExpr) (body : VExpr),
      (VExpr.forallN domains body).lift' lift =
        VExpr.forallN (vexprLiftTel lift domains)
          (body.lift' (lift.consN domains.length))
  | [], _ => rfl
  | domain :: domains, body => by
      simp only [VExpr.forallN, VExpr.lift', vexprLiftTel,
        List.length_cons]
      rw [vexpr_lift'_forallN lift.cons domains body]
      congr 2
      rw [show domains.length + 1 = 1 + domains.length by omega,
        ← Lift.consN_consN]
      rfl

private theorem vexprLiftTel_length (lift : Lift) :
    ∀ domains : List VExpr,
      (vexprLiftTel lift domains).length = domains.length
  | [] => rfl
  | _ :: domains => by
      simp only [vexprLiftTel, List.length_cons,
        vexprLiftTel_length lift.cons domains]

private theorem forall₂_append
    (left : List.Forall₂ relation leftSources leftTargets)
    (right : List.Forall₂ relation rightSources rightTargets) :
    List.Forall₂ relation (leftSources ++ rightSources)
      (leftTargets ++ rightTargets) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

private theorem forall₂_length
    (run : List.Forall₂ relation sources targets) :
    sources.length = targets.length := by
  induction run with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem forall₂_translation_unique
    (left : List.Forall₂ (TrExprS env Us context) sources leftTargets)
    (right : List.Forall₂ (TrExprS env Us context) sources rightTargets)
    (unique : ∀ source ∈ sources, TrExprS.IsUnique source) :
    leftTargets = rightTargets := by
  induction left generalizing rightTargets with
  | nil => cases right; rfl
  | @cons source leftTarget sources leftTargets leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail =>
          rw [leftHead.unique (unique source (.head sources)) rightHead,
            ih rightTail (fun candidate member =>
              unique candidate (.tail source member))]

theorem forall₂_drop
    (run : List.Forall₂ relation sources targets) (n : Nat) :
    List.Forall₂ relation (sources.drop n) (targets.drop n) := by
  induction n generalizing sources targets with
  | zero => simpa using run
  | succ n ih =>
      cases run with
      | nil => exact .nil
      | cons head tail => simpa using ih tail

theorem forall₂_tr_weakFV'
    {env : VEnv} {Us : List Name} {base full : VLCtx}
    {lift : Lift} (henv : VEnv.Ordered env)
    (extension : VLCtx.FVLift' base full 0 lift 0)
    (fullWF : VLCtx.WF env Us.length full)
    (run : List.Forall₂ (TrExprS env Us base) sources targets) :
    List.Forall₂ (TrExprS env Us full) sources
      (targets.map fun target => target.lift' lift) := by
  induction run with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (by simpa using head.weakFV' henv extension fullWF) ih

theorem forall₂_tr_mono
    (add : env ≤ env')
    (run : List.Forall₂ (TrExprS env Us context) sources targets) :
    List.Forall₂ (TrExprS env' Us context) sources targets := by
  induction run with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.mono add) ih

theorem isValidIndAppIdx_shape
    {stats : AddInductive.InductiveStats} {source : Expr}
    {familyIdx : Nat}
    (valid : AddInductive.isValidIndAppIdx stats source familyIdx = true) :
    (source.getAppFn == stats.indConsts[familyIdx]!) = true ∧
      source.getAppArgs.size =
        stats.params.size + stats.nindices[familyIdx]! := by
  unfold AddInductive.isValidIndAppIdx at valid
  rw [Expr.withApp_eq] at valid
  simp only [Id.run] at valid
  split at valid
  · rename_i shape
    simpa only [Bool.and_eq_true, beq_iff_eq] using shape
  · simp_all

theorem isValidIndAppIdx_indexArgs_length
    {stats : AddInductive.InductiveStats} {source : Expr}
    {familyIdx : Nat}
    (valid : AddInductive.isValidIndAppIdx stats source familyIdx = true) :
    (source.getAppArgs.toList.drop stats.params.size).length =
      stats.nindices[familyIdx]! := by
  have shape := isValidIndAppIdx_shape valid
  rw [List.length_drop, Array.length_toList, shape.2]
  omega

theorem constructorIndependentOf_fvars
    {source : Expr} {full base removed : List FVarId}
    (scope : FVarsIn (· ∈ full) source)
    (independent : AddInductive.constructorIndependentOf source removed = true)
    (remaining : ∀ fv, fv ∈ full → fv ∉ removed → fv ∈ base) :
    FVarsIn (· ∈ base) source := by
  rw [fvarsIn_iff] at scope ⊢
  refine ⟨?_, scope.2⟩
  intro fv member
  apply remaining fv (scope.1 fv member)
  unfold AddInductive.constructorIndependentOf at independent
  simp only [List.all_eq_true] at independent
  have omitted := independent fv member
  simpa using omitted

/-- Strict translation preserves a constant-headed application spine and
translates its arguments position-for-position. -/
theorem TrExprS.constApp_components
    {env : VEnv} {Us : List Name} {context : VLCtx}
    {source : Expr} {target : VExpr} {name : Name} {levels : List Level}
    (run : TrExprS env Us context source target)
    (head : source.getAppFn = .const name levels) :
    ∃ levels',
      VExpr.appHead target = .const name levels' ∧
      List.Forall₂ (TrExprS env Us context)
        source.getAppArgsList (VExpr.appArgs target []) := by
  induction source generalizing target with
  | const sourceName sourceLevels =>
      cases run with
      | const lookup levelsTr arity =>
          simp only [Expr.getAppFn] at head
          obtain ⟨rfl, rfl⟩ := head
          exact ⟨_, rfl, .nil⟩
  | app function argument functionIH argumentIH =>
      cases run with
      | app =>
          rename_i function' domain' body' argument' functionType argumentType
            functionTr argumentTr
          have functionHead : function.getAppFn = .const name levels := by
            simpa only [Expr.getAppFn] using head
          obtain ⟨levels', targetHead, argumentsTr⟩ :=
            functionIH functionTr functionHead
          refine ⟨levels', ?_, ?_⟩
          · simpa only [VExpr.appHead] using targetHead
          · rw [show VExpr.appArgs (.app function' argument') [] =
              VExpr.appArgs function' [] ++ [argument'] by
                rw [VExpr.appArgs, vexpr_appArgs_acc]]
            simp only [Expr.getAppArgsList] at *
            rw [expr_getAppArgsList_acc]
            exact forall₂_append argumentsTr (.cons argumentTr .nil)
  | bvar => cases run; simp [Expr.getAppFn] at head
  | fvar => cases run; simp [Expr.getAppFn] at head
  | mvar => cases run
  | sort => cases run; simp [Expr.getAppFn] at head
  | lam => cases run; simp [Expr.getAppFn] at head
  | forallE => cases run; simp [Expr.getAppFn] at head
  | letE => cases run; simp [Expr.getAppFn] at head
  | lit => cases run; simp [Expr.getAppFn] at head
  | mdata => cases run; simp [Expr.getAppFn] at head
  | proj => cases run; simp [Expr.getAppFn] at head

/-- Remove one verified free-variable context extension from a list of strict
translations, retaining the exact lifted endpoints. -/
theorem TrExprS.forall₂_weakFV_inv
    {env : VEnv} {Us : List Name} {base full : VLCtx}
    {sources : List Expr} {targets : List VExpr} {n : Lift}
    (henv : VEnv.WF env) (fullWF : VLCtx.WF env Us.length full)
    (extension : VLCtx.FVLift' base full 0 n 0)
    (runs : List.Forall₂ (TrExprS env Us full) sources targets)
    (closed : ∀ source ∈ sources, Closed source)
    (fvars : ∀ source ∈ sources, FVarsIn (· ∈ base.fvars) source)
    (unique : ∀ source ∈ sources, TrExprS.IsUnique source) :
    ∃ baseTargets,
      List.Forall₂ (TrExprS env Us base) sources baseTargets ∧
      targets = baseTargets.map (fun target => target.lift' (n.consN 0)) := by
  induction runs with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons source target sources targets headRun tailRuns ih =>
      have headClosed := closed source (.head sources)
      have headFVars := fvars source (.head sources)
      have headUnique := unique source (.head sources)
      have tailClosed : ∀ expression ∈ sources, Closed expression :=
        fun expression member => closed expression (.tail source member)
      have tailFVars : ∀ expression ∈ sources,
          FVarsIn (· ∈ base.fvars) expression :=
        fun expression member => fvars expression (.tail source member)
      have tailUnique : ∀ expression ∈ sources,
          TrExprS.IsUnique expression :=
        fun expression member => unique expression (.tail source member)
      obtain ⟨headBase, headBaseRun⟩ :=
        headRun.weakFV'_inv henv extension (.refl henv fullWF)
          headClosed headFVars
      obtain ⟨tailBase, tailBaseRuns, tailEq⟩ :=
        ih tailClosed tailFVars tailUnique
      have headEq : target = headBase.lift' (n.consN 0) :=
        headRun.unique headUnique
          (headBaseRun.weakFV' henv.ordered extension fullWF)
      subst target
      exact ⟨headBase :: tailBase, .cons headBaseRun tailBaseRuns, by
        simp only [List.map_cons, tailEq]⟩

/-- Remove a free-variable extension modulo the verified context equality
used by the retained checker run. -/
theorem TrExprS.forall₂_weakFV_inv_defeq
    {env : VEnv} {Us : List Name} {base actual view : VLCtx}
    {sources : List Expr} {targets : List VExpr} {n : Lift}
    (henv : VEnv.WF env)
    (viewDefEq : VLCtx.IsDefEq env Us.length actual view)
    (viewUnique : TrExprS.IsUniqueCtx actual view)
    (extension : VLCtx.FVLift' base view 0 n 0)
    (runs : List.Forall₂ (TrExprS env Us actual) sources targets)
    (closed : ∀ source ∈ sources, Closed source)
    (fvars : ∀ source ∈ sources, FVarsIn (· ∈ base.fvars) source)
    (unique : ∀ source ∈ sources, TrExprS.IsUnique source) :
    ∃ baseTargets,
      List.Forall₂ (TrExprS env Us base) sources baseTargets ∧
      targets = baseTargets.map (fun target => target.lift' (n.consN 0)) := by
  have viewWF : VLCtx.WF env Us.length view :=
    (viewDefEq.symm henv.ordered).wf
  induction runs with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons source target sources targets headRun tailRuns ih =>
      have headClosed := closed source (.head sources)
      have headFVars := fvars source (.head sources)
      have headUnique := unique source (.head sources)
      have tailClosed : ∀ expression ∈ sources, Closed expression :=
        fun expression member => closed expression (.tail source member)
      have tailFVars : ∀ expression ∈ sources,
          FVarsIn (· ∈ base.fvars) expression :=
        fun expression member => fvars expression (.tail source member)
      have tailUnique : ∀ expression ∈ sources,
          TrExprS.IsUnique expression :=
        fun expression member => unique expression (.tail source member)
      obtain ⟨headBase, headBaseRun⟩ :=
        headRun.weakFV'_inv henv extension viewDefEq
          headClosed headFVars
      obtain ⟨tailBase, tailBaseRuns, tailEq⟩ :=
        ih tailClosed tailFVars tailUnique
      have headEq : target = headBase.lift' (n.consN 0) :=
        headRun.unique' viewUnique headUnique
          (headBaseRun.weakFV' henv.ordered extension viewWF)
      subst target
      exact ⟨headBase :: tailBase, .cons headBaseRun tailBaseRuns, by
        simp only [List.map_cons, tailEq]⟩

theorem ConstructorPreFamilyIndexSpineSemanticRun.expected_eq_of_family_lift
    {env : VEnv} {Us : List Name} {context : AddInductive.Context}
    {contextRun : AddInductive.ConstructorContextRun env Us context}
    {expected : Expr} {arguments : List Expr}
    {trace : AddInductive.ConstructorPreFamilyIndexSpineTrace context expected
      arguments}
    {expected' : VExpr}
    (run : AddInductive.ConstructorPreFamilyIndexSpineSemanticRun env Us
      context contextRun trace expected')
    {base view : VLCtx} {expectedBase : VExpr} {lift : Lift}
    (familyTr : TrExprS env Us base expected expectedBase)
    (unique : TrExprS.IsUnique expected)
    (extension : VLCtx.FVLift' base view 0 lift 0)
    (viewDefEq : VLCtx.IsDefEq env Us.length
      contextRun.candidate.context.vlctx view)
    (viewUnique : TrExprS.IsUniqueCtx
      contextRun.candidate.context.vlctx view) :
    expected' = expectedBase.lift' (lift.consN 0) := by
  have henv : VEnv.Ordered env := by
    simpa only [contextRun.venv_eq] using
      contextRun.candidate.context.Ewf.ordered
  have viewWF : VLCtx.WF env Us.length view :=
    (viewDefEq.symm henv).wf
  have familyAtView : TrExprS env Us view expected
      (expectedBase.lift' (lift.consN 0)) :=
    familyTr.weakFV' henv extension viewWF
  have retained : TrExprS env Us contextRun.candidate.context.vlctx
      expected expected' := run.expectedRun.expr_tr
  exact retained.unique' viewUnique unique familyAtView

theorem VLCtx.FVLift'.toCtxLiftN
    {base view : VLCtx} {n : Nat}
    (extension : VLCtx.FVLift' base view 0 (.skipN .refl n) 0) :
    Ctx.LiftN n 0 base.toCtx view.toCtx := by
  exact Ctx.liftN_iff_lift'.2 extension.toCtx

/-- Transport a spine to the canonical view context and then remove the
free-variable extension from all of its endpoints. -/
theorem VEnv.SpineWF.fvLift_inv
    {env : VEnv} {U n : Nat} {base actual view : VLCtx}
    {arguments : List VExpr} {source target : VExpr}
    (henv : VEnv.WF env)
    (viewDefEq : VLCtx.IsDefEq env U actual view)
    (extension : VLCtx.FVLift' base view 0 (.skipN .refl n) 0)
    (run : env.SpineWF U actual.toCtx (source.liftN n 0)
      (arguments.map fun argument => argument.liftN n 0)
      (target.liftN n 0)) :
    env.SpineWF U base.toCtx source arguments target := by
  have viewWF : VLCtx.WF env U view :=
    (viewDefEq.symm henv.ordered).wf
  have viewRun : env.SpineWF U view.toCtx (source.liftN n 0)
      (arguments.map fun argument => argument.liftN n 0)
      (target.liftN n 0) :=
    run.defeqDFC henv.ordered viewDefEq.defeqCtx
  exact VEnv.SpineWF.weakN_inv henv viewWF.toCtx
    (Ctx.liftN_iff_lift'.2 extension.toCtx) viewRun

theorem VEnv.SpineWF.fvLift'_inv
    {env : VEnv} {U : Nat} {lift : Lift} {base actual view : VLCtx}
    {arguments : List VExpr} {source target : VExpr}
    (henv : VEnv.WF env)
    (viewDefEq : VLCtx.IsDefEq env U actual view)
    (extension : VLCtx.FVLift' base view 0 lift 0)
    (run : env.SpineWF U actual.toCtx (source.lift' (lift.consN 0))
      (arguments.map fun argument => argument.lift' (lift.consN 0))
      (target.lift' (lift.consN 0))) :
    env.SpineWF U base.toCtx source arguments target := by
  have viewWF : VLCtx.WF env U view :=
    (viewDefEq.symm henv.ordered).wf
  have viewRun : env.SpineWF U view.toCtx
      (source.lift' (lift.consN 0))
      (arguments.map fun argument => argument.lift' (lift.consN 0))
      (target.lift' (lift.consN 0)) :=
    run.defeqDFC henv.ordered viewDefEq.defeqCtx
  exact VEnv.SpineWF.weak'_inv henv viewWF.toCtx extension.toCtx viewRun

/-- Identify a pre-family index replay with the analyzer family telescope,
remove the family-index locals, and retarget its terminal to the family sort. -/
theorem ConstructorPreFamilyIndexSpineSemanticRun.baseSpine
    {env : VEnv} {Us : List Name} {context : AddInductive.Context}
    {contextRun : AddInductive.ConstructorContextRun env Us context}
    {expected : Expr} {arguments : List Expr}
    {trace : AddInductive.ConstructorPreFamilyIndexSpineTrace context expected
      arguments}
    {expected' : VExpr} {base view : VLCtx} {indices : List VExpr}
    {level : VLevel} {n : Nat}
    (run : AddInductive.ConstructorPreFamilyIndexSpineSemanticRun env Us
      context contextRun trace expected')
    (familyTr : TrExprS env Us base expected
      (VExpr.forallN indices (.sort level)))
    (expectedUnique : TrExprS.IsUnique expected)
    (viewDefEq : VLCtx.IsDefEq env Us.length
      contextRun.candidate.context.vlctx view)
    (viewUnique : TrExprS.IsUniqueCtx
      contextRun.candidate.context.vlctx view)
    (extension : VLCtx.FVLift' base view 0 (.skipN .refl n) 0)
    (argumentClosed : ∀ argument ∈ arguments, Closed argument)
    (argumentFVars : ∀ argument ∈ arguments,
      FVarsIn (· ∈ base.fvars) argument)
    (argumentUnique : ∀ argument ∈ arguments,
      TrExprS.IsUnique argument)
    (argumentLength : arguments.length = indices.length) :
    ∃ indices',
      List.Forall₂ (TrExprS env Us base) arguments indices' ∧
      env.SpineWF Us.length base.toCtx
        (VExpr.forallN indices (.sort level)) indices' (.sort level) := by
  have henv : VEnv.WF env := by
    simpa only [contextRun.venv_eq] using
      contextRun.candidate.context.Ewf
  have expectedEq : expected' =
      (VExpr.forallN indices (.sort level)).liftN n 0 :=
    run.expected_eq_of_family familyTr expectedUnique extension viewDefEq
      viewUnique
  subst expected'
  obtain ⟨indices', indicesTr, indicesEq⟩ :=
    TrExprS.forall₂_weakFV_inv_defeq henv viewDefEq viewUnique
      extension run.arguments_tr argumentClosed argumentFVars argumentUnique
  have translatedLength : run.arguments'.length =
      (VExpr.liftTelN n indices 0).length := by
    rw [← forall₂_length run.arguments_tr, argumentLength,
      VExpr.liftTelN_length]
  have liftedSpine : env.SpineWF Us.length
      contextRun.candidate.context.vlctx.toCtx
      ((VExpr.forallN indices (.sort level)).liftN n 0)
      run.arguments' (.sort level) := by
    have sourceEq :
        (VExpr.forallN indices (.sort level)).liftN n 0 =
          VExpr.forallN (VExpr.liftTelN n indices 0) (.sort level) := by
      rw [VExpr.liftN_forallN]
      rfl
    have spine : env.SpineWF Us.length
        contextRun.candidate.context.vlctx.toCtx
        (VExpr.forallN (VExpr.liftTelN n indices 0) (.sort level))
        run.arguments' run.result' :=
      sourceEq ▸ run.spine
    have retargeted := spine.retarget translatedLength (.sort level)
    have sortClosed : (VExpr.sort level).ClosedN 0 := by trivial
    have targetEq : (VExpr.sort level).instRev run.arguments' =
        .sort level := VExpr.instRev_closedN run.arguments' sortClosed
    rw [targetEq] at retargeted
    exact Eq.mpr (congrArg (fun source => env.SpineWF Us.length
      contextRun.candidate.context.vlctx.toCtx source run.arguments'
        (.sort level)) sourceEq) retargeted
  simp only [VExpr.lift'_consN_skipN] at indicesEq
  rw [indicesEq] at liftedSpine
  exact ⟨indices', indicesTr, by
    apply VEnv.SpineWF.fvLift_inv henv viewDefEq extension
    simpa only [VExpr.liftN] using liftedSpine⟩

theorem ConstructorPreFamilyIndexSpineSemanticRun.baseSpine_lift
    {env : VEnv} {Us : List Name} {context : AddInductive.Context}
    {contextRun : AddInductive.ConstructorContextRun env Us context}
    {expected : Expr} {arguments : List Expr}
    {trace : AddInductive.ConstructorPreFamilyIndexSpineTrace context expected
      arguments}
    {expected' : VExpr} {base view : VLCtx} {indices : List VExpr}
    {level : VLevel} {lift : Lift}
    (run : AddInductive.ConstructorPreFamilyIndexSpineSemanticRun env Us
      context contextRun trace expected')
    (familyTr : TrExprS env Us base expected
      (VExpr.forallN indices (.sort level)))
    (expectedUnique : TrExprS.IsUnique expected)
    (viewDefEq : VLCtx.IsDefEq env Us.length
      contextRun.candidate.context.vlctx view)
    (viewUnique : TrExprS.IsUniqueCtx
      contextRun.candidate.context.vlctx view)
    (extension : VLCtx.FVLift' base view 0 lift 0)
    (argumentClosed : ∀ argument ∈ arguments, Closed argument)
    (argumentFVars : ∀ argument ∈ arguments,
      FVarsIn (· ∈ base.fvars) argument)
    (argumentUnique : ∀ argument ∈ arguments,
      TrExprS.IsUnique argument)
    (argumentLength : arguments.length = indices.length) :
    ∃ indices',
      List.Forall₂ (TrExprS env Us base) arguments indices' ∧
      env.SpineWF Us.length base.toCtx
        (VExpr.forallN indices (.sort level)) indices' (.sort level) := by
  have henv : VEnv.WF env := by
    simpa only [contextRun.venv_eq] using
      contextRun.candidate.context.Ewf
  have expectedEq : expected' =
      (VExpr.forallN indices (.sort level)).lift' (lift.consN 0) :=
    expected_eq_of_family_lift run familyTr expectedUnique extension
      viewDefEq viewUnique
  subst expected'
  obtain ⟨indices', indicesTr, indicesEq⟩ :=
    TrExprS.forall₂_weakFV_inv_defeq henv viewDefEq viewUnique
      extension run.arguments_tr argumentClosed argumentFVars argumentUnique
  have translatedLength : run.arguments'.length =
      (vexprLiftTel (lift.consN 0) indices).length := by
    rw [← forall₂_length run.arguments_tr, argumentLength,
      vexprLiftTel_length]
  have liftedSpine : env.SpineWF Us.length
      contextRun.candidate.context.vlctx.toCtx
      ((VExpr.forallN indices (.sort level)).lift' (lift.consN 0))
      run.arguments' (.sort level) := by
    have sourceEq :
        (VExpr.forallN indices (.sort level)).lift' (lift.consN 0) =
          VExpr.forallN (vexprLiftTel (lift.consN 0) indices)
            (.sort level) := by
      rw [vexpr_lift'_forallN]
      rfl
    have spine : env.SpineWF Us.length
        contextRun.candidate.context.vlctx.toCtx
        (VExpr.forallN (vexprLiftTel (lift.consN 0) indices) (.sort level))
        run.arguments' run.result' :=
      sourceEq ▸ run.spine
    have retargeted := spine.retarget translatedLength (.sort level)
    have sortClosed : (VExpr.sort level).ClosedN 0 := by trivial
    have targetEq : (VExpr.sort level).instRev run.arguments' =
        .sort level := VExpr.instRev_closedN run.arguments' sortClosed
    rw [targetEq] at retargeted
    exact Eq.mpr (congrArg (fun source => env.SpineWF Us.length
      contextRun.candidate.context.vlctx.toCtx source run.arguments'
        (.sort level)) sourceEq) retargeted
  rw [indicesEq] at liftedSpine
  exact ⟨indices', indicesTr, by
    apply VEnv.SpineWF.fvLift'_inv henv viewDefEq extension
    simpa only [VExpr.lift'] using liftedSpine⟩

/-- Recover the exact analyzer-selected source type and its checker-selected
sort after removing a verified free-variable context extension. -/
theorem ensureTypeRun_baseType
    {env typeEnv : VEnv} {Us : List Name}
    {base actual view : VLCtx} {source : Expr}
    {source' actual' : VExpr} {fieldLevel : VLevel} {n : Lift}
    (henv : VEnv.WF env) (typeEnvOrdered : VEnv.Ordered typeEnv)
    (addType : env ≤ typeEnv)
    (_baseWF : VLCtx.WF env Us.length base)
    (viewDefEq : VLCtx.IsDefEq env Us.length actual view)
    (viewUnique : TrExprS.IsUniqueCtx actual view)
    (viewLift : VLCtx.FVLift' base view 0 n 0)
    (sourceUnique : TrExprS.IsUnique source)
    (sourceClosed : Closed source)
    (sourceFVars : FVarsIn (· ∈ base.fvars) source)
    (sourceTr : TrExprS typeEnv Us base source source')
    (actualTr : TrExprS env Us actual source actual')
    (actualType : env.HasType Us.length actual.toCtx actual' (.sort fieldLevel)) :
    env.HasType Us.length base.toCtx source' (.sort fieldLevel) := by
  obtain ⟨base', baseTr⟩ :=
    actualTr.weakFV'_inv henv viewLift viewDefEq sourceClosed sourceFVars
  have baseEq : base' = source' :=
    (baseTr.mono addType).unique sourceUnique sourceTr
  subst base'
  have viewWF : VLCtx.WF env Us.length view :=
    (viewDefEq.symm henv.ordered).wf
  have sourceAtView := sourceTr
  have sourceAtView' : TrExprS typeEnv Us view source
      (source'.lift' (n.consN 0)) :=
    sourceAtView.weakFV' typeEnvOrdered viewLift (viewWF.mono addType)
  have actualEq : actual' = source'.lift' (n.consN 0) := by
    exact (actualTr.mono addType).unique' viewUnique sourceUnique sourceAtView'
  have sourceTypeAtView : env.HasType Us.length view.toCtx
      actual' (.sort fieldLevel) :=
    actualType.defeqDFC henv.ordered viewDefEq.defeqCtx
  rw [actualEq] at sourceTypeAtView
  exact (HasType.weak'_iff henv viewWF.toCtx viewLift.toCtx).1 (by
    simpa using sourceTypeAtView)

theorem ensureTypeRun_baseType_mono
    {env typeEnv : VEnv} {Us : List Name}
    {base actual view : VLCtx} {source : Expr}
    {source' actual' : VExpr} {fieldLevel : VLevel} {n : Lift}
    (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    (baseWF : VLCtx.WF env Us.length base)
    (viewDefEq : VLCtx.IsDefEq env Us.length actual view)
    (viewUnique : TrExprS.IsUniqueCtx actual view)
    (viewLift : VLCtx.FVLift' base view 0 n 0)
    (sourceUnique : TrExprS.IsUnique source)
    (sourceClosed : Closed source)
    (sourceFVars : FVarsIn (· ∈ base.fvars) source)
    (sourceTr : TrExprS typeEnv Us base source source')
    (actualTr : TrExprS env Us actual source actual')
    (actualType : typeEnv.HasType Us.length actual.toCtx actual'
      (.sort fieldLevel)) :
    typeEnv.HasType Us.length base.toCtx source' (.sort fieldLevel) := by
  exact ensureTypeRun_baseType typeEnvWF
    typeEnvWF.ordered VEnv.LE.rfl
    (baseWF.mono addType) (viewDefEq.mono addType) viewUnique viewLift
    sourceUnique sourceClosed sourceFVars sourceTr (actualTr.mono addType)
    actualType

/-- Recover a family-free base endpoint when the analyzer translation lives
under a different prefix than D3's index-extended replay context. -/
theorem ensureTypeRun_commonType
    {env typeEnv : VEnv} {Us : List Name}
    {base full actual view : VLCtx} {source : Expr}
    {fullTarget actualTarget : VExpr} {fieldLevel : VLevel}
    {fullLift viewLift : Lift}
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    (baseWF : VLCtx.WF env Us.length base)
    (fullWF : VLCtx.WF typeEnv Us.length full)
    (fullExtension : VLCtx.FVLift' base full 0 fullLift 0)
    (viewDefEq : VLCtx.IsDefEq env Us.length actual view)
    (viewUnique : TrExprS.IsUniqueCtx actual view)
    (viewExtension : VLCtx.FVLift' base view 0 viewLift 0)
    (sourceUnique : TrExprS.IsUnique source)
    (sourceClosed : Closed source)
    (sourceFVars : FVarsIn (· ∈ base.fvars) source)
    (fullTr : TrExprS typeEnv Us full source fullTarget)
    (actualTr : TrExprS env Us actual source actualTarget)
    (actualType : env.HasType Us.length actual.toCtx actualTarget
      (.sort fieldLevel)) :
    ∃ baseTarget,
      TrExprS typeEnv Us base source baseTarget ∧
      fullTarget = baseTarget.lift' fullLift ∧
      env.HasType Us.length base.toCtx baseTarget (.sort fieldLevel) := by
  obtain ⟨baseTarget, baseTr⟩ := fullTr.weakFV'_inv typeEnvWF
    fullExtension (.refl typeEnvWF.ordered fullWF) sourceClosed sourceFVars
  have fullEq : fullTarget = baseTarget.lift' fullLift :=
    fullTr.unique sourceUnique
      (baseTr.weakFV' typeEnvWF.ordered fullExtension fullWF)
  have baseType := ensureTypeRun_baseType
    henv typeEnvWF.ordered
    addType baseWF viewDefEq viewUnique viewExtension sourceUnique
    sourceClosed sourceFVars baseTr actualTr actualType
  exact ⟨baseTarget, baseTr, fullEq, baseType⟩

/-- D2 types the exact analyzer-owned field in the synthetic full field
context and relates it to the declaration actually pushed by validation. -/
theorem analyzerField_postType
    {typeEnv : VEnv} {Us : List Name}
    {full postActual : VLCtx} {source : Expr}
    {analyzer postRaw postView postConsumed : VExpr}
    {rawLevel : VLevel}
    (typeEnvWF : VEnv.WF typeEnv)
    (fullWF : VLCtx.WF typeEnv Us.length full)
    (postWF : VLCtx.WF typeEnv Us.length postActual)
    (relation : VLCtx.IsDefEqFVars typeEnv Us.length full postActual)
    (analyzerTr : TrExprS typeEnv Us full source analyzer)
    (postViewTr : TrExprS typeEnv Us postActual source postView)
    (postRawType : typeEnv.HasType Us.length postActual.toCtx postRaw
      (.sort rawLevel))
    (postRawView : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw postView)
    (postAnnotations : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw postConsumed) :
    typeEnv.HasType Us.length full.toCtx analyzer (.sort rawLevel) ∧
      typeEnv.IsDefEq Us.length full.toCtx analyzer postConsumed
        (.sort rawLevel) := by
  have postViewType : typeEnv.HasType Us.length postActual.toCtx postView
      (.sort rawLevel) :=
    postRawType.defeqU_l typeEnvWF postWF.toCtx postRawView
  have postViewAtFull : typeEnv.HasType Us.length full.toCtx postView
      (.sort rawLevel) :=
    postViewType.defeqDFC typeEnvWF.ordered
      (relation.defeqCtx.symm typeEnvWF.ordered)
  have analyzerViewU : typeEnv.IsDefEqU Us.length full.toCtx
      analyzer postView :=
    analyzerTr.uniqFVars typeEnvWF relation fullWF postViewTr
  have analyzerView := analyzerViewU.of_r typeEnvWF fullWF.toCtx
    postViewAtFull
  have rawViewAtFull := postRawView.defeqDFC typeEnvWF.ordered
    (relation.defeqCtx.symm typeEnvWF.ordered)
  have rawConsumedAtFull := postAnnotations.defeqDFC typeEnvWF.ordered
    (relation.defeqCtx.symm typeEnvWF.ordered)
  have rawTypeAtFull := postRawType.defeqDFC typeEnvWF.ordered
    (relation.defeqCtx.symm typeEnvWF.ordered)
  have rawConsumed := rawConsumedAtFull.of_l typeEnvWF fullWF.toCtx
    rawTypeAtFull
  have analyzerConsumed := analyzerView.trans
    ((rawViewAtFull.of_l typeEnvWF fullWF.toCtx rawTypeAtFull).symm.trans
      rawConsumed)
  exact ⟨analyzerView.hasType.1, analyzerConsumed⟩

structure AnalyzerPostContextState
    (typeEnv : VEnv) (Us : List Name)
    (full postActual postView : VLCtx) (viewLift : Lift) where
  fullWF : VLCtx.WF typeEnv Us.length full
  postWF : VLCtx.WF typeEnv Us.length postActual
  viewWF : VLCtx.WF typeEnv Us.length postView
  viewDefEq : VLCtx.IsDefEqFVars typeEnv Us.length postActual postView
  viewExtension : VLCtx.FVLift' full postView 0 viewLift 0

def vlctxCons
    (entry : Option (FVarId × List FVarId) × VLocalDecl)
    (tail : VLCtx) : VLCtx :=
  entry :: tail

theorem VLCtx.IsDefEqFVars.fvars
    (relation : VLCtx.IsDefEqFVars env U left right) :
    left.fvars = right.fvars := by
  induction relation with
  | nil => rfl
  | cons_bvar relation declaration ih =>
      change _ = _
      exact ih
  | cons_fvar relation declaration ih =>
      change _ :: _ = _ :: _
      exact congrArg (fun tail => _ :: tail) ih

theorem VLCtx.IsDefEqFVars.mono
    (add : env ≤ env') :
    VLCtx.IsDefEqFVars env U left right →
      VLCtx.IsDefEqFVars env' U left right := by
  intro relation
  induction relation with
  | nil => exact .nil
  | cons_bvar relation declaration ih =>
      exact .cons_bvar ih (declaration.mono add)
  | cons_fvar relation declaration ih =>
      exact .cons_fvar ih (declaration.mono add)

theorem VLCtx.IsDefEqFVars.symm
    (henv : VEnv.Ordered env) :
    VLCtx.IsDefEqFVars env U left right →
      VLCtx.IsDefEqFVars env U right left := by
  intro relation
  induction relation with
  | nil => exact .nil
  | cons_bvar relation declaration ih =>
      exact .cons_bvar ih
        (declaration.symm.defeqDFC henv relation.defeqCtx)
  | cons_fvar relation declaration ih =>
      exact .cons_fvar ih
        (declaration.symm.defeqDFC henv relation.defeqCtx)

def FullFreshInvariant (context : AddInductive.Context)
    (common full : VLCtx) : Prop :=
  ∀ fv ∈ full.fvars,
    fv ∈ common.fvars ∨ context.ngen.Reserves fv

theorem FullFreshInvariant.fresh
    (invariant : FullFreshInvariant context common full)
    (freshCommon : context.freshFVarId ∉ common.fvars) :
    context.freshFVarId ∉ full.fvars := by
  intro present
  rcases invariant context.freshFVarId present with common | reserved
  · exact freshCommon common
  · exact NameGenerator.not_reserves_self reserved

theorem FullFreshInvariant.push
    (invariant : FullFreshInvariant context common full)
    {commonDomain fullDomain : VLocalDecl}
    {commonDeps fullDeps : List FVarId} :
    FullFreshInvariant
      (context.pushLocalDecl name binderInfo sourceDomain)
      (vlctxCons
        (some (context.freshFVarId, commonDeps), commonDomain) common)
      (vlctxCons
        (some (context.freshFVarId, fullDeps), fullDomain) full) := by
  intro fv present
  simp only [vlctxCons, VLCtx.fvars_cons_some, List.mem_cons] at present
  rcases present with rfl | present
  · exact .inl (by simp [vlctxCons])
  · rcases invariant fv present with commonMem | reserved
    · exact .inl (by
        simp only [vlctxCons, VLCtx.fvars_cons_some, List.mem_cons]
        exact .inr commonMem)
    · exact .inr (reserved.mono NameGenerator.LE.next)

theorem FullFreshInvariant.skip
    (invariant : FullFreshInvariant context common full)
    {fullDomain : VLocalDecl} {fullDeps : List FVarId} :
    FullFreshInvariant context.advanceFresh common
      (vlctxCons
        (some (context.freshFVarId, fullDeps), fullDomain) full) := by
  intro fv present
  simp only [vlctxCons, VLCtx.fvars_cons_some, List.mem_cons] at present
  rcases present with rfl | present
  · exact .inr NameGenerator.next_reserves_self
  · rcases invariant fv present with common | reserved
    · exact .inl common
    · exact .inr (reserved.mono NameGenerator.LE.next)

structure D3FullContextState
    (env typeEnv : VEnv) (Us : List Name)
    (context : AddInductive.Context)
    (common full actual view : VLCtx) (fullLift viewLift : Lift) where
  commonWF : VLCtx.WF env Us.length common
  commonNoBV : common.NoBV
  fullWF : VLCtx.WF typeEnv Us.length full
  fullExtension : VLCtx.FVLift' common full 0 fullLift 0
  actualWF : VLCtx.WF env Us.length actual
  viewDefEq : VLCtx.IsDefEq env Us.length actual view
  viewUnique : TrExprS.IsUniqueCtx actual view
  viewExtension : VLCtx.FVLift' common view 0 viewLift 0
  freshInvariant : FullFreshInvariant context common full

/-- Push one family-free D3 binder through both the analyzer's full context
and D3's index-extended context. -/
theorem D3FullContextState.push
    {env typeEnv : VEnv} {Us : List Name}
    {context : AddInductive.Context}
    {common full actual view : VLCtx} {fullLift viewLift : Lift}
    (state : D3FullContextState env typeEnv Us context
      common full actual view fullLift viewLift)
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    {source : Expr}
    {fullTarget actualSource actualConsumed : VExpr}
    {fieldLevel consumedLevel : VLevel}
    (sourceUnique : TrExprS.IsUnique source)
    (sourceClosed : Closed source)
    (sourceFVars : FVarsIn (· ∈ common.fvars) source)
    (fullTr : TrExprS typeEnv Us full source fullTarget)
    (actualTr : TrExprS env Us actual source actualSource)
    (actualType : env.HasType Us.length actual.toCtx actualSource
      (.sort fieldLevel))
    (actualAnnotations : env.IsDefEqU Us.length actual.toCtx
      actualSource actualConsumed)
    (actualConsumedType : env.HasType Us.length actual.toCtx actualConsumed
      (.sort consumedLevel))
    (actualTailWF : VLCtx.WF env Us.length
      (vlctxCons
        (some (context.freshFVarId,
          (consumeTypeAnnotations source).fvarsList),
          .vlam actualConsumed) actual)) :
    ∃ commonTarget,
      TrExprS typeEnv Us common source commonTarget ∧
      fullTarget = commonTarget.lift' fullLift ∧
      env.HasType Us.length common.toCtx commonTarget (.sort fieldLevel) ∧
      D3FullContextState env typeEnv Us
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations source))
        (vlctxCons
          (some (context.freshFVarId,
            (consumeTypeAnnotations source).fvarsList),
            .vlam commonTarget) common)
        (vlctxCons
          (some (context.freshFVarId,
            (consumeTypeAnnotations source).fvarsList),
            .vlam fullTarget) full)
        (vlctxCons
          (some (context.freshFVarId,
            (consumeTypeAnnotations source).fvarsList),
            .vlam actualConsumed) actual)
        (vlctxCons
          (some (context.freshFVarId,
            (consumeTypeAnnotations source).fvarsList),
            .vlam (commonTarget.lift' viewLift)) view)
        (.consN fullLift 1) (.consN viewLift 1) := by
  obtain ⟨commonTarget, commonTr, fullEq, commonType⟩ :=
    ensureTypeRun_commonType henv typeEnvWF addType state.commonWF
      state.fullWF state.fullExtension state.viewDefEq state.viewUnique
      state.viewExtension sourceUnique sourceClosed sourceFVars fullTr
      actualTr actualType
  have viewWF : VLCtx.WF env Us.length view :=
    (state.viewDefEq.symm henv.ordered).wf
  have commonAtView : TrExprS typeEnv Us view source
      (commonTarget.lift' viewLift) :=
    commonTr.weakFV' typeEnvWF.ordered state.viewExtension
      (viewWF.mono addType)
  have actualSource_eq : actualSource = commonTarget.lift' viewLift :=
    (actualTr.mono addType).unique' state.viewUnique sourceUnique commonAtView
  have consumedToCommon : env.IsDefEq Us.length actual.toCtx
      actualConsumed (commonTarget.lift' viewLift)
      (.sort consumedLevel) := by
    rw [← actualSource_eq]
    exact (actualAnnotations.of_r henv state.actualWF.toCtx
      actualConsumedType).symm
  have depsSubset : (consumeTypeAnnotations source).fvarsList ⊆
      common.fvars :=
    (FVarsIn.consumeTypeAnnotations sourceFVars |> fvarsIn_iff.mp).1
  have freshCommon : context.freshFVarId ∉ common.fvars := by
    intro present
    have presentView := state.viewExtension.fvars_sublist.subset present
    have presentActual : context.freshFVarId ∈ actual.fvars := by
      simpa only [state.viewDefEq.fvars] using presentView
    exact (actualTailWF.2.1 _ _ rfl).1 presentActual
  have freshFull := state.freshInvariant.fresh freshCommon
  have commonTailWF : VLCtx.WF env Us.length
      (vlctxCons
        (some (context.freshFVarId,
          (consumeTypeAnnotations source).fvarsList),
          .vlam commonTarget) common) := by
    refine ⟨state.commonWF, ?_, ⟨fieldLevel, commonType⟩⟩
    intro fv deps equality
    cases equality
    exact ⟨freshCommon, depsSubset⟩
  have fullType : typeEnv.HasType Us.length full.toCtx fullTarget
      (.sort fieldLevel) := by
    rw [fullEq]
    exact (commonType.weak' henv.ordered state.fullExtension.toCtx).mono addType
  have fullTailWF : VLCtx.WF typeEnv Us.length
      (vlctxCons
        (some (context.freshFVarId,
          (consumeTypeAnnotations source).fvarsList),
          .vlam fullTarget) full) := by
    refine ⟨state.fullWF, ?_, ⟨fieldLevel, fullType⟩⟩
    intro fv deps equality
    cases equality
    exact ⟨freshFull, fun fv member =>
      state.fullExtension.fvars_sublist.subset (depsSubset member)⟩
  have nextViewDefEq : VLCtx.IsDefEq env Us.length
      (vlctxCons
        (some (context.freshFVarId,
          (consumeTypeAnnotations source).fvarsList),
          .vlam actualConsumed) actual)
      (vlctxCons
        (some (context.freshFVarId,
          (consumeTypeAnnotations source).fvarsList),
          .vlam (commonTarget.lift' viewLift)) view) := by
    exact .cons state.viewDefEq actualTailWF.2.1
      (.vlam consumedToCommon)
  refine ⟨commonTarget, commonTr, fullEq, commonType, {
    commonWF := commonTailWF
    commonNoBV := by
      simpa only [vlctxCons, VLCtx.NoBV, VLCtx.bvars] using
        state.commonNoBV
    fullWF := fullTailWF
    fullExtension := ?_
    actualWF := actualTailWF
    viewDefEq := nextViewDefEq
    viewUnique := state.viewUnique.cons .vlam
    viewExtension := state.viewExtension.cons_fvar
      (context.freshFVarId,
        (consumeTypeAnnotations source).fvarsList)
      (.vlam commonTarget) depsSubset
    freshInvariant := state.freshInvariant.push }⟩
  simpa only [fullEq, vlctxCons, VLocalDecl.lift',
    VLocalDecl.depth] using state.fullExtension.cons_fvar
    (context.freshFVarId,
      (consumeTypeAnnotations source).fvarsList)
    (.vlam commonTarget) depsSubset

/-- Skip one family-dependent outer field in D3's family-free replay while
retaining that exact analyzer field in the full context. -/
theorem D3FullContextState.skip
    {env typeEnv : VEnv} {Us : List Name}
    {context : AddInductive.Context}
    {common full actual view : VLCtx} {fullLift viewLift : Lift}
    (state : D3FullContextState env typeEnv Us context
      common full actual view fullLift viewLift)
    {source : Expr} {field : VExpr}
    (nextFullWF : VLCtx.WF typeEnv Us.length
      ((some (context.freshFVarId,
          (consumeTypeAnnotations source).fvarsList),
        .vlam field) :: full)) :
    D3FullContextState env typeEnv Us context.advanceFresh common
      ((some (context.freshFVarId,
          (consumeTypeAnnotations source).fvarsList),
        .vlam field) :: full)
      actual view (.skipN fullLift 1) viewLift where
  commonWF := state.commonWF
  commonNoBV := state.commonNoBV
  fullWF := nextFullWF
  fullExtension := by
    simpa only [VLocalDecl.depth] using state.fullExtension.skip_fvar
      (context.freshFVarId,
        (consumeTypeAnnotations source).fvarsList) (.vlam field)
  actualWF := state.actualWF
  viewDefEq := state.viewDefEq
  viewUnique := state.viewUnique
  viewExtension := state.viewExtension
  freshInvariant := state.freshInvariant.skip

/-- Exact analyzer syntax and pre-family semantic evidence for one recursive
field.  The family telescope is tracked at the analyzer's current full
context; nested binders lift it in the ordinary de Bruijn way. -/
def RecursiveFieldRunResult
    (env : VEnv) (Us : List Name) (full : VLCtx)
    (familyTarget fieldTarget : VExpr) (level : VLevel)
    (familyName : Name) (parameterCount : Nat) : Prop :=
  ∃ binders indices terminal,
    fieldTarget = VExpr.forallN binders terminal ∧
    env.OnTel Us.length full.toCtx binders ∧
    env.SpineWF Us.length
      (binders.reverse ++ full.toCtx)
      (familyTarget.liftN binders.length 0) indices (.sort level) ∧
    (∃ levels, VExpr.appHead terminal = .const familyName levels) ∧
    (VExpr.appArgs terminal []).drop parameterCount = indices

/-- Synchronize the recursive D3 replay with the analyzer's exact strict
translation.  D3 supplies all family-free typing and the terminal index
spine; strict translation uniqueness fixes the analyzer-owned domains and
terminal arguments componentwise. -/
theorem recursiveField_exactAnalyzer
    {env typeEnv : VEnv} {Us : List Name}
    {stats : AddInductive.InductiveStats} {familyIdx : Nat}
    {familyIndices : Expr} {context : AddInductive.Context}
    {contextRun : AddInductive.ConstructorContextRun env Us context}
    {source : Expr} {fuel : Nat}
    {trace : AddInductive.ConstructorPreFamilyRecursiveTrace stats familyIdx
      familyIndices context source fuel}
    (run : AddInductive.ConstructorPreFamilyRecursiveSemanticRun env Us stats
      familyIdx familyIndices contextRun trace)
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    {common full view : VLCtx} {fullLift viewLift : Lift}
    (state : D3FullContextState env typeEnv Us context common full
      contextRun.candidate.context.vlctx view fullLift viewLift)
    {commonIndices : List VExpr} {familyTarget fieldTarget : VExpr}
    {level : VLevel} {familyName : Name} {familyLevels : List Level}
    (familyCommonTr : TrExprS env Us common familyIndices
      (VExpr.forallN commonIndices (.sort level)))
    (familyFullTr : TrExprS typeEnv Us full familyIndices familyTarget)
    (familyUnique : TrExprS.IsUnique familyIndices)
    (indexLength : commonIndices.length = stats.nindices[familyIdx]!)
    (familyHead : stats.indConsts[familyIdx]! =
      .const familyName familyLevels)
    (sourceUnique : TrExprS.IsUnique source)
    (sourceClosed : Closed source)
    (sourceFVars : FVarsIn (· ∈ common.fvars) source)
    (fullTr : TrExprS typeEnv Us full source fieldTarget) :
    RecursiveFieldRunResult env Us full familyTarget fieldTarget level
      familyName stats.params.size := by
  induction run generalizing common full view fullLift viewLift commonIndices
      familyTarget fieldTarget with
  | @target _ context source fuel valid spineTrace branchContextRun expected'
      spine =>
      have argumentClosed : ∀ argument ∈
          source.getAppArgs.toList.drop stats.params.size,
          Closed argument := by
        intro argument member
        apply Closed.getAppArgsList sourceClosed
        rw [← Expr.getAppArgs_toList]
        exact List.mem_of_mem_drop member
      have argumentFVars : ∀ argument ∈
          source.getAppArgs.toList.drop stats.params.size,
          FVarsIn (· ∈ common.fvars) argument := by
        intro argument member
        apply FVarsIn.getAppArgsList sourceFVars
        rw [← Expr.getAppArgs_toList]
        exact List.mem_of_mem_drop member
      have argumentUnique : ∀ argument ∈
          source.getAppArgs.toList.drop stats.params.size,
          TrExprS.IsUnique argument := by
        intro argument member
        apply TrExprS.IsUnique.getAppArgsList sourceUnique
        rw [← Expr.getAppArgs_toList]
        exact List.mem_of_mem_drop member
      have argumentLength :
          (source.getAppArgs.toList.drop stats.params.size).length =
            commonIndices.length :=
        (isValidIndAppIdx_indexArgs_length valid).trans
          indexLength.symm
      obtain ⟨baseIndices, baseIndicesTr, baseSpine⟩ :=
        ConstructorPreFamilyIndexSpineSemanticRun.baseSpine_lift spine
          familyCommonTr familyUnique
          state.viewDefEq state.viewUnique state.viewExtension
          argumentClosed argumentFVars argumentUnique argumentLength
      have commonFamilyAtFull : TrExprS typeEnv Us full familyIndices
          ((VExpr.forallN commonIndices (.sort level)).lift' fullLift) := by
        simpa using (familyCommonTr.mono addType).weakFV'
          typeEnvWF.ordered state.fullExtension state.fullWF
      have familyEq : familyTarget =
          (VExpr.forallN commonIndices (.sort level)).lift' fullLift :=
        familyFullTr.unique familyUnique commonFamilyAtFull
      have shape := isValidIndAppIdx_shape valid
      have sourceHead : source.getAppFn =
          .const familyName familyLevels := by
        rw [familyHead] at shape
        change source.getAppFn.eqv (.const familyName familyLevels) = true ∧
          _ at shape
        rw [Expr.eqv_eq] at shape
        generalize headEq : source.getAppFn = head at shape
        cases head <;> simp_all [Expr.eqv']
      obtain ⟨targetLevels, targetHead, allArgumentsTr⟩ :=
        TrExprS.constApp_components fullTr sourceHead
      have droppedArgumentsTr :=
        forall₂_drop allArgumentsTr stats.params.size
      have baseIndicesAtFull : List.Forall₂
          (TrExprS typeEnv Us full)
          (source.getAppArgsList.drop stats.params.size)
          (baseIndices.map fun index => index.lift' fullLift) := by
        have baseMono := forall₂_tr_mono addType baseIndicesTr
        have baseWeak := forall₂_tr_weakFV' typeEnvWF.ordered
          state.fullExtension state.fullWF baseMono
        simpa only [Expr.getAppArgs_toList] using baseWeak
      have translatedIndicesEq :
          (VExpr.appArgs fieldTarget []).drop stats.params.size =
            baseIndices.map fun index => index.lift' fullLift :=
        forall₂_translation_unique droppedArgumentsTr
          baseIndicesAtFull (fun argument member =>
            TrExprS.IsUnique.getAppArgsList sourceUnique argument
              (List.mem_of_mem_drop member))
      have fullSpine : env.SpineWF Us.length full.toCtx
          ((VExpr.forallN commonIndices (.sort level)).lift' fullLift)
          (baseIndices.map fun index => index.lift' fullLift)
          (.sort level) := by
        simpa using VEnv.SpineWF.weak' henv.ordered
          state.fullExtension.toCtx baseSpine
      rw [← familyEq, ← translatedIndicesEq] at fullSpine
      exact ⟨[], (VExpr.appArgs fieldTarget []).drop stats.params.size,
        fieldTarget, rfl, trivial, by simpa using fullSpine,
        ⟨targetLevels, targetHead⟩, rfl⟩
  | @forallE context name domain body binderInfo fuel domainCheck ensureType
      consumedCheck annotations fresh tailTrace branchContextRun domainRun
      consumedRun ensureTypeRun annotationsRun consumedType tail ih =>
      obtain ⟨fullDomain, fullBody, rfl, fullDomainType, fullBodyType,
          domainTr, bodyTr⟩ := TrExprS.forallE_components fullTr
      have actualDomainTr : TrExprS env Us
          branchContextRun.candidate.context.vlctx domain
          domainRun.source' := by
        simpa only [branchContextRun.venv_eq,
          branchContextRun.lparams_eq] using domainRun.check.expr_tr
      have actualDomainType : env.HasType Us.length
          branchContextRun.candidate.context.vlctx.toCtx domainRun.source'
          (.sort ensureTypeRun.resultLevel') := by
        simpa only [branchContextRun.venv_eq,
          branchContextRun.lparams_eq] using ensureTypeRun.source_type
      have actualAnnotations : env.IsDefEqU Us.length
          branchContextRun.candidate.context.vlctx.toCtx domainRun.source'
          consumedRun.source' := by
        simpa only [branchContextRun.venv_eq,
          branchContextRun.lparams_eq] using annotationsRun.isDefEqU
      have consumedTypeCopy := consumedType
      obtain ⟨consumedLevel, consumedHasType⟩ := consumedType
      have actualConsumedType : env.HasType Us.length
          branchContextRun.candidate.context.vlctx.toCtx consumedRun.source'
          (.sort consumedLevel) := by
        simpa only [branchContextRun.venv_eq,
          branchContextRun.lparams_eq] using consumedHasType
      let nextContextRun := branchContextRun.pushLocalDecl name binderInfo
        (consumeTypeAnnotations domain) fresh consumedRun.source'
        consumedRun.check.expr_tr consumedTypeCopy
      have actualTailWF : VLCtx.WF env Us.length
          (vlctxCons
            (some (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList),
              .vlam consumedRun.source')
            branchContextRun.candidate.context.vlctx) := by
        have nextWF := nextContextRun.candidate.context.Δwf
        rw [nextContextRun.venv_eq, nextContextRun.lparams_eq] at nextWF
        simpa only [vlctxCons, nextContextRun,
          AddInductive.ConstructorContextRun.pushLocalDecl,
          CandidateContextRun.pushLocalDecl_vlctx] using nextWF
      obtain ⟨commonDomain, commonDomainTr, fullDomainEq,
          commonDomainType, nextState⟩ :=
        state.push henv typeEnvWF addType sourceUnique.1 sourceClosed.1
          sourceFVars.1 domainTr actualDomainTr actualDomainType
          actualAnnotations actualConsumedType actualTailWF
      have bodyOpened : TrExprS typeEnv Us
          (vlctxCons
            (some (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList),
              .vlam fullDomain) full)
          (body.instantiate1 context.freshExpr) fullBody := by
        simpa only [vlctxCons, AddInductive.Context.freshExpr,
          Expr.instantiate1_eq] using
          bodyTr.inst_fvar typeEnvWF.ordered nextState.fullWF
      have familyCommonNext : TrExprS env Us
          (vlctxCons
            (some (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList),
              .vlam commonDomain) common)
          familyIndices
          (VExpr.forallN (VExpr.liftTelN 1 commonIndices 0)
            (.sort level)) := by
        have weakened := familyCommonTr.weakFV henv.ordered
          (VLCtx.FVLift.skip_fvar
            (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList)
            (.vlam commonDomain) .refl)
          nextState.commonWF
        simpa [vlctxCons, VLocalDecl.depth,
          VExpr.liftN_forallN, VExpr.liftN] using weakened
      have familyFullNext : TrExprS typeEnv Us
          (vlctxCons
            (some (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList),
              .vlam fullDomain) full)
          familyIndices (familyTarget.liftN 1 0) := by
        have weakened := familyFullTr.weakFV typeEnvWF.ordered
          (VLCtx.FVLift.skip_fvar
            (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList)
            (.vlam fullDomain) .refl)
          nextState.fullWF
        simpa [vlctxCons, VLocalDecl.depth] using weakened
      have nextIndexLength :
          (VExpr.liftTelN 1 commonIndices 0).length =
            stats.nindices[familyIdx]! := by
        simpa only [VExpr.liftTelN_length] using indexLength
      have tailUnique : TrExprS.IsUnique
          (body.instantiate1 context.freshExpr) := by
        apply TrExprS.IsUnique.instantiate1 sourceUnique.2
        simp only [AddInductive.Context.freshExpr]
        trivial
      have nextFullNoBV :
          (vlctxCons
            (some (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList),
              .vlam fullDomain) full).bvars = 0 :=
        nextState.fullExtension.bvars_eq.trans nextState.commonNoBV
      have tailClosed : Closed (body.instantiate1 context.freshExpr) := by
        have closed := bodyOpened.closed
        rw [nextFullNoBV] at closed
        exact closed
      have tailFVars : FVarsIn
          (· ∈ (vlctxCons
            (some (context.freshFVarId,
              (consumeTypeAnnotations domain).fvarsList),
              .vlam commonDomain) common).fvars)
          (body.instantiate1 context.freshExpr) := by
        rw [Expr.instantiate1_eq]
        apply FVarsIn.instantiate1
        · exact sourceFVars.2.mono (fun fv member => by
            simp only [vlctxCons, VLCtx.fvars_cons_some,
              List.mem_cons]
            exact .inr member)
        · simp [AddInductive.Context.freshExpr, vlctxCons, FVarsIn]
      obtain ⟨tailBinders, indices, terminal, tailTargetEq, tailOnTel,
          tailSpine, terminalHead, terminalIndices⟩ :=
        ih nextState familyCommonNext familyFullNext nextIndexLength
          tailUnique tailClosed tailFVars bodyOpened
      refine ⟨fullDomain :: tailBinders, indices, terminal, ?_, ?_, ?_,
        terminalHead, terminalIndices⟩
      · simp only [VExpr.forallN, VExpr.forallE.injEq, true_and]
        exact tailTargetEq
      · exact ⟨by
          rw [fullDomainEq]
          exact ⟨ensureTypeRun.resultLevel', by
            simpa using commonDomainType.weak' henv.ordered
              state.fullExtension.toCtx⟩,
          by
            simpa only [vlctxCons, VLCtx.toCtx] using tailOnTel⟩
      · simpa only [List.reverse_cons, List.singleton_append,
          List.append_assoc, vlctxCons, VLCtx.toCtx,
          List.length_cons, VExpr.liftN_liftN, Nat.add_comm] using tailSpine

private theorem forallN_inj_of_terminal_ne_forall
    (leftNot : ∀ domain body, leftTerminal ≠ .forallE domain body)
    (rightNot : ∀ domain body, rightTerminal ≠ .forallE domain body)
    (equality : VExpr.forallN leftBinders leftTerminal =
      VExpr.forallN rightBinders rightTerminal) :
    leftBinders = rightBinders ∧ leftTerminal = rightTerminal := by
  induction leftBinders generalizing rightBinders with
  | nil =>
      cases rightBinders with
      | nil => exact ⟨rfl, equality⟩
      | cons domain binders =>
          exact (leftNot domain (VExpr.forallN binders rightTerminal)
            equality).elim
  | cons domain binders ih =>
      cases rightBinders with
      | nil =>
          exact (rightNot domain (VExpr.forallN binders leftTerminal)
            equality.symm).elim
      | cons rightDomain rightBinders =>
          simp only [VExpr.forallN, VExpr.forallE.injEq] at equality
          obtain ⟨domainEq, tailEq⟩ := equality
          obtain ⟨bindersEq, terminalEq⟩ :=
            ih tailEq
          cases domainEq
          cases bindersEq
          exact ⟨rfl, terminalEq⟩

private theorem terminal_ne_forall_of_appHead_const
    (head : VExpr.appHead terminal = .const familyName levels) :
    ∀ domain body, terminal ≠ .forallE domain body := by
  intro domain body equality
  subst terminal
  simp only [VExpr.appHead] at head
  exact VExpr.noConfusion head

private theorem hasConst_of_appHead_const
    (head : VExpr.appHead terminal = .const familyName levels) :
    terminal.hasConst familyName = true := by
  induction terminal with
  | app function argument functionIH argumentIH =>
      simp only [VExpr.appHead] at head
      simp only [VExpr.hasConst, Bool.or_eq_true]
      exact .inl (functionIH head)
  | const name levels =>
      simp only [VExpr.appHead, VExpr.const.injEq] at head
      exact (beq_iff_eq).2 head.1
  | bvar | sort | lam | forallE => simp [VExpr.appHead] at head

private theorem forallN_hasConst_of_terminal
    (terminalHasConst : terminal.hasConst familyName = true) :
    (VExpr.forallN binders terminal).hasConst familyName = true := by
  induction binders with
  | nil => exact terminalHasConst
  | cons binder binders ih =>
      simp only [VExpr.forallN, VExpr.hasConst, Bool.or_eq_true]
      exact .inr ih

theorem recArg?_eq_none_of_hasConst_false
    (free : field.hasConst familyName = false) :
    VInductDecl.recArg? U familyName np ni fieldIndex field = none := by
  cases recursiveEq : VInductDecl.recArg? U familyName np ni fieldIndex field with
  | none => rfl
  | some recursive =>
      have anatomy := VInductDecl.recArg?_eq recursiveEq
      have terminalHead :
          VExpr.appHead
              (VExpr.appN (.const familyName (VLevel.params U))
                (VExpr.bvarRevRange
                    (fieldIndex + recursive.binders.length) np ++
                  recursive.indices)) =
            .const familyName (VLevel.params U) :=
        VExpr.appHead_appN _ _
      have terminalHasConst :=
        hasConst_of_appHead_const terminalHead
      have recursiveHasConst :=
        forallN_hasConst_of_terminal
          (binders := recursive.binders) terminalHasConst
      rw [← anatomy.2.2.1, free] at recursiveHasConst
      contradiction

private theorem drop_bvarRevRange_append
    (offset count : Nat) (suffix : List VExpr) :
    (VExpr.bvarRevRange offset count ++ suffix).drop count = suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [VExpr.bvarRevRange, List.cons_append, List.drop_succ_cons]
      exact ih

/-- A recursive-field synchronization certificate is exactly the semantic
payload required by the analyzer's `RecArg` descriptor. -/
theorem recursiveFieldResult_recArgWF
    {env : VEnv} {Us : List Name} {full : VLCtx}
    {familyTarget fieldTarget : VExpr} {level : VLevel}
    {familyName : Name} {np ni fieldIndex : Nat}
    {familyIndices : List VExpr}
    (result : RecursiveFieldRunResult env Us full familyTarget
      fieldTarget level familyName np)
    (familyTargetEq : familyTarget =
      VExpr.forallN (VExpr.liftTelN fieldIndex familyIndices 0)
        (.sort level))
    (stage : VInductDecl.stage3Field Us.length familyName np ni fieldIndex
      fieldTarget = true) :
    ∃ recursive,
      VInductDecl.recArg? Us.length familyName np ni fieldIndex fieldTarget =
        some recursive ∧
      recursive.WF Us.length env level familyIndices full.toCtx := by
  obtain ⟨binders, indices, terminal, targetEq, onTel, spine,
      ⟨terminalLevels, terminalHead⟩, terminalIndices⟩ := result
  have terminalHasConst : terminal.hasConst familyName = true :=
    hasConst_of_appHead_const terminalHead
  have fieldHasConst : fieldTarget.hasConst familyName = true := by
    rw [targetEq]
    exact forallN_hasConst_of_terminal terminalHasConst
  have recursiveSome :
      (VInductDecl.recArg? Us.length familyName np ni fieldIndex
        fieldTarget).isSome = true := by
    simpa only [VInductDecl.stage3Field, fieldHasConst, Bool.not_true,
      Bool.or_false] using stage
  cases recursiveEq : VInductDecl.recArg? Us.length familyName np ni
      fieldIndex fieldTarget with
  | none => simp [recursiveEq] at recursiveSome
  | some recursive =>
      have anatomy := VInductDecl.recArg?_eq recursiveEq
      let recursiveTerminal := VExpr.appN
        (.const familyName (VLevel.params Us.length))
        (VExpr.bvarRevRange (fieldIndex + recursive.binders.length) np ++
          recursive.indices)
      have telescopesEq : VExpr.forallN binders terminal =
          VExpr.forallN recursive.binders recursiveTerminal := by
        exact targetEq.symm.trans anatomy.2.2.1
      have recursiveTerminalHead :
          VExpr.appHead recursiveTerminal =
            .const familyName (VLevel.params Us.length) := by
        exact VExpr.appHead_appN _ _
      obtain ⟨bindersEq, terminalEq⟩ :=
        forallN_inj_of_terminal_ne_forall
          (terminal_ne_forall_of_appHead_const terminalHead)
          (terminal_ne_forall_of_appHead_const recursiveTerminalHead)
          telescopesEq
      have indicesEq : indices = recursive.indices := by
        rw [terminalEq, VExpr.appArgs_appN] at terminalIndices
        simp only [VExpr.appArgs, List.append_nil] at terminalIndices
        rw [drop_bvarRevRange_append] at terminalIndices
        exact terminalIndices.symm
      refine ⟨recursive, rfl, ?_⟩
      unfold VInductDecl.RecArg.WF
      refine ⟨?_, ?_⟩
      · rw [← bindersEq]
        exact onTel
      · rw [anatomy.1, ← bindersEq, ← indicesEq]
        rw [familyTargetEq, VExpr.liftN_forallN,
          VExpr.liftTelN_liftTelN] at spine
        simpa [VExpr.liftN] using spine

theorem AnalyzerPostContextState.push
    {typeEnv : VEnv} {Us : List Name}
    {full postActual postViewContext : VLCtx} {viewLift : Lift}
    (state : AnalyzerPostContextState typeEnv Us full postActual
      postViewContext viewLift)
    (typeEnvWF : VEnv.WF typeEnv)
    {source : Expr} {analyzer postRaw postView postConsumed : VExpr}
    {rawLevel : VLevel} {fv : FVarId} {postDeps : List FVarId}
    (_sourceUnique : TrExprS.IsUnique source)
    (_sourceClosed : Closed source)
    (analyzerTr : TrExprS typeEnv Us full source analyzer)
    (postViewTr : TrExprS typeEnv Us postActual source postView)
    (postRawType : typeEnv.HasType Us.length postActual.toCtx postRaw
      (.sort rawLevel))
    (postRawView : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw postView)
    (postAnnotations : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw postConsumed)
    (postTailWF : VLCtx.WF typeEnv Us.length
      ((some (fv, postDeps), .vlam postConsumed) :: postActual)) :
    let deps := (AddInductive.consumeTypeAnnotations source).fvarsList
    typeEnv.HasType Us.length full.toCtx analyzer (.sort rawLevel) ∧
      AnalyzerPostContextState typeEnv Us
        ((some (fv, deps), .vlam analyzer) :: full)
        ((some (fv, postDeps), .vlam postConsumed) :: postActual)
        ((some (fv, deps), .vlam (analyzer.lift' viewLift)) ::
          postViewContext)
        (.consN viewLift 1) := by
  dsimp only
  have postViewType : typeEnv.HasType Us.length postActual.toCtx postView
      (.sort rawLevel) :=
    postRawType.defeqU_l typeEnvWF state.postWF.toCtx postRawView
  have postViewContextWF : VLCtx.WF typeEnv Us.length postViewContext :=
    state.viewWF
  have analyzerAtView : TrExprS typeEnv Us postViewContext source
      (analyzer.lift' viewLift) :=
    analyzerTr.weakFV' typeEnvWF.ordered state.viewExtension
      postViewContextWF
  have postViewAnalyzer : typeEnv.IsDefEqU Us.length postActual.toCtx
      postView (analyzer.lift' viewLift) :=
    postViewTr.uniqFVars typeEnvWF state.viewDefEq state.postWF
      analyzerAtView
  have analyzerAtPostType : typeEnv.HasType Us.length postActual.toCtx
      (analyzer.lift' viewLift) (.sort rawLevel) :=
    (postViewAnalyzer.of_l typeEnvWF state.postWF.toCtx postViewType).hasType.2
  have analyzerAtViewType : typeEnv.HasType Us.length postViewContext.toCtx
      (analyzer.lift' viewLift) (.sort rawLevel) :=
    analyzerAtPostType.defeqDFC typeEnvWF.ordered
      state.viewDefEq.defeqCtx
  have analyzerType : typeEnv.HasType Us.length full.toCtx analyzer
      (.sort rawLevel) :=
    (HasType.weak'_iff typeEnvWF postViewContextWF.toCtx
      state.viewExtension.toCtx).1 (by simpa using analyzerAtViewType)
  have rawView := postRawView.of_l typeEnvWF state.postWF.toCtx postRawType
  have rawConsumed :=
    postAnnotations.of_l typeEnvWF state.postWF.toCtx postRawType
  have analyzerConsumed : typeEnv.IsDefEq Us.length postActual.toCtx
      postConsumed (analyzer.lift' viewLift) (.sort rawLevel) :=
    (rawConsumed.symm.trans rawView).trans
      (postViewAnalyzer.of_l typeEnvWF state.postWF.toCtx postViewType)
  have depsSubset : (AddInductive.consumeTypeAnnotations source).fvarsList ⊆
      full.fvars :=
    (FVarsIn.consumeTypeAnnotations analyzerTr.fvarsIn
      |> fvarsIn_iff.mp).1
  have freshFull : fv ∉ full.fvars := by
    intro present
    have presentView := state.viewExtension.fvars_sublist.subset present
    have presentPost : fv ∈ postActual.fvars := by
      simpa only [ConstructorValidation.VLCtx.IsDefEqFVars.fvars state.viewDefEq]
        using presentView
    exact (postTailWF.2.1 fv postDeps rfl).1 presentPost
  have freshView : fv ∉ postViewContext.fvars := by
    intro present
    have presentPost : fv ∈ postActual.fvars := by
      simpa only [ConstructorValidation.VLCtx.IsDefEqFVars.fvars state.viewDefEq]
        using present
    exact (postTailWF.2.1 fv postDeps rfl).1 presentPost
  have depsSubsetView :
      (AddInductive.consumeTypeAnnotations source).fvarsList ⊆
        postViewContext.fvars := fun _ member =>
    state.viewExtension.fvars_sublist.subset (depsSubset member)
  have fullTailWF : VLCtx.WF typeEnv Us.length
      ((some (fv, (AddInductive.consumeTypeAnnotations source).fvarsList),
        .vlam analyzer) :: full) :=
    ⟨state.fullWF,
      fun _ _ equality => by
        cases equality
        exact ⟨freshFull, depsSubset⟩,
      ⟨rawLevel, analyzerType⟩⟩
  have viewTailWF : VLCtx.WF typeEnv Us.length
      ((some (fv, (AddInductive.consumeTypeAnnotations source).fvarsList),
        .vlam (analyzer.lift' viewLift)) :: postViewContext) :=
    ⟨state.viewWF,
      fun _ _ equality => by
        cases equality
        exact ⟨freshView, depsSubsetView⟩,
      ⟨rawLevel, analyzerAtViewType⟩⟩
  exact ⟨analyzerType, {
    fullWF := fullTailWF
    postWF := postTailWF
    viewWF := viewTailWF
    viewDefEq := .cons_fvar state.viewDefEq (.vlam analyzerConsumed)
    viewExtension := state.viewExtension.cons_fvar
      (fv, (AddInductive.consumeTypeAnnotations source).fvarsList)
      (.vlam analyzer) depsSubset }⟩

theorem ordinaryField_baseTypes
    {env typeEnv : VEnv} {Us : List Name}
    {base actual view postActual : VLCtx} {source : Expr}
    {source' actual' postRaw' postView' : VExpr}
    {fieldLevel rawLevel resultLevel : VLevel} {n : Lift}
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    (baseWF : VLCtx.WF env Us.length base)
    (actualWF : VLCtx.WF env Us.length actual)
    (postWF : VLCtx.WF typeEnv Us.length postActual)
    (postRelation : VLCtx.IsDefEqFVars typeEnv Us.length actual postActual)
    (viewDefEq : VLCtx.IsDefEq env Us.length actual view)
    (viewUnique : TrExprS.IsUniqueCtx actual view)
    (viewLift : VLCtx.FVLift' base view 0 n 0)
    (sourceUnique : TrExprS.IsUnique source)
    (sourceClosed : Closed source)
    (sourceFVars : FVarsIn (· ∈ base.fvars) source)
    (sourceTr : TrExprS typeEnv Us base source source')
    (actualTr : TrExprS env Us actual source actual')
    (actualType : env.HasType Us.length actual.toCtx actual'
      (.sort fieldLevel))
    (postViewTr : TrExprS typeEnv Us postActual source postView')
    (postRawType : typeEnv.HasType Us.length postActual.toCtx postRaw'
      (.sort rawLevel))
    (postRawView : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw' postView')
    (rawBound : resultLevel = .zero ∨ rawLevel ≤ resultLevel) :
    env.HasType Us.length base.toCtx source' (.sort fieldLevel) ∧
      fieldLevel ≈ rawLevel ∧
      (resultLevel = .zero ∨ fieldLevel ≤ resultLevel) := by
  have baseField := ensureTypeRun_baseType henv
    typeEnvWF.ordered addType baseWF viewDefEq viewUnique viewLift
    sourceUnique sourceClosed sourceFVars sourceTr actualTr actualType
  have postViewType : typeEnv.HasType Us.length postActual.toCtx postView'
      (.sort rawLevel) :=
    postRawType.defeqU_l typeEnvWF postWF.toCtx postRawView
  have postViewTypeAtActual : typeEnv.HasType Us.length actual.toCtx
      postView' (.sort rawLevel) :=
    postViewType.defeqDFC typeEnvWF.ordered
      (postRelation.defeqCtx.symm typeEnvWF.ordered)
  have translatedDefEq : typeEnv.IsDefEqU Us.length actual.toCtx
      actual' postView' :=
    (actualTr.mono addType).uniqFVars typeEnvWF postRelation
      (actualWF.mono addType) postViewTr
  have actualRawType : typeEnv.HasType Us.length actual.toCtx actual'
      (.sort rawLevel) :=
    (translatedDefEq.of_r typeEnvWF (actualWF.mono addType).toCtx
      postViewTypeAtActual).hasType.1
  have baseRaw := ensureTypeRun_baseType_mono typeEnvWF addType baseWF
    viewDefEq viewUnique viewLift sourceUnique sourceClosed sourceFVars
    sourceTr actualTr actualRawType
  have levelEq : fieldLevel ≈ rawLevel :=
    (baseField.mono addType).uniqU typeEnvWF (baseWF.mono addType).toCtx
      baseRaw |>.sort_inv typeEnvWF (baseWF.mono addType).toCtx
  refine ⟨baseField, levelEq, ?_⟩
  rcases rawBound with prop | bound
  · exact .inl prop
  · exact .inr (VLevel.le_trans
      (VLevel.le_antisymm_iff.mp levelEq).1 bound)

theorem ordinaryConsumed_defeq
    {env typeEnv : VEnv} {Us : List Name}
    {actual postActual : VLCtx} {source _rawSource _rawConsumed _sourceConsumed : Expr}
    {actualSource' actualConsumed' postRaw' postView' postConsumed' : VExpr}
    (typeEnvWF : VEnv.WF typeEnv) (addType : env ≤ typeEnv)
    (actualWF : VLCtx.WF env Us.length actual)
    (relation : VLCtx.IsDefEqFVars typeEnv Us.length actual postActual)
    (actualSourceTr : TrExprS env Us actual source actualSource')
    (actualAnnotations : env.IsDefEqU Us.length actual.toCtx
      actualSource' actualConsumed')
    (actualConsumedType : env.IsType Us.length actual.toCtx actualConsumed')
    (postViewTr : TrExprS typeEnv Us postActual source postView')
    (postRawView : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw' postView')
    (postAnnotations : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw' postConsumed') :
    ∃ level, typeEnv.IsDefEq Us.length actual.toCtx
      actualConsumed' postConsumed' (.sort level) := by
  have actualWF' := actualWF.mono addType
  have sourceEq : typeEnv.IsDefEqU Us.length actual.toCtx
      actualSource' postView' :=
    (actualSourceTr.mono addType).uniqFVars typeEnvWF relation actualWF'
      postViewTr
  have postToActual := relation.defeqCtx.symm typeEnvWF.ordered
  have rawView := postRawView.defeqDFC typeEnvWF.ordered postToActual
  have rawConsumed := postAnnotations.defeqDFC typeEnvWF.ordered postToActual
  have consumedEq := (actualAnnotations.mono addType).symm.trans typeEnvWF
    actualWF'.toCtx (sourceEq.trans typeEnvWF actualWF'.toCtx
      (rawView.symm.trans typeEnvWF actualWF'.toCtx rawConsumed))
  obtain ⟨level, consumedType⟩ := actualConsumedType
  exact ⟨level, consumedEq.of_l typeEnvWF actualWF'.toCtx
    (consumedType.mono addType)⟩

/-- The terminal kernel sort retained by a candidate recursion translates to
the exact terminal Theory sort exposed by its analyzer-owned view telescope. -/
theorem CandidateExprRun.terminalLevel_tr
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {context : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace context source' view' inferred')
    {resultLevel : Level} {resultLevel' : VLevel} {binders : List VExpr}
    (terminal : trace.terminalResult = .sort resultLevel)
    (viewEq : view' = VExpr.forallN binders (.sort resultLevel'))
    (lengthEq : trace.spineLength = binders.length) :
    VLevel.ofLevel Us resultLevel = some resultLevel' := by
  induction run generalizing binders with
  | terminal node =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at lengthEq
      have bindersEq : binders = [] := List.eq_nil_of_length_eq_zero
        lengthEq.symm
      subst binders
      simp only [VExpr.forallN] at viewEq
      simp only [AddInductive.CandidateExprTrace.terminalResult] at terminal
      rw [terminal, viewEq] at node
      cases node.whnf.rhs_tr with
      | sort levelTr => exact levelTr
  | @forallE domain candidateContext name binderInfo context source inferred
      body source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyContext storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate bodyCandidate
      node domainRun annotationsRun bodyRun domainType bodyType bodySource
      bodyContextEq domainIH bodyIH =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at lengthEq
      cases binders with
      | nil => simp at lengthEq
      | cons binder binders =>
          simp only [VExpr.forallN, VExpr.forallE.injEq] at viewEq
          obtain ⟨_, bodyViewEq⟩ := viewEq
          apply bodyIH terminal bodyViewEq
          simpa only [List.length_cons] using Nat.succ.inj lengthEq

end ConstructorValidation


namespace ConstructorValidation
open AddInductive TypeChecker
-- `VEnv` here resolves to these two namespaces; `_root_.Ix.Theory.Named.VEnv` is
-- shadowed by the enclosing namespace, so name both explicitly.
open _root_.Ix.Theory.Named.ConstructorValidation.VEnv _root_.Ix.Theory.Named.TypeChecker.VEnv

/-- Every full-context free variable not deliberately omitted by D3 is still
present in the family-free common context. -/
def FullRemovedInvariant (common full : VLCtx)
    (removed : List FVarId) : Prop :=
  ∀ fv, fv ∈ full.fvars → fv ∉ removed → fv ∈ common.fvars

theorem FullRemovedInvariant.push
    (invariant : FullRemovedInvariant common full removed) :
    FullRemovedInvariant
      ((some (fv, commonDeps), commonDomain) :: common)
      ((some (fv, fullDeps), fullDomain) :: full) removed := by
  intro candidate present notRemoved
  simp only [VLCtx.fvars_cons_some, List.mem_cons] at present ⊢
  rcases present with rfl | present
  · exact .inl rfl
  · exact .inr (invariant candidate present notRemoved)

theorem FullRemovedInvariant.skip
    (invariant : FullRemovedInvariant common full removed)
    (fresh : fv ∉ full.fvars) :
    FullRemovedInvariant common
      ((some (fv, fullDeps), fullDomain) :: full) (fv :: removed) := by
  intro candidate present notRemoved
  simp only [VLCtx.fvars_cons_some, List.mem_cons] at present
  rcases present with rfl | present
  · exact (notRemoved (by simp)).elim
  · exact invariant candidate present (fun old => notRemoved (by simp [old]))

theorem Context.freshFVarId_eq_of_ngen_eq
    {left right : AddInductive.Context}
    (equal : left.ngen = right.ngen) :
    left.freshFVarId = right.freshFVarId := by
  simp only [AddInductive.Context.freshFVarId, equal]

theorem Context.push_advance_ngen_eq
    {left right : AddInductive.Context}
    (equal : left.ngen = right.ngen) :
    (left.pushLocalDecl name binderInfo domain).ngen =
      right.advanceFresh.ngen := by
  simp only [AddInductive.Context.pushLocalDecl,
    AddInductive.Context.advanceFresh, equal]

theorem ordinaryConsumed_defeqAt
    {env typeEnv : VEnv} {Us : List Name}
    {actual postActual : VLCtx} {source : Expr}
    {actualSource' actualConsumed' postRaw' postView' postConsumed' : VExpr}
    {consumedLevel : VLevel}
    (typeEnvWF : VEnv.WF typeEnv) (addType : env ≤ typeEnv)
    (actualWF : VLCtx.WF env Us.length actual)
    (relation : VLCtx.IsDefEqFVars typeEnv Us.length actual postActual)
    (actualSourceTr : TrExprS env Us actual source actualSource')
    (actualAnnotations : env.IsDefEqU Us.length actual.toCtx
      actualSource' actualConsumed')
    (actualConsumedType : env.HasType Us.length actual.toCtx actualConsumed'
      (.sort consumedLevel))
    (postViewTr : TrExprS typeEnv Us postActual source postView')
    (postRawView : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw' postView')
    (postAnnotations : typeEnv.IsDefEqU Us.length postActual.toCtx
      postRaw' postConsumed') :
    typeEnv.IsDefEq Us.length actual.toCtx
      actualConsumed' postConsumed' (.sort consumedLevel) := by
  have actualWF' := actualWF.mono addType
  have sourceEq : typeEnv.IsDefEqU Us.length actual.toCtx
      actualSource' postView' :=
    (actualSourceTr.mono addType).uniqFVars typeEnvWF relation actualWF'
      postViewTr
  have postToActual := relation.defeqCtx.symm typeEnvWF.ordered
  have rawView := postRawView.defeqDFC typeEnvWF.ordered postToActual
  have rawConsumed := postAnnotations.defeqDFC typeEnvWF.ordered postToActual
  have consumedEq := (actualAnnotations.mono addType).symm.trans typeEnvWF
    actualWF'.toCtx (sourceEq.trans typeEnvWF actualWF'.toCtx
      (rawView.symm.trans typeEnvWF actualWF'.toCtx rawConsumed))
  exact consumedEq.of_l typeEnvWF actualWF'.toCtx
    (actualConsumedType.mono addType)

theorem ConstructorUniverseTrace.bound
    {stats : AddInductive.InductiveStats}
    {sortResult : Expr}
    (trace : AddInductive.ConstructorUniverseTrace stats.resultLevel
      sortResult.sortLevel!)
    (valid : trace.semantic = true)
    (resultLevelTr : VLevel.ofLevel Us stats.resultLevel = some resultLevel)
    (ensureTypeRun : TypeChecker.EnsureTypeRun typeEnv Us postContext
      source sortResult source') :
    resultLevel = .zero ∨ ensureTypeRun.resultLevel' ≤ resultLevel := by
  apply AddInductive.constructorUniverseSemanticGe_ofLevel valid resultLevelTr
  have sortLevelEq : sortResult.sortLevel! = ensureTypeRun.resultLevel := by
    simpa only [Expr.sortLevel!] using
      congrArg Expr.sortLevel! ensureTypeRun.result_eq
  rw [sortLevelEq]
  exact ensureTypeRun.resultLevel_tr

/-- D3's terminal index replay transported to the analyzer's exact full
context and exact translated result target. -/
theorem terminal_exactAnalyzer
    {env typeEnv : VEnv} {Us : List Name}
    {stats : AddInductive.InductiveStats} {familyIdx : Nat}
    {familyIndices : Expr} {context : AddInductive.Context}
    {contextRun : AddInductive.ConstructorContextRun env Us context}
    {source : Expr}
    {valid : AddInductive.isValidIndAppIdx stats source familyIdx = true}
    {spineTrace : AddInductive.ConstructorPreFamilyIndexSpineTrace context
      familyIndices (source.getAppArgs.toList.drop stats.params.size)}
    {expected' : VExpr}
    (spine : AddInductive.ConstructorPreFamilyIndexSpineSemanticRun env Us
      context contextRun spineTrace expected')
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    {common full view : VLCtx} {fullLift viewLift : Lift}
    (state : D3FullContextState env typeEnv Us context common full
      contextRun.candidate.context.vlctx view fullLift viewLift)
    {commonIndices : List VExpr} {familyTarget resultTarget : VExpr}
    {level : VLevel} {familyName : Name} {familyLevels : List Level}
    (familyCommonTr : TrExprS env Us common familyIndices
      (VExpr.forallN commonIndices (.sort level)))
    (familyFullTr : TrExprS typeEnv Us full familyIndices familyTarget)
    (familyUnique : TrExprS.IsUnique familyIndices)
    (indexLength : commonIndices.length = stats.nindices[familyIdx]!)
    (familyHead : stats.indConsts[familyIdx]! =
      .const familyName familyLevels)
    (sourceUnique : TrExprS.IsUnique source)
    (sourceClosed : Closed source)
    (sourceFVars : FVarsIn (· ∈ common.fvars) source)
    (fullTr : TrExprS typeEnv Us full source resultTarget) :
    env.SpineWF Us.length full.toCtx familyTarget
      (VInductDecl.recFieldIdxs stats.params.size resultTarget)
      (.sort level) := by
  have argumentClosed : ∀ argument ∈
      source.getAppArgs.toList.drop stats.params.size,
      Closed argument := by
    intro argument member
    apply Closed.getAppArgsList sourceClosed
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop member
  have argumentFVars : ∀ argument ∈
      source.getAppArgs.toList.drop stats.params.size,
      FVarsIn (· ∈ common.fvars) argument := by
    intro argument member
    apply FVarsIn.getAppArgsList sourceFVars
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop member
  have argumentUnique : ∀ argument ∈
      source.getAppArgs.toList.drop stats.params.size,
      TrExprS.IsUnique argument := by
    intro argument member
    apply TrExprS.IsUnique.getAppArgsList sourceUnique
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop member
  have argumentLength :
      (source.getAppArgs.toList.drop stats.params.size).length =
        commonIndices.length :=
    (isValidIndAppIdx_indexArgs_length valid).trans indexLength.symm
  obtain ⟨baseIndices, baseIndicesTr, baseSpine⟩ :=
    ConstructorPreFamilyIndexSpineSemanticRun.baseSpine_lift
      spine familyCommonTr familyUnique state.viewDefEq state.viewUnique
      state.viewExtension argumentClosed argumentFVars argumentUnique
      argumentLength
  have commonFamilyAtFull : TrExprS typeEnv Us full familyIndices
      ((VExpr.forallN commonIndices (.sort level)).lift' fullLift) := by
    simpa using (familyCommonTr.mono addType).weakFV'
      typeEnvWF.ordered state.fullExtension state.fullWF
  have familyEq : familyTarget =
      (VExpr.forallN commonIndices (.sort level)).lift' fullLift :=
    familyFullTr.unique familyUnique commonFamilyAtFull
  have shape := isValidIndAppIdx_shape valid
  have sourceHead : source.getAppFn = .const familyName familyLevels := by
    rw [familyHead] at shape
    change source.getAppFn.eqv (.const familyName familyLevels) = true ∧ _
      at shape
    rw [Expr.eqv_eq] at shape
    generalize headEq : source.getAppFn = head at shape
    cases head <;> simp_all [Expr.eqv']
  obtain ⟨targetLevels, targetHead, allArgumentsTr⟩ :=
    TrExprS.constApp_components fullTr sourceHead
  have droppedArgumentsTr :=
    forall₂_drop allArgumentsTr stats.params.size
  have baseIndicesAtFull : List.Forall₂ (TrExprS typeEnv Us full)
      (source.getAppArgsList.drop stats.params.size)
      (baseIndices.map fun index => index.lift' fullLift) := by
    have baseMono := forall₂_tr_mono addType baseIndicesTr
    have baseWeak := forall₂_tr_weakFV' typeEnvWF.ordered
      state.fullExtension state.fullWF baseMono
    simpa only [Expr.getAppArgs_toList] using baseWeak
  have translatedIndicesEq :
      (VExpr.appArgs resultTarget []).drop stats.params.size =
        baseIndices.map fun index => index.lift' fullLift :=
    forall₂_translation_unique droppedArgumentsTr baseIndicesAtFull
      (fun argument member =>
        TrExprS.IsUnique.getAppArgsList sourceUnique argument
          (List.mem_of_mem_drop member))
  have fullSpine : env.SpineWF Us.length full.toCtx
      ((VExpr.forallN commonIndices (.sort level)).lift' fullLift)
      (baseIndices.map fun index => index.lift' fullLift) (.sort level) := by
    simpa using VEnv.SpineWF.weak' henv.ordered
      state.fullExtension.toCtx baseSpine
  rw [← familyEq, ← translatedIndicesEq] at fullSpine
  simpa only [VInductDecl.recFieldIdxs] using fullSpine

def ConstructorFieldsRunResult
    (env : VEnv) (Us : List Name) (full : VLCtx)
    (familyTarget : VExpr) (level : VLevel) (familyName : Name)
    (parameters : Nat) (familyIndices fields : List VExpr)
    (fieldIndex : Nat) (resultTarget : VExpr) : Prop :=
  VInductDecl.fieldsWF Us.length familyName parameters env level familyIndices
      full.toCtx fieldIndex fields ∧
    env.SpineWF Us.length (fields.reverse ++ full.toCtx)
      (familyTarget.liftN fields.length 0)
      (VInductDecl.recFieldIdxs parameters resultTarget) (.sort level)

/-- Synchronize the exact D3 family-free replay with D2's analyzer-owned
constructor view, deriving every field judgment and the terminal index spine. -/
theorem constructorFields_exactAnalyzer
    {env typeEnv : VEnv} {Us : List Name}
    {stats : AddInductive.InductiveStats} {familyIdx : Nat}
    {familyIndices : Expr}
    {d3Context d2Context : AddInductive.Context}
    {d3ContextRun : AddInductive.ConstructorContextRun env Us d3Context}
    {d2ContextRun : AddInductive.ConstructorContextRun typeEnv Us d2Context}
    {view : Expr} {argIdx : Nat} {removed : List FVarId}
    {recursiveStarted : Bool}
    {d3Trace : AddInductive.ConstructorPreFamilyViewTrace stats familyIdx
      familyIndices d3Context view argIdx removed recursiveStarted}
    (d3 : AddInductive.ConstructorPreFamilyViewSemanticRun env Us stats
      familyIdx familyIndices d3ContextRun d3Trace)
    {isUnsafe : Bool} {ctorName : Name} {rawSource : Expr}
    {d2Fuel whnfFuel : Nat}
    {d2Trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctorName d2Context rawSource argIdx d2Fuel}
    (d2Alignment : AddInductive.ConstructorViewAlignmentTrace d2Trace view)
    (d2 : AddInductive.ConstructorViewSemanticRun typeEnv Us whnfFuel
      d2ContextRun d2Trace view)
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    {common full d3ViewContext analyzerViewContext : VLCtx}
    {fullLift viewLift analyzerViewLift : Lift}
    (d3State : D3FullContextState env typeEnv Us d3Context common full
      d3ContextRun.candidate.context.vlctx d3ViewContext fullLift viewLift)
    (analyzerState : AnalyzerPostContextState typeEnv Us full
      d2ContextRun.candidate.context.vlctx analyzerViewContext
      analyzerViewLift)
    (removedInvariant : FullRemovedInvariant common full removed)
    (ngenEq : d3Context.ngen = d2Context.ngen)
    {commonIndices checkedIndices fields : List VExpr}
    {familyTarget resultTarget : VExpr} {level : VLevel}
    {familyName : Name} {familyLevels : List Level}
    (familyCommonTr : TrExprS env Us common familyIndices
      (VExpr.forallN commonIndices (.sort level)))
    (familyFullTr : TrExprS typeEnv Us full familyIndices familyTarget)
    (familyUnique : TrExprS.IsUnique familyIndices)
    (indexLength : commonIndices.length = stats.nindices[familyIdx]!)
    (familyHead : stats.indConsts[familyIdx]! =
      .const familyName familyLevels)
    (familyTargetEq : familyTarget =
      VExpr.forallN (VExpr.liftTelN fieldIndex checkedIndices 0)
        (.sort level))
    (resultNotForall : ∀ domain body, resultTarget ≠ .forallE domain body)
    (resultLevelTr : VLevel.ofLevel Us stats.resultLevel = some level)
    (absent : env.constants familyName = none)
    (sourceUnique : TrExprS.IsUnique view)
    (sourceClosed : Closed view)
    (wholeTr : TrExprS typeEnv Us full view
      (VExpr.forallN fields resultTarget))
    (parametersDone : stats.params.size ≤ argIdx)
    (universeSemantics : d2Trace.universeSemantics = true)
    (stageFields : ∀ q field, fields[q]? = some field →
      VInductDecl.stage3Field Us.length familyName stats.params.size
        checkedIndices.length (fieldIndex + q) field = true) :
    ConstructorFieldsRunResult env Us full familyTarget level familyName
      stats.params.size checkedIndices fields fieldIndex resultTarget := by
  induction d3 generalizing d2Context d2ContextRun rawSource d2Fuel
      common full d3ViewContext fullLift viewLift commonIndices familyTarget
      analyzerViewContext analyzerViewLift fields fieldIndex with
  | @parameter context parameterArgIdx removed recursiveStarted name domain
      body binderInfo parameter parameterAt tailTrace contextRun tail ih =>
      have parameterLt : parameterArgIdx < stats.params.size := by
        exact Array.getElem?_eq_some_iff.mp parameterAt |>.1
      omega
  | @ordinary context ordinaryArgIdx removed recursiveStarted name domain body
      binderInfo noParameter nonrecursive independent domainCheck ensureType
      consumedCheck annotations fresh tailTrace contextRun domainRun
      consumedRun ensureTypeRun annotationsRun consumedType tail ih =>
      cases d2 with
      | @parameter _ _ _ _ d2Context d2Fuel ordinaryArgIdx name₂
          rawDomain rawBody
          binderInfo₂ parameter parameterType parameterAt parameterTypeGet
          validationDefEq d2TailTrace viewName viewDomain viewBody
          viewBinderInfo domainCheck₂ viewDomainCheck₂ parameterTypeCheck
          d2ContextRun domainRun₂ viewDomainRun₂ parameterTypeSemantic
          validationRun tail₂ =>
          rw [noParameter] at parameterAt
          contradiction
      | @ordinary _ _ _ _ d2Context d2Fuel ordinaryArgIdx name₂
          rawDomain rawBody
          binderInfo₂ sortResult noParameter₂ ensureTypeStep universeTrace
          positivityTrace d2TailTrace viewName viewDomain viewBody
          viewBinderInfo domainCheck₂ viewDomainCheck₂ viewEquality
          consumedCheck₂ fresh₂ d2ContextRun domainRun₂ viewDomainRun₂
          viewEqualityRun₂
          consumedRun₂ ensureTypeRun₂ positivity₂ annotationsRun₂
          consumedType₂ tail₂ =>
          cases d2Alignment with
          | ordinary _ _ _ _ _ positivityAlignment _ _ _ tailAlignment =>
              obtain ⟨fieldTarget, bodyTarget, targetEq, fieldType,
                  bodyType, fieldTr, bodyTr⟩ :=
                TrExprS.forallE_components wholeTr
              cases fields with
              | nil =>
                  exact (resultNotForall fieldTarget bodyTarget targetEq).elim
              | cons field fields =>
                  simp only [VExpr.forallN, VExpr.forallE.injEq] at targetEq
                  obtain ⟨rfl, rfl⟩ := targetEq
                  have actualFieldTr : TrExprS env Us
                      contextRun.candidate.context.vlctx domain
                      domainRun.source' := by
                    simpa only [contextRun.venv_eq, contextRun.lparams_eq]
                      using domainRun.check.expr_tr
                  have actualFieldType : env.HasType Us.length
                      contextRun.candidate.context.vlctx.toCtx
                      domainRun.source' (.sort ensureTypeRun.resultLevel') := by
                    simpa only [contextRun.venv_eq, contextRun.lparams_eq]
                      using ensureTypeRun.source_type
                  have actualAnnotations : env.IsDefEqU Us.length
                      contextRun.candidate.context.vlctx.toCtx
                      domainRun.source' consumedRun.source' := by
                    simpa only [contextRun.venv_eq, contextRun.lparams_eq]
                      using annotationsRun.isDefEqU
                  obtain ⟨consumedLevel, actualConsumedType⟩ := consumedType
                  have actualConsumedType' : env.HasType Us.length
                      contextRun.candidate.context.vlctx.toCtx
                      consumedRun.source' (.sort consumedLevel) := by
                    simpa only [contextRun.venv_eq, contextRun.lparams_eq]
                      using actualConsumedType
                  let nextD3ContextRun := contextRun.pushLocalDecl name
                    binderInfo (consumeTypeAnnotations domain) fresh
                    consumedRun.source' consumedRun.check.expr_tr
                    ⟨consumedLevel, actualConsumedType⟩
                  have actualTailWF : VLCtx.WF env Us.length
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam consumedRun.source') ::
                        contextRun.candidate.context.vlctx) := by
                    have nextWF := nextD3ContextRun.candidate.context.Δwf
                    rw [nextD3ContextRun.venv_eq,
                      nextD3ContextRun.lparams_eq] at nextWF
                    exact nextWF
                  have postViewTr : TrExprS typeEnv Us
                      d2ContextRun.candidate.context.vlctx domain
                      viewDomainRun₂.source' := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using
                      viewDomainRun₂.check.expr_tr
                  have postRawType : typeEnv.HasType Us.length
                      d2ContextRun.candidate.context.vlctx.toCtx
                      domainRun₂.source' (.sort ensureTypeRun₂.resultLevel') := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using ensureTypeRun₂.source_type
                  have postRawView : typeEnv.IsDefEqU Us.length
                      d2ContextRun.candidate.context.vlctx.toCtx
                      domainRun₂.source' viewDomainRun₂.source' := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using
                      viewEqualityRun₂.isDefEqU
                  have postAnnotations : typeEnv.IsDefEqU Us.length
                      d2ContextRun.candidate.context.vlctx.toCtx
                      domainRun₂.source' consumedRun₂.source' := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using
                      annotationsRun₂.isDefEqU
                  let nextD2ContextRun := d2ContextRun.pushLocalDecl name₂
                    binderInfo₂ (consumeTypeAnnotations rawDomain) fresh₂
                    consumedRun₂.source' consumedRun₂.check.expr_tr
                    consumedType₂
                  have postTailWF : VLCtx.WF typeEnv Us.length
                      ((some (d2Context.freshFVarId,
                          (consumeTypeAnnotations rawDomain).fvarsList),
                        .vlam consumedRun₂.source') ::
                        d2ContextRun.candidate.context.vlctx) := by
                    have nextWF := nextD2ContextRun.candidate.context.Δwf
                    rw [nextD2ContextRun.venv_eq,
                      nextD2ContextRun.lparams_eq] at nextWF
                    simpa only [nextD2ContextRun,
                      AddInductive.ConstructorContextRun.pushLocalDecl,
                      CandidateContextRun.pushLocalDecl_vlctx] using nextWF
                  simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics,
                    Bool.and_eq_true] at universeSemantics
                  have sortLevelEq : sortResult.sortLevel! =
                      ensureTypeRun₂.resultLevel := by
                    simpa only [Expr.sortLevel!] using
                      congrArg Expr.sortLevel! ensureTypeRun₂.result_eq
                  have fieldLevelTr : VLevel.ofLevel Us
                      sortResult.sortLevel! =
                        some ensureTypeRun₂.resultLevel' := by
                    rw [sortLevelEq]
                    simpa only [d2ContextRun.lparams_eq] using
                      ensureTypeRun₂.resultLevel_tr
                  have rawBound :=
                    AddInductive.constructorUniverseSemanticGe_ofLevel
                      universeSemantics.1 resultLevelTr fieldLevelTr
                  have freshEq : context.freshFVarId =
                      d2Context.freshFVarId :=
                    Context.freshFVarId_eq_of_ngen_eq ngenEq
                  have domainFVars : FVarsIn (· ∈ common.fvars) domain :=
                    constructorIndependentOf_fvars fieldTr.fvarsIn
                      independent removedInvariant
                  obtain ⟨commonDomain, commonDomainTr, fieldEq,
                      commonDomainType, nextD3State⟩ :=
                    d3State.push (name := name) (binderInfo := binderInfo)
                      henv typeEnvWF addType sourceUnique.1
                      sourceClosed.1 domainFVars fieldTr actualFieldTr
                      actualFieldType actualAnnotations actualConsumedType'
                      actualTailWF
                  obtain ⟨postAnalyzerType, nextAnalyzerState⟩ :=
                    analyzerState.push typeEnvWF sourceUnique.1 sourceClosed.1
                      fieldTr postViewTr postRawType postRawView
                      postAnnotations postTailWF
                  have fieldBaseType : env.HasType Us.length full.toCtx field
                      (.sort ensureTypeRun.resultLevel') := by
                    rw [fieldEq]
                    exact commonDomainType.weak' henv.ordered
                      d3State.fullExtension.toCtx
                  have levelEq : ensureTypeRun.resultLevel' ≈
                      ensureTypeRun₂.resultLevel' :=
                    (fieldBaseType.mono addType).uniqU typeEnvWF
                      d3State.fullWF.toCtx postAnalyzerType |>.sort_inv
                        typeEnvWF d3State.fullWF.toCtx
                  have fieldBound : level = .zero ∨
                      ensureTypeRun.resultLevel' ≤ level := by
                    rcases rawBound with prop | bound
                    · exact .inl prop
                    · exact .inr <| VLevel.le_trans
                        (VLevel.le_antisymm_iff.mp levelEq).1 bound
                  have commonFree : commonDomain.hasConst familyName = false :=
                    VEnv.HasType.hasConst_false_of_absent henv.ordered
                      d3State.commonWF.toCtx absent commonDomainType
                  have fieldFree : field.hasConst familyName = false := by
                    rw [fieldEq, VExpr.hasConst_lift']
                    exact commonFree
                  have recNone := recArg?_eq_none_of_hasConst_false
                    (U := Us.length) (np := stats.params.size)
                    (ni := checkedIndices.length) (fieldIndex := fieldIndex)
                    fieldFree
                  have nextD3State' : D3FullContextState env typeEnv Us
                      (context.pushLocalDecl name binderInfo
                        (consumeTypeAnnotations domain))
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam commonDomain) :: common)
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      nextD3ContextRun.candidate.context.vlctx
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam (commonDomain.lift' viewLift)) :: d3ViewContext)
                      (.consN fullLift 1) (.consN viewLift 1) := by
                    exact nextD3State
                  have nextAnalyzerState' : AnalyzerPostContextState
                      typeEnv Us
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      nextD2ContextRun.candidate.context.vlctx
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam (field.lift' analyzerViewLift)) ::
                        analyzerViewContext)
                      (.consN analyzerViewLift 1) := by
                    rw [freshEq]
                    simpa only [nextD2ContextRun,
                      AddInductive.ConstructorContextRun.pushLocalDecl,
                      CandidateContextRun.pushLocalDecl_vlctx] using
                      nextAnalyzerState
                  have familyCommonNext : TrExprS env Us
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam commonDomain) :: common)
                      familyIndices
                      (VExpr.forallN (VExpr.liftTelN 1 commonIndices 0)
                        (.sort level)) := by
                    have weakened := familyCommonTr.weakFV henv.ordered
                      (VLCtx.FVLift.skip_fvar
                        (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList)
                        (.vlam commonDomain) .refl)
                      nextD3State'.commonWF
                    simpa [VLocalDecl.depth, VExpr.liftN_forallN,
                      VExpr.liftN] using weakened
                  have familyFullNext : TrExprS typeEnv Us
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      familyIndices (familyTarget.liftN 1 0) := by
                    have weakened := familyFullTr.weakFV typeEnvWF.ordered
                      (VLCtx.FVLift.skip_fvar
                        (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList)
                        (.vlam field) .refl)
                      nextD3State'.fullWF
                    simpa [VLocalDecl.depth] using weakened
                  have bodyOpened : TrExprS typeEnv Us
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      (body.instantiate1 context.freshExpr)
                      (VExpr.forallN fields resultTarget) := by
                    simpa only [AddInductive.Context.freshExpr,
                      Expr.instantiate1_eq] using
                      bodyTr.inst_fvar typeEnvWF.ordered nextD3State'.fullWF
                  have tailUnique : TrExprS.IsUnique
                      (body.instantiate1 context.freshExpr) := by
                    apply TrExprS.IsUnique.instantiate1 sourceUnique.2
                    simp only [AddInductive.Context.freshExpr]
                    trivial
                  have nextFullNoBV :
                      VLCtx.bvars (((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full) : VLCtx) = 0 :=
                    nextD3State'.fullExtension.bvars_eq.trans
                      nextD3State'.commonNoBV
                  have tailClosed : Closed
                      (body.instantiate1 context.freshExpr) := by
                    have closed := bodyOpened.closed
                    rw [nextFullNoBV] at closed
                    exact closed
                  have freshExprEq : d2Context.freshExpr =
                      context.freshExpr := by
                    simp only [AddInductive.Context.freshExpr, freshEq]
                  have tailAlignment' : AddInductive.ConstructorViewAlignmentTrace
                      d2TailTrace (body.instantiate1 context.freshExpr) := by
                    rw [← freshExprEq]
                    exact tailAlignment
                  have tail₂' : AddInductive.ConstructorViewSemanticRun
                      typeEnv Us whnfFuel nextD2ContextRun d2TailTrace
                      (body.instantiate1 context.freshExpr) := by
                    rw [← freshExprEq]
                    exact tail₂
                  have nextNgenEq :
                      (context.pushLocalDecl name binderInfo
                        (consumeTypeAnnotations domain)).ngen =
                      (d2Context.pushLocalDecl name₂ binderInfo₂
                        (consumeTypeAnnotations rawDomain)).ngen := by
                    simp only [AddInductive.Context.pushLocalDecl, ngenEq]
                  have nextIndexLength :
                      (VExpr.liftTelN 1 commonIndices 0).length =
                        stats.nindices[familyIdx]! := by
                    simpa only [VExpr.liftTelN_length] using indexLength
                  have familyTargetNextEq : familyTarget.liftN 1 0 =
                      VExpr.forallN
                        (VExpr.liftTelN (fieldIndex + 1) checkedIndices 0)
                        (.sort level) := by
                    rw [familyTargetEq, VExpr.liftN_forallN,
                      VExpr.liftTelN_liftTelN]
                    simp only [VExpr.liftN]
                  have stageTail : ∀ q candidate,
                      fields[q]? = some candidate →
                      VInductDecl.stage3Field Us.length familyName
                        stats.params.size checkedIndices.length
                        (fieldIndex + 1 + q) candidate = true := by
                    intro q candidate member
                    have staged := stageFields (q + 1) candidate (by
                      simpa using member)
                    simpa only [Nat.add_assoc, Nat.add_comm 1 q] using staged
                  obtain ⟨tailFields, tailSpine⟩ := ih
                    (fieldIndex := fieldIndex + 1) tailAlignment' tail₂'
                    nextD3State' nextAnalyzerState'
                    (removedInvariant.push) nextNgenEq familyCommonNext
                    familyFullNext nextIndexLength familyTargetNextEq
                    tailUnique tailClosed bodyOpened (by omega)
                    universeSemantics.2 stageTail
                  unfold ConstructorFieldsRunResult
                  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                  · exact .inr (.inr ⟨recNone, ensureTypeRun.resultLevel',
                      fieldBaseType, fieldBound⟩)
                  · intro recursive
                    rw [VInductDecl.recArg?_of_isRecField recursive] at recNone
                    contradiction
                  · simpa only [VLCtx.toCtx] using tailFields
                  · simpa only [List.reverse_cons, List.singleton_append,
                      List.append_assoc, VLCtx.toCtx, List.length_cons,
                      VExpr.liftN_liftN, Nat.add_comm] using tailSpine
      | terminal sourceRun₂ viewRun₂ =>
          cases d2Alignment; simp_all [Expr.isForall]
  | @recursive context recursiveArgIdx removed recursiveStarted name domain
      body binderInfo noParameter isRecursive independent fieldTrace fresh
      tailTrace contextRun recursiveRun tail ih =>
      cases d2 with
      | @parameter _ _ _ _ d2Context d2Fuel recursiveArgIdx name₂
          rawDomain rawBody binderInfo₂ parameter parameterType parameterAt
          parameterTypeGet validationDefEq d2TailTrace viewName viewDomain
          viewBody viewBinderInfo domainCheck₂ viewDomainCheck₂
          parameterTypeCheck d2ContextRun domainRun₂ viewDomainRun₂
          parameterTypeSemantic validationRun tail₂ =>
          rw [noParameter] at parameterAt
          contradiction
      | @ordinary _ _ _ _ d2Context d2Fuel recursiveArgIdx name₂
          rawDomain rawBody binderInfo₂ sortResult noParameter₂
          ensureTypeStep universeTrace positivityTrace d2TailTrace viewName
          viewDomain viewBody viewBinderInfo domainCheck₂ viewDomainCheck₂
          viewEquality consumedCheck₂ fresh₂ d2ContextRun domainRun₂
          viewDomainRun₂ viewEqualityRun₂ consumedRun₂ ensureTypeRun₂
          positivity₂ annotationsRun₂ consumedType₂ tail₂ =>
          cases d2Alignment with
          | ordinary _ _ _ _ _ positivityAlignment _ _ _ tailAlignment =>
              obtain ⟨fieldTarget, bodyTarget, targetEq, fieldType,
                  bodyType, fieldTr, bodyTr⟩ :=
                TrExprS.forallE_components wholeTr
              cases fields with
              | nil =>
                  exact (resultNotForall fieldTarget bodyTarget targetEq).elim
              | cons field fields =>
                  simp only [VExpr.forallN, VExpr.forallE.injEq] at targetEq
                  obtain ⟨rfl, rfl⟩ := targetEq
                  have postViewTr : TrExprS typeEnv Us
                      d2ContextRun.candidate.context.vlctx domain
                      viewDomainRun₂.source' := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using
                      viewDomainRun₂.check.expr_tr
                  have postRawType : typeEnv.HasType Us.length
                      d2ContextRun.candidate.context.vlctx.toCtx
                      domainRun₂.source' (.sort ensureTypeRun₂.resultLevel') := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using ensureTypeRun₂.source_type
                  have postRawView : typeEnv.IsDefEqU Us.length
                      d2ContextRun.candidate.context.vlctx.toCtx
                      domainRun₂.source' viewDomainRun₂.source' := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using
                      viewEqualityRun₂.isDefEqU
                  have postAnnotations : typeEnv.IsDefEqU Us.length
                      d2ContextRun.candidate.context.vlctx.toCtx
                      domainRun₂.source' consumedRun₂.source' := by
                    simpa only [d2ContextRun.venv_eq,
                      d2ContextRun.lparams_eq] using annotationsRun₂.isDefEqU
                  let nextD2ContextRun := d2ContextRun.pushLocalDecl name₂
                    binderInfo₂ (consumeTypeAnnotations rawDomain) fresh₂
                    consumedRun₂.source' consumedRun₂.check.expr_tr
                    consumedType₂
                  have postTailWF : VLCtx.WF typeEnv Us.length
                      ((some (d2Context.freshFVarId,
                          (consumeTypeAnnotations rawDomain).fvarsList),
                        .vlam consumedRun₂.source') ::
                        d2ContextRun.candidate.context.vlctx) := by
                    have nextWF := nextD2ContextRun.candidate.context.Δwf
                    rw [nextD2ContextRun.venv_eq,
                      nextD2ContextRun.lparams_eq] at nextWF
                    simpa only [nextD2ContextRun,
                      AddInductive.ConstructorContextRun.pushLocalDecl,
                      CandidateContextRun.pushLocalDecl_vlctx] using nextWF
                  simp only [
                    AddInductive.ConstructorTypeValidationTrace.universeSemantics,
                    Bool.and_eq_true] at universeSemantics
                  have freshEq : context.freshFVarId =
                      d2Context.freshFVarId :=
                    Context.freshFVarId_eq_of_ngen_eq ngenEq
                  obtain ⟨postAnalyzerType, nextAnalyzerState⟩ :=
                    analyzerState.push typeEnvWF sourceUnique.1 sourceClosed.1
                      fieldTr postViewTr postRawType postRawView
                      postAnnotations postTailWF
                  have nextAnalyzerState' : AnalyzerPostContextState
                      typeEnv Us
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      nextD2ContextRun.candidate.context.vlctx
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam (field.lift' analyzerViewLift)) ::
                        analyzerViewContext)
                      (.consN analyzerViewLift 1) := by
                    rw [freshEq]
                    simpa only [nextD2ContextRun,
                      AddInductive.ConstructorContextRun.pushLocalDecl,
                      CandidateContextRun.pushLocalDecl_vlctx] using
                      nextAnalyzerState
                  have domainFVars : FVarsIn (· ∈ common.fvars) domain :=
                    constructorIndependentOf_fvars fieldTr.fvarsIn
                      independent removedInvariant
                  have recursiveResult := recursiveField_exactAnalyzer
                    recursiveRun henv typeEnvWF addType d3State
                    familyCommonTr familyFullTr familyUnique indexLength
                    familyHead sourceUnique.1 sourceClosed.1 domainFVars fieldTr
                  have stageHead : VInductDecl.stage3Field Us.length
                      familyName stats.params.size checkedIndices.length
                      fieldIndex field = true := by
                    simpa using stageFields 0 field (by simp)
                  obtain ⟨recursive, recursiveEq, recursiveWF⟩ :=
                    recursiveFieldResult_recArgWF recursiveResult
                      familyTargetEq stageHead
                  have nextD3State : D3FullContextState env typeEnv Us
                      context.advanceFresh common
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      contextRun.advanceFresh.candidate.context.vlctx
                      d3ViewContext (.skipN fullLift 1) viewLift := by
                    simpa only [AddInductive.ConstructorContextRun.advanceFresh,
                      AddInductive.advanceCandidateContextRun] using
                      d3State.skip (source := domain)
                        nextAnalyzerState'.fullWF
                  have familyFullNext : TrExprS typeEnv Us
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      familyIndices (familyTarget.liftN 1 0) := by
                    have weakened := familyFullTr.weakFV typeEnvWF.ordered
                      (VLCtx.FVLift.skip_fvar
                        (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList)
                        (.vlam field) .refl)
                      nextD3State.fullWF
                    simpa [VLocalDecl.depth] using weakened
                  have bodyOpened : TrExprS typeEnv Us
                      ((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full)
                      (body.instantiate1 context.freshExpr)
                      (VExpr.forallN fields resultTarget) := by
                    simpa only [AddInductive.Context.freshExpr,
                      Expr.instantiate1_eq] using
                      bodyTr.inst_fvar typeEnvWF.ordered nextD3State.fullWF
                  have tailUnique : TrExprS.IsUnique
                      (body.instantiate1 context.freshExpr) := by
                    apply TrExprS.IsUnique.instantiate1 sourceUnique.2
                    simp only [AddInductive.Context.freshExpr]
                    trivial
                  have nextFullNoBV :
                      VLCtx.bvars (((some (context.freshFVarId,
                          (consumeTypeAnnotations domain).fvarsList),
                        .vlam field) :: full) : VLCtx) = 0 :=
                    nextD3State.fullExtension.bvars_eq.trans
                      nextD3State.commonNoBV
                  have tailClosed : Closed
                      (body.instantiate1 context.freshExpr) := by
                    have closed := bodyOpened.closed
                    rw [nextFullNoBV] at closed
                    exact closed
                  have freshExprEq : d2Context.freshExpr =
                      context.freshExpr := by
                    simp only [AddInductive.Context.freshExpr, freshEq]
                  have tailAlignment' : AddInductive.ConstructorViewAlignmentTrace
                      d2TailTrace (body.instantiate1 context.freshExpr) := by
                    rw [← freshExprEq]
                    exact tailAlignment
                  have tail₂' : AddInductive.ConstructorViewSemanticRun
                      typeEnv Us whnfFuel nextD2ContextRun d2TailTrace
                      (body.instantiate1 context.freshExpr) := by
                    rw [← freshExprEq]
                    exact tail₂
                  have nextNgenEq : context.advanceFresh.ngen =
                      (d2Context.pushLocalDecl name₂ binderInfo₂
                        (consumeTypeAnnotations rawDomain)).ngen := by
                    simp only [AddInductive.Context.advanceFresh,
                      AddInductive.Context.pushLocalDecl, ngenEq]
                  have freshFull : context.freshFVarId ∉ full.fvars :=
                    (nextAnalyzerState'.fullWF.2.1 _ _ rfl).1
                  have familyTargetNextEq : familyTarget.liftN 1 0 =
                      VExpr.forallN
                        (VExpr.liftTelN (fieldIndex + 1) checkedIndices 0)
                        (.sort level) := by
                    rw [familyTargetEq, VExpr.liftN_forallN,
                      VExpr.liftTelN_liftTelN]
                    simp only [VExpr.liftN]
                  have stageTail : ∀ q candidate,
                      fields[q]? = some candidate →
                      VInductDecl.stage3Field Us.length familyName
                        stats.params.size checkedIndices.length
                        (fieldIndex + 1 + q) candidate = true := by
                    intro q candidate member
                    have staged := stageFields (q + 1) candidate (by
                      simpa using member)
                    simpa only [Nat.add_assoc, Nat.add_comm 1 q] using staged
                  obtain ⟨tailFields, tailSpine⟩ := ih
                    (fieldIndex := fieldIndex + 1) tailAlignment' tail₂'
                    nextD3State nextAnalyzerState'
                    (removedInvariant.skip freshFull) nextNgenEq
                    familyCommonTr familyFullNext indexLength
                    familyTargetNextEq tailUnique tailClosed bodyOpened
                    (by omega) universeSemantics.2 stageTail
                  have headClassification :
                      VInductDecl.isRecField Us.length familyName
                          stats.params.size checkedIndices.length fieldIndex
                          field = true ∨
                        (∃ descriptor,
                          VInductDecl.recArg? Us.length familyName
                              stats.params.size checkedIndices.length
                              fieldIndex field = some descriptor ∧
                            descriptor.binders ≠ [] ∧
                            descriptor.WF Us.length env level checkedIndices
                              full.toCtx) ∨
                        VInductDecl.recArg? Us.length familyName
                            stats.params.size checkedIndices.length fieldIndex
                            field = none ∧
                          ∃ fieldLevel,
                            env.HasType Us.length full.toCtx field
                                (.sort fieldLevel) ∧
                              (level = .zero ∨ fieldLevel ≤ level) := by
                    by_cases nonempty : recursive.binders ≠ []
                    · exact .inr (.inl ⟨recursive, recursiveEq, nonempty,
                        recursiveWF⟩)
                    · have empty : recursive.binders = [] := by
                        simpa using nonempty
                      exact .inl
                        (VInductDecl.recArg?_nil recursiveEq empty).1
                  have headDirectSpine :
                      VInductDecl.isRecField Us.length familyName
                          stats.params.size checkedIndices.length fieldIndex
                          field = true →
                        env.SpineWF Us.length full.toCtx
                          (VExpr.forallN
                            (VExpr.liftTelN fieldIndex checkedIndices 0)
                            (.sort level))
                          (VInductDecl.recFieldIdxs stats.params.size field)
                          (.sort level) := by
                    intro direct
                    have canonical :=
                      VInductDecl.recArg?_of_isRecField direct
                    have descriptorEq : recursive =
                        { fieldIndex := fieldIndex, binders := [],
                          targetType := 0,
                          indices := VInductDecl.recFieldIdxs
                            stats.params.size field } :=
                      Option.some.inj (recursiveEq.symm.trans canonical)
                    rw [descriptorEq] at recursiveWF
                    simpa [VInductDecl.RecArg.WF] using recursiveWF.2
                  unfold ConstructorFieldsRunResult
                  refine ⟨⟨headClassification, headDirectSpine, ?_⟩, ?_⟩
                  · simpa only [VLCtx.toCtx] using tailFields
                  · simpa only [List.reverse_cons, List.singleton_append,
                      List.append_assoc, VLCtx.toCtx, List.length_cons,
                      VExpr.liftN_liftN, Nat.add_comm] using tailSpine
      | terminal sourceRun₂ viewRun₂ =>
          cases d2Alignment; simp_all [Expr.isForall]
  | @terminal context source terminalArgIdx removed recursiveStarted valid
      independent spineTrace contextRun expected spine =>
      have shape := isValidIndAppIdx_shape valid
      have sourceHead : source.getAppFn = .const familyName familyLevels := by
        rw [familyHead] at shape
        change source.getAppFn.eqv (.const familyName familyLevels) = true ∧ _
          at shape
        rw [Expr.eqv_eq] at shape
        generalize headEq : source.getAppFn = head at shape
        cases head <;> simp_all [Expr.eqv']
      cases fields with
      | nil =>
          unfold ConstructorFieldsRunResult
          refine ⟨trivial, ?_⟩
          simpa using terminal_exactAnalyzer
            (valid := valid) (resultTarget := resultTarget)
            spine henv typeEnvWF addType d3State
            familyCommonTr familyFullTr familyUnique indexLength familyHead
            sourceUnique sourceClosed
            (constructorIndependentOf_fvars wholeTr.fvarsIn independent
              removedInvariant)
            wholeTr
      | cons field fields =>
          cases wholeTr
          all_goals simp_all [Expr.getAppFn]

end ConstructorValidation

namespace VInductDecl
open AddInductive TypeChecker VEnv

theorem stagedIndexCount_eq
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {kernelSource : InductiveType}
    {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate source)
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source)
    (_analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    (input.postFamilyInput.universeInput.staged.family.validation.stats
        ).nindices[0]! = generation.block.checked.indices.length := by
  let validation := input.postFamilyInput.universeInput.staged.family.validation
  have familyShape := shape
  simp only [NormalizationCandidateSemanticRun.generationShape,
    normalizationCandidateGenerationShape, Bool.and_eq_true,
    beq_iff_eq] at familyShape
  have spineLengthEq :
      candidate.families.singleton.familyType.type.trace.spineLength =
        (generation.block.checked.params ++
          generation.block.checked.indices).length := by
    calc
      _ = (VExpr.telN source.nparams normalization.raw.type ++
          ctorFields (VExpr.dropN source.nparams normalization.raw.type)).length :=
        familyShape.1.2
      _ = (generation.block.rawParams ++
          generation.block.rawIndices).length := by
        simp only [NormalizedChecked.rawParams, NormalizedChecked.rawIndices,
          NormalizationCandidateSemanticRun.root,
          normalization.root.sourceType_eq generation]
      _ = (generation.block.checked.params ++
          generation.block.checked.indices).length := by
        simp only [List.length_append]
        rw [generation.shape.2.1, generation.shape.2.2.1]
  have parameterLength : generation.block.checked.params.length =
      source.nparams :=
    generation.block.checked.direct_anatomy.2.1.trans
      generation.block.nparams_eq.symm
  change validation.stats.nindices[0]! = _
  rw [validation.stats_eq]
  simp only [CandidateExprTrace.singletonCandidateInductiveStats]
  rw [spineLengthEq, List.length_append, parameterLength,
    input.postFamilyInput.universeInput.staged.validation_nparams_eq,
    Nat.add_sub_cancel_left]
  rfl

theorem stagedResultLevel_tr
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {kernelSource : InductiveType}
    {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate source)
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    VLevel.ofLevel Us
        input.postFamilyInput.universeInput.staged.family.validation.stats.resultLevel =
      some generation.block.checked.resultLevel := by
  let validation := input.postFamilyInput.universeInput.staged.family.validation
  have familyShape := shape
  simp only [NormalizationCandidateSemanticRun.generationShape,
    normalizationCandidateGenerationShape, Bool.and_eq_true,
    beq_iff_eq] at familyShape
  have spineLengthEq :
      candidate.families.singleton.familyType.type.trace.spineLength =
        (generation.block.checked.params ++
          generation.block.checked.indices).length := by
    calc
      _ = (VExpr.telN source.nparams normalization.raw.type ++
          ctorFields (VExpr.dropN source.nparams normalization.raw.type)).length :=
        familyShape.1.2
      _ = (generation.block.rawParams ++
          generation.block.rawIndices).length := by
        simp only [NormalizedChecked.rawParams, NormalizedChecked.rawIndices,
          NormalizationCandidateSemanticRun.root,
          normalization.root.sourceType_eq generation]
      _ = (generation.block.checked.params ++
          generation.block.checked.indices).length := by
        simp only [List.length_append]
        rw [generation.shape.2.1, generation.shape.2.2.1]
  have viewEq : normalization.family.type.view =
      VExpr.forallN
        (generation.block.checked.params ++ generation.block.checked.indices)
        (.sort generation.block.checked.resultLevel) := by
    have analyzerEq : normalization.family.type.view =
        generation.block.checked.type.type :=
      (congrArg (fun ty : VInductiveType => ty.type)
        (normalization.root.familyViewType_eq analysis)).symm
    rw [analyzerEq, generation.block.checked.type_eq,
      VExpr.forallN_append]
  obtain ⟨_, recursive⟩ := normalization.family.type.recursive
  have levelTr := ConstructorValidation.CandidateExprRun.terminalLevel_tr recursive
    validation.terminal_eq viewEq spineLengthEq
  change VLevel.ofLevel Us validation.stats.resultLevel = _
  rw [validation.stats_eq]
  simpa only [CandidateExprTrace.singletonCandidateInductiveStats] using levelTr

end VInductDecl

namespace VInductDecl
open AddInductive TypeChecker VEnv
open ConstructorValidation

/-- Derive the checked field and result-spine obligations for one exact
analyzer-owned constructor position after consuming its parameter prefix. -/
theorem CandidateSemanticNormalizedCtorRun.checkedConstructorWF
    {env typeEnv : VEnv} {Us : List Name}
    {source : VInductDecl} {generation : GenerationChecked source}
    {kernelCtor : Constructor}
    {candidateCtor : AddInductive.CandidateConstructor kernelCtor}
    {rawCtor : VConstVal}
    {root : CandidateConstructorSemanticRun typeEnv Us candidateCtor rawCtor}
    {ctor : NormalizedCtor}
    {stats : InductiveStats} {familyIndices : Expr}
    {d3Context d2Context : AddInductive.Context}
    {d3ContextRun : AddInductive.ConstructorContextRun env Us d3Context}
    {d2ContextRun : AddInductive.ConstructorContextRun typeEnv Us d2Context}
    {d3Trace : AddInductive.ConstructorPreFamilyViewTrace stats 0
      familyIndices d3Context candidateCtor.type.view 0 [] false}
    (d3 : AddInductive.ConstructorPreFamilyViewSemanticRun env Us stats 0
      familyIndices d3ContextRun d3Trace)
    {d2Trace : AddInductive.ConstructorTypeValidationTrace stats false 0
      kernelCtor.name d2Context kernelCtor.type 0 d2Context.fuel.inductiveFuel}
    (d2Alignment : AddInductive.ConstructorViewAlignmentTrace d2Trace
      candidateCtor.type.view)
    (d2 : AddInductive.ConstructorViewSemanticRun typeEnv Us
      root.type.whnfFuel d2ContextRun d2Trace candidateCtor.type.view)
    (genRun : CandidateSemanticNormalizedCtorRun generation.block typeEnv Us
      root ctor)
    (hctor : ctor ∈ generation.block.ctorPairs)
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    {parameterΔ d3ViewContext analyzerViewContext : VLCtx}
    {viewLift analyzerViewLift : Lift}
    {parameters : List Expr}
    (parameterContext : CandidateParameterContext [] parameters
      generation.block.checked.params parameterΔ)
    (parameterWF : VLCtx.WF env Us.length parameterΔ)
    (parameterCtx : parameterΔ.toCtx =
      generation.block.checked.params.reverse)
    (d3State : D3FullContextState env typeEnv Us d3Context
      parameterΔ parameterΔ d3ContextRun.candidate.context.vlctx
      d3ViewContext .refl viewLift)
    (analyzerState : AnalyzerPostContextState typeEnv Us parameterΔ
      d2ContextRun.candidate.context.vlctx analyzerViewContext
      analyzerViewLift)
    (ngenEq : d3Context.ngen = d2Context.ngen)
    (parametersEq : stats.params.toList = parameters)
    {familyName : Name} {familyLevels : List Level}
    (indConsts : stats.indConsts = #[.const familyName familyLevels])
    (familyTr : TrExprS env Us parameterΔ familyIndices
      (VExpr.forallN generation.block.checked.indices
        (.sort generation.block.checked.resultLevel)))
    (familyUnique : TrExprS.IsUnique familyIndices)
    (indexLength : generation.block.checked.indices.length =
      stats.nindices[0]!)
    (resultLevelTr : VLevel.ofLevel Us stats.resultLevel =
      some generation.block.checked.resultLevel)
    (absent : env.constants familyName = none)
    (unique : CandidateExprTraceViewIsUnique candidateCtor.type.trace)
    (universeSemantics : d2Trace.universeSemantics = true)
    (stageFields : ∀ q field, ctor.view.fields[q]? = some field →
      VInductDecl.stage3Field Us.length familyName stats.params.size
        generation.block.checked.indices.length q field = true) :
    VInductDecl.fieldsWF Us.length familyName stats.params.size env
        generation.block.checked.resultLevel
        generation.block.checked.indices
        generation.block.checked.params.reverse 0 ctor.view.fields ∧
      env.SpineWF Us.length
        (ctor.view.fields.reverse ++
          generation.block.checked.params.reverse)
        (VExpr.forallN
          (VExpr.liftTelN ctor.view.fields.length
            generation.block.checked.indices 0)
          (.sort generation.block.checked.resultLevel))
        (VInductDecl.recFieldIdxs stats.params.size
          (ctor.resultTarget generation.block))
        (.sort generation.block.checked.resultLevel) := by
  obtain ⟨rest, instantiation, ⟨d3Suffix⟩, wholeTr⟩ :=
    genRun.preFamilySuffix addType parameterContext parameterWF unique d3
      hctor parametersEq indConsts
  obtain ⟨d2Suffix, suffixUniverse⟩ :=
    d2.afterParameters d2Alignment (by omega) instantiation
  have instantiation' : instantiateFamilyParameters candidateCtor.type.view
      parameters = .ok rest := by
    rw [← parametersEq]
    exact instantiation
  have sourceUnique : TrExprS.IsUnique rest :=
    instantiateFamilyParameters_unique unique.view
      (ConstructorValidation.CandidateParameterContext.parametersUnique
        parameterContext) instantiation'
  have sourceClosed : Closed rest := by
    have closed := wholeTr.closed
    rw [show parameterΔ.bvars = 0 from by
      simpa only [VLCtx.NoBV] using d3State.commonNoBV] at closed
    exact closed
  have resultNotForall : ∀ domain body,
      ctor.resultTarget generation.block ≠ .forallE domain body := by
    intro domain body equality
    have headEq := congrArg VExpr.appHead equality
    simp only [NormalizedCtor.resultTarget, VExpr.appHead_appN,
      VExpr.appHead] at headEq
    exact VExpr.noConfusion headEq
  have familyTargetEq :
      VExpr.forallN generation.block.checked.indices
          (.sort generation.block.checked.resultLevel) =
        VExpr.forallN
          (VExpr.liftTelN 0 generation.block.checked.indices 0)
          (.sort generation.block.checked.resultLevel) := by
    have liftTelNZero : ∀ (indices : List VExpr) (cutoff : Nat),
        VExpr.liftTelN 0 indices cutoff = indices := by
      intro indices cutoff
      induction indices generalizing cutoff with
      | nil => rfl
      | cons index indices ih =>
          simp only [VExpr.liftTelN, VExpr.liftN_zero]
          rw [ih]
    rw [liftTelNZero]
  have removedInvariant : FullRemovedInvariant parameterΔ parameterΔ
      [] := by
    intro fv member _
    exact member
  have familyHead : stats.indConsts[0]! =
      .const familyName familyLevels := by
    rw [indConsts]
    rfl
  have suffixUniverseSemantics :
      d2Suffix.trace.universeSemantics = true :=
    suffixUniverse.trans universeSemantics
  have result := constructorFields_exactAnalyzer
    (d3 := d3Suffix.semantic)
    (d2Alignment := d2Suffix.alignment) (d2 := d2Suffix.semantic)
    henv typeEnvWF addType d3State analyzerState
    removedInvariant ngenEq
    familyTr (familyTr.mono addType) familyUnique indexLength
    familyHead
    familyTargetEq resultNotForall resultLevelTr absent sourceUnique
    sourceClosed wholeTr (by omega) suffixUniverseSemantics (by
      intro q field atIndex
      simpa only [Nat.zero_add] using stageFields q field atIndex)
  unfold ConstructorFieldsRunResult at result
  simpa only [parameterCtx, VExpr.liftN_forallN, VExpr.liftN,
    Nat.zero_add] using result

/-- Traverse the exact source-indexed D3, D2, and analyzer lists in lockstep.
The dependent indices rule out truncation, reordering, or reuse of evidence
from a different constructor position. -/
theorem CandidateSemanticNormalizedCtorListRun.checkedConstructorsWF
    {env typeEnv : VEnv} {Us : List Name}
    {source : VInductDecl} {generation : GenerationChecked source}
    {stats : InductiveStats} {familyIndices : Expr}
    {d3Context d2Context : AddInductive.Context}
    {d3ContextRun : AddInductive.ConstructorContextRun env Us d3Context}
    {d2ContextRun : AddInductive.ConstructorContextRun typeEnv Us d2Context}
    {kernelCtors : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelCtors}
    {d3Trace : AddInductive.ConstructorPreFamilyListTrace stats 0
      familyIndices d3Context candidates}
    (d3 : AddInductive.ConstructorPreFamilyListSemanticRun env Us stats 0
      familyIndices d3Context d3ContextRun d3Trace)
    {seen : NameSet}
    {d2Trace : AddInductive.ConstructorListValidationTrace stats false 0
      d2Context seen kernelCtors}
    {alignment : AddInductive.ConstructorCandidateAlignmentTrace stats false 0
      d2Context d2Trace candidates}
    {raws : List VConstVal}
    {roots : CandidateConstructorSemanticListRun typeEnv Us candidates raws}
    (d2 : AddInductive.ConstructorPostFamilySemanticListRun typeEnv Us stats
      false 0 d2Context d2ContextRun d2Trace candidates alignment roots)
    {ctors : List NormalizedCtor}
    (generationRuns : CandidateSemanticNormalizedCtorListRun generation.block
      typeEnv Us roots ctors)
    (membership : ∀ ctor ∈ ctors,
      ctor ∈ generation.block.ctorPairs)
    (henv : VEnv.WF env) (typeEnvWF : VEnv.WF typeEnv)
    (addType : env ≤ typeEnv)
    {parameterΔ d3ViewContext analyzerViewContext : VLCtx}
    {viewLift analyzerViewLift : Lift}
    {parameters : List Expr}
    (parameterContext : CandidateParameterContext [] parameters
      generation.block.checked.params parameterΔ)
    (parameterWF : VLCtx.WF env Us.length parameterΔ)
    (parameterCtx : parameterΔ.toCtx =
      generation.block.checked.params.reverse)
    (d3State : D3FullContextState env typeEnv Us d3Context
      parameterΔ parameterΔ d3ContextRun.candidate.context.vlctx
      d3ViewContext .refl viewLift)
    (analyzerState : AnalyzerPostContextState typeEnv Us parameterΔ
      d2ContextRun.candidate.context.vlctx analyzerViewContext
      analyzerViewLift)
    (ngenEq : d3Context.ngen = d2Context.ngen)
    (parametersEq : stats.params.toList = parameters)
    {familyName : Name} {familyLevels : List Level}
    (indConsts : stats.indConsts = #[.const familyName familyLevels])
    (familyTr : TrExprS env Us parameterΔ familyIndices
      (VExpr.forallN generation.block.checked.indices
        (.sort generation.block.checked.resultLevel)))
    (familyUnique : TrExprS.IsUnique familyIndices)
    (indexLength : generation.block.checked.indices.length =
      stats.nindices[0]!)
    (resultLevelTr : VLevel.ofLevel Us stats.resultLevel =
      some generation.block.checked.resultLevel)
    (absent : env.constants familyName = none)
    (unique : candidates.ViewTranslationUnique)
    (universeSemantics : d2Trace.universeSemantics = true)
    (uvarsEq : source.uvars = Us.length)
    (familyNameEq : familyName = generation.block.checked.type.name)
    (paramsSizeEq : stats.params.size = source.nparams) :
    ∀ ctor ∈ ctors,
      VInductDecl.fieldsWF Us.length familyName stats.params.size env
          generation.block.checked.resultLevel
          generation.block.checked.indices
          generation.block.checked.params.reverse 0 ctor.view.fields ∧
        env.SpineWF Us.length
          (ctor.view.fields.reverse ++
            generation.block.checked.params.reverse)
          (VExpr.forallN
            (VExpr.liftTelN ctor.view.fields.length
              generation.block.checked.indices 0)
            (.sort generation.block.checked.resultLevel))
          (VInductDecl.recFieldIdxs stats.params.size
            (ctor.resultTarget generation.block))
          (.sort generation.block.checked.resultLevel) := by
  induction d3 generalizing seen raws ctors with
  | nil =>
      cases d2
      cases generationRuns
      intro ctor member
      simp at member
  | cons d3Head d3Tail ih =>
      cases alignment with
      | cons rootScope storedSpine spineLength candidateDepth headAlignment
          tailAlignment =>
        cases d2 with
        | cons root d2Head spine d2Tail =>
          cases generationRuns with
          | cons generationHead generationTail =>
            simp only [AddInductive.ConstructorListValidationTrace.universeSemantics,
              Bool.and_eq_true] at universeSemantics
            intro ctor member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · have hctor : ctor ∈ generation.block.ctorPairs :=
                membership ctor (.head _)
              obtain ⟨directCtor, directMember, viewEq⟩ :=
                generation.viewCtor_ofDirect hctor
              have directStage :=
                (generation.block.checked.direct_anatomy.2.2.2.2.2
                  directCtor directMember).2.2
              rw [← generation.block.uvars_eq,
                ← generation.block.nparams_eq,
                uvarsEq, ← familyNameEq, ← paramsSizeEq] at directStage
              have viewEq' : ctor.view =
                  CheckedCtor.ofDirect Us.length familyName stats.params.size
                    generation.block.checked.indices.length directCtor := by
                simpa only [uvarsEq, paramsSizeEq,
                  generation.block.sourceType_name_eq, familyNameEq] using viewEq
              have stageFields : ∀ q field,
                  ctor.view.fields[q]? = some field →
                    VInductDecl.stage3Field Us.length familyName
                      stats.params.size
                      generation.block.checked.indices.length q field = true := by
                intro q field atIndex
                rw [viewEq'] at atIndex
                simpa only [Nat.zero_add] using
                  (VInductDecl.stage3Ctor_eq directStage).2.2.2 q field
                    (by simpa only [CheckedCtor.ofDirect] using atIndex)
              exact generationHead.checkedConstructorWF d3Head
                headAlignment d2Head hctor henv typeEnvWF addType
                parameterContext parameterWF parameterCtx d3State analyzerState
                ngenEq parametersEq indConsts familyTr
                familyUnique indexLength resultLevelTr absent unique.1
                universeSemantics.1 stageFields
            · exact ih d2Tail generationTail
                (fun ctor member => membership ctor (.tail _ member)) unique.2
                universeSemantics.2 ctor member

/-- The retained D1/D2/D3 producer traces derive the exact analyzer-owned
checked declaration semantics. -/
theorem StagedNormalizationCandidatePreFamilyInput.checkedWF
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {kernelSource : InductiveType}
    {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate source)
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    generation.block.checked.WF env := by
  let staged := input.postFamilyInput.universeInput.staged
  let validation := staged.family.validation
  obtain ⟨parameterΔ, terminalRun, viewTerminal, familyInstantiation,
      familyTr, parameterCtx, parameterContext, parameterFVars,
      parameterNoBV, parameterWF, terminalVenv, terminalLparams,
      terminalViewDefEq, terminalViewUnique, terminalViewLift,
      terminalViewEq⟩ :=
    input.familyContext normalization generation analysis shape
  have henv : VEnv.WF env := by
    simpa only [normalization.family.type.venv_eq] using
      normalization.family.type.contextRun.context.Ewf
  have rawWF : normalization.raw.toVConstant.WF env := by
    show env.IsType normalization.raw.uvars [] normalization.raw.type
    simpa only [normalization.family.uvars_eq] using
      normalization.family.type.source_isType_of_terminalSort
        validation.terminal_eq
  have typeEnvWF : VEnv.WF normalization.family.typeEnv := by
    obtain ⟨declarations, declarationsWF⟩ := henv
    exact ⟨.axiom normalization.raw.toVConstVal :: declarations,
      .decl (.axiom rawWF normalization.family.addType) declarationsWF⟩
  have rawEq : normalization.raw = staged.raw := by
    have singletonEq : [normalization.raw] = [staged.raw] :=
      normalization.raw_types_eq.symm.trans staged.raw_types_eq
    injection singletonEq
  have typeEnvEq : normalization.family.typeEnv = staged.family.typeEnv := by
    exact Option.some.inj <| normalization.family.addType.symm.trans (by
      simpa only [rawEq] using staged.family.addInduct.env_add)
  obtain ⟨validationRun, validationVenv, validationLparams,
      validationVlctx⟩ :=
    staged.family.validationContextRunFromPre terminalRun terminalVenv
      terminalLparams
  let d3ContextRun : AddInductive.ConstructorContextRun env Us
      candidate.families.singleton.familyType.type.trace.terminalContext :=
    ⟨terminalRun, terminalVenv, terminalLparams⟩
  let d2ContextRun : AddInductive.ConstructorContextRun
      normalization.family.typeEnv Us
      { candidate.families.singleton.familyType.type.trace.terminalContext with
        env := constructorContext.env } :=
    ⟨validationRun, validationVenv.trans typeEnvEq.symm,
      validationLparams⟩
  obtain ⟨d3Constructors⟩ :=
    AddInductive.ConstructorPreFamilyListSemanticRun.nonempty d3ContextRun
      input.safety.constructors
  obtain ⟨d2Constructors⟩ :=
    AddInductive.ConstructorPostFamilySemanticListRun.nonempty_of_alignment
      d2ContextRun input.postFamilyInput.alignment
      normalization.family.constructors
  let generationRuns := normalization.constructorGenerationRuns generation
    analysis shape
  have terminalWF : VLCtx.WF env Us.length
      terminalRun.context.vlctx := by
    simpa only [terminalVenv, terminalLparams] using terminalRun.context.Δwf
  have validationWF : VLCtx.WF normalization.family.typeEnv Us.length
      validationRun.context.vlctx := by
    simpa only [validationVenv, ← typeEnvEq, validationLparams] using
      validationRun.context.Δwf
  have viewTerminalWF : VLCtx.WF env Us.length viewTerminal :=
    (terminalViewDefEq.symm henv.ordered).wf
  have d3State : D3FullContextState env normalization.family.typeEnv Us
      candidate.families.singleton.familyType.type.trace.terminalContext
      parameterΔ parameterΔ terminalRun.context.vlctx viewTerminal .refl
      (.skipN .refl generation.block.checked.indices.length) := {
    commonWF := parameterWF
    commonNoBV := parameterNoBV
    fullWF := parameterWF.mono
      (VEnv.addConst_le normalization.family.addType)
    fullExtension := .refl
    actualWF := terminalWF
    viewDefEq := terminalViewDefEq
    viewUnique := terminalViewUnique
    viewExtension := terminalViewLift
    freshInvariant := fun _ present => .inl present }
  have analyzerState : AnalyzerPostContextState
      normalization.family.typeEnv Us parameterΔ validationRun.context.vlctx
      viewTerminal (.skipN .refl
        generation.block.checked.indices.length) := {
    fullWF := parameterWF.mono
      (VEnv.addConst_le normalization.family.addType)
    postWF := validationWF
    viewWF := viewTerminalWF.mono
      (VEnv.addConst_le normalization.family.addType)
    viewDefEq := by
      rw [validationVlctx]
      exact (terminalViewDefEq.mono
        (VEnv.addConst_le normalization.family.addType)).toFVars
    viewExtension := terminalViewLift }
  have parametersEq : validation.stats.params.toList =
      candidate.families.singleton.familyType.type.trace.parameterList
        source.nparams := by
    rw [validation.stats_eq]
    simp only [CandidateExprTrace.singletonCandidateInductiveStats,
      validation, staged, staged.validation_nparams_eq]
  have paramsSizeEq : validation.stats.params.size = source.nparams := by
    calc
      validation.stats.params.size =
          validation.stats.params.toList.length := by simp
      _ = (candidate.families.singleton.familyType.type.trace.parameterList
          source.nparams).length := congrArg List.length parametersEq
      _ = generation.block.checked.params.length :=
        parameterContext.length_eq
      _ = source.nparams :=
        generation.block.checked.direct_anatomy.2.1.trans
          generation.block.nparams_eq.symm
  have sourceTypeEq : generation.block.sourceType = normalization.raw := by
    simpa only [NormalizationCandidateSemanticRun.root] using
      normalization.root.sourceType_eq generation
  have familyNameEq : generation.block.sourceType.name =
      generation.block.checked.type.name :=
    generation.block.sourceType_name_eq
  have familyLparams :
      candidate.families.singleton.familyType.type.context.lparams = Us := by
    exact normalization.family.type.contextRun.context_lparams.symm.trans
      normalization.family.type.lparams_eq
  have indConsts : validation.stats.indConsts =
      #[.const generation.block.sourceType.name (Us.map .param)] := by
    rw [validation.stats_eq]
    simp only [CandidateExprTrace.singletonCandidateInductiveStats,
      familyLparams]
    congr 2
    exact congrArg (fun name => Expr.const name (Us.map .param)) <|
      staged.family.name_eq.trans (congrArg
        (fun type : VInductiveType => type.name)
        (rawEq.symm.trans sourceTypeEq.symm))
  have familyUnique : TrExprS.IsUnique input.safety.familyIndices :=
    instantiateFamilyParameters_unique
      input.safety.familyTranslationUnique
      (ConstructorValidation.CandidateParameterContext.parametersUnique
        parameterContext) familyInstantiation
  have indexLength : generation.block.checked.indices.length =
      validation.stats.nindices[0]! :=
    (stagedIndexCount_eq input normalization generation analysis
      shape).symm
  have resultLevelTr : VLevel.ofLevel Us validation.stats.resultLevel =
      some generation.block.checked.resultLevel :=
    stagedResultLevel_tr input normalization generation analysis shape
  have absent : env.constants generation.block.sourceType.name = none := by
    rw [sourceTypeEq]
    exact VEnv.addConst_fresh normalization.family.addType
  have pairWF := generationRuns.checkedConstructorsWF
    d3Constructors d2Constructors (fun _ member => member) henv typeEnvWF
    (VEnv.addConst_le normalization.family.addType) parameterContext
    parameterWF parameterCtx d3State analyzerState rfl
    parametersEq indConsts familyTr familyUnique indexLength resultLevelTr
    absent input.safety.constructorTranslationUnique
    input.postFamilyInput.universeInput.universeSemantics
    normalization.uvars_eq familyNameEq paramsSizeEq
  refine ⟨by
    simpa only [generation.block.uvars_eq] using
      input.familyOnTel normalization generation analysis, ?_⟩
  intro ctor ctorMember
  have directMember :
      CheckedCtor.ofDirect generation.block.normalization.view.uvars
          generation.block.checked.type.name
          generation.block.normalization.view.nparams
          generation.block.checked.indices.length ctor ∈
        generation.block.checked.constructors := by
    rw [generation.block.checked.constructors_eq]
    exact List.mem_map.2 ⟨ctor, ctorMember, rfl⟩
  rw [← generation.viewCtors_eq] at directMember
  obtain ⟨pair, pairMember, pairViewEq⟩ := List.mem_map.1 directMember
  have result := pairWF pair pairMember
  rw [pairViewEq] at result
  have viewUvarsEq : generation.block.normalization.view.uvars = Us.length :=
    generation.block.uvars_eq.symm.trans normalization.uvars_eq
  have dropBvarRevRange : ∀ (offset count : Nat) (suffix : List VExpr),
      (VExpr.bvarRevRange offset count ++ suffix).drop count = suffix := by
    intro offset count suffix
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [VExpr.bvarRevRange, List.cons_append,
          List.drop_succ_cons]
        exact ih
  rw [← viewUvarsEq, paramsSizeEq, generation.block.nparams_eq,
    familyNameEq] at result
  simpa only [
    generation.block.nparams_eq, pairViewEq,
    CheckedCtor.ofDirect, NormalizedCtor.resultTarget,
    VInductDecl.recFieldIdxs, VExpr.appArgs_appN, VExpr.appArgs,
    List.append_nil, dropBvarRevRange] using result

/-- Re-index the derived checked semantics onto the exact normalization view
selected by dependent analysis. -/
theorem StagedNormalizationCandidatePreFamilyInput.viewDeclWF
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {kernelSource : InductiveType}
    {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate source)
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    normalization.root.viewDecl.WF env := by
  have checkedWF := input.checkedWF normalization generation analysis shape
  have normalizationEq : generation.block.normalization =
      normalization.root.normalization :=
    Normalization.generation?_normalization analysis
  have viewEq : generation.block.normalization.view =
      normalization.root.viewDecl := by
    simpa only [NormalizationCandidateRun.normalization] using
      congrArg (fun normalized : Normalization source => normalized.view)
        normalizationEq
  rw [← viewEq]
  exact generation.block.checked.to_declWF generation.block.checked_eq
    checkedWF

/-- Build the semantic generation owner from the retained D1/D2/D3 input,
exact dependent analysis, and the single executable hierarchy shape check.
The analyzer-owned checked semantics are derived from those traces rather
than accepted as a premise. -/
def GenerationCandidateSemanticRun.ofGenerationShape
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate source)
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    GenerationCandidateSemanticRun normalization generation := by
  have familyShape := shape
  simp only [NormalizationCandidateSemanticRun.generationShape,
    normalizationCandidateGenerationShape, Bool.and_eq_true,
    beq_iff_eq] at familyShape
  have sourceTypeEq : generation.block.sourceType = normalization.raw := by
    simpa only [NormalizationCandidateSemanticRun.root] using
      normalization.root.sourceType_eq generation
  apply GenerationCandidateSemanticShapeRun.run {
    analysis := analysis
    checked := input.checkedWF normalization generation analysis shape
    family := {
      storedSpine := familyShape.1.1
      spineLength_eq := by
        simpa only [NormalizedChecked.rawParams,
          NormalizedChecked.rawIndices, sourceTypeEq] using familyShape.1.2 }
    constructors :=
      CandidateConstructorSemanticGenerationShapeList.ofCheck
        normalization.family.constructors familyShape.2 }

/-- Construct the produced package at the consolidated generation-shape
boundary without accepting a checked- or view-WF premise. -/
def NormalizationCandidateSemanticRun.producedPackageOfGenerationShape
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate source)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true)
    (context : AddInductive.Context)
    (nparams numNested : Nat) (isUnsafe : Bool)
    (produced :
      AddInductive.buildNormalizationCandidate nparams
          [kernelSource] numNested isUnsafe context = .ok candidate) :
    ProducedGenerationCandidatePackage env Us :=
  (GenerationCandidateSemanticRun.ofGenerationShape input normalization
    generation analysis shape).producedPackage context nparams numNested
      isUnsafe produced

/-- Interpret one successful shape-producing outer result using the matching
retained D1/D2/D3 semantic input. -/
def ProducedGenerationShapeCandidate.producedPackage
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {raw : VInductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (producedCandidate : ProducedGenerationShapeCandidate source raw
      kernelSource numNested isUnsafe context)
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us producedCandidate.candidate source)
    (normalization : NormalizationCandidateSemanticRun env Us
      producedCandidate.candidate source)
    (rawEq : raw = normalization.raw)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation) :
    ProducedGenerationCandidatePackage env Us :=
  normalization.producedPackageOfGenerationShape input generation analysis
    (by
      simpa only [NormalizationCandidateSemanticRun.generationShape,
        rawEq] using producedCandidate.shape)
    context source.nparams numNested isUnsafe producedCandidate.produced

/-- Projection-free D3 candidates determine one exact Theory constructor
view at every source position, independently of the existential checker run
that selected it. -/
theorem CandidateConstructorSemanticListRun.roots_views_eq
    {env : VEnv} {Us : List Name} {constructors : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors}
    {raws : List VConstVal}
    (unique : candidates.ViewTranslationUnique)
    (left right : CandidateConstructorSemanticListRun env Us candidates raws) :
    left.roots.views = right.roots.views := by
  induction left with
  | nil =>
      cases right
      rfl
  | @cons constructor constructors candidate candidates raw raws head tail ih =>
      cases right with
      | cons otherHead otherTail =>
          obtain ⟨_, headRecursive⟩ := head.type.recursive
          obtain ⟨_, otherHeadRecursive⟩ := otherHead.type.recursive
          have headViewEq : head.type.view = otherHead.type.view :=
            TrExprS.unique unique.1.view
              (headRecursive.view_tr_strict unique.1)
              (otherHeadRecursive.view_tr_strict unique.1)
          have tailViewsEq := ih unique.2 otherTail
          simp only [CandidateConstructorSemanticListRun.roots,
            CandidateConstructorListRun.views,
            CandidateConstructorSemanticRun.root,
            CandidateConstructorRun.view]
          rw [headViewEq, tailViewsEq]

/-- Transport the positional uniqueness theorem across the uniquely produced
post-family environment and raw constructor list. -/
theorem CandidateConstructorSemanticListRun.roots_views_eq_of_eq
    {leftEnv rightEnv : VEnv} {Us : List Name}
    {constructors : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors}
    {leftRaws rightRaws : List VConstVal}
    (unique : candidates.ViewTranslationUnique)
    (envEq : leftEnv = rightEnv) (rawsEq : leftRaws = rightRaws)
    (left : CandidateConstructorSemanticListRun leftEnv Us candidates leftRaws)
    (right : CandidateConstructorSemanticListRun rightEnv Us candidates
      rightRaws) :
    left.roots.views = right.roots.views := by
  subst rightEnv
  subst rightRaws
  exact left.roots_views_eq unique right

private theorem candidateFamilyView_eq_of_components
    {rawLeft rawRight : VInductiveType}
    {typeLeft typeRight : VExpr}
    {ctorsLeft ctorsRight : List VConstVal}
    (rawEq : rawLeft = rawRight) (typeEq : typeLeft = typeRight)
    (ctorsEq : ctorsLeft = ctorsRight) :
    ({ rawLeft with type := typeLeft, ctors := ctorsLeft } :
        VInductiveType) =
      { rawRight with type := typeRight, ctors := ctorsRight } := by
  cases rawEq
  cases typeEq
  cases ctorsEq
  rfl

private theorem Normalization.eq_of_view_eq
    {source : VInductDecl} {left right : Normalization source}
    (viewEq : left.view = right.view) : left = right := by
  cases left with
  | mk leftView leftShape =>
      cases right with
      | mk rightView rightShape =>
          cases viewEq
          rfl

/-- The D3 projection-free safety gate makes the complete normalization
selected by the staged semantic owner syntactically unique.  In particular,
fixtures may state dependent analysis once for the known normalization and
transport it to whichever semantic hierarchy `input.exists` selects. -/
theorem StagedNormalizationCandidatePreFamilyInput.normalization_eq
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate source)
    (left right : NormalizationCandidateSemanticRun env Us candidate source) :
    left.root.normalization = right.root.normalization := by
  have rawEq : left.raw = right.raw := by
    have singletonEq := left.raw_types_eq.symm.trans right.raw_types_eq
    injection singletonEq
  have typeEnvEq : left.family.typeEnv = right.family.typeEnv := by
    exact Option.some.inj <| left.family.addType.symm.trans <| by
      simpa only [rawEq] using right.family.addType
  have familyViewEq : left.family.type.view = right.family.type.view := by
    obtain ⟨_, leftRecursive⟩ := left.family.type.recursive
    obtain ⟨_, rightRecursive⟩ := right.family.type.recursive
    exact TrExprS.unique input.safety.familyTranslationUnique
      (leftRecursive.view_tr_strict <|
        AddInductive.CandidateExprTrace.viewTranslationUnique_sound _ <| by
          rw [AddInductive.CandidateExprTrace.viewTranslationUnique_eq]
          have gate := input.safety.translationUnique
          simp only [Bool.and_eq_true] at gate
          exact gate.1)
      (rightRecursive.view_tr_strict <|
        AddInductive.CandidateExprTrace.viewTranslationUnique_sound _ <| by
          rw [AddInductive.CandidateExprTrace.viewTranslationUnique_eq]
          have gate := input.safety.translationUnique
          simp only [Bool.and_eq_true] at gate
          exact gate.1)
  have constructorViewsEq : left.family.constructors.roots.views =
      right.family.constructors.roots.views := by
    exact left.family.constructors.roots_views_eq_of_eq
      input.safety.constructorTranslationUnique typeEnvEq
      (congrArg VInductiveType.ctors rawEq) right.family.constructors
  have familyEq : left.family.root.view = right.family.root.view := by
    exact candidateFamilyView_eq_of_components rawEq familyViewEq
      constructorViewsEq
  have viewDeclEq : left.root.viewDecl = right.root.viewDecl := by
    simp only [NormalizationCandidateSemanticRun.root,
      NormalizationCandidateRun.viewDecl]
    rw [familyEq]
  exact Normalization.eq_of_view_eq viewDeclEq

/-- Choice-free constructor-root interpretation: the semantic root's view is
computed by the deterministic translator under the constructor's strict-view
uniqueness certificate. -/
def CandidateConstructorSemanticInput.semanticOfUnique
    {env : VEnv} {Us : List Name} {source : Constructor}
    {candidate : AddInductive.CandidateConstructor source} {raw : VConstVal}
    (input : CandidateConstructorSemanticInput env Us candidate raw)
    (unique : TypeChecker.CandidateExprTraceViewIsUnique
      candidate.type.trace) :
    CandidateConstructorSemanticRun env Us candidate raw where
  name_eq := input.name_eq
  uvars_eq := input.uvars_eq
  type := input.type.semanticOfUnique unique

/-- Choice-free source-ordered interpretation of a complete constructor list
under its source-ordered strict-view certificate. -/
def CandidateConstructorSemanticListInput.semanticOfUnique
    {env : VEnv} {Us : List Name} :
    {sources : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources} →
    {raws : List VConstVal} →
    CandidateConstructorSemanticListInput env Us candidates raws →
    candidates.ViewTranslationUnique →
    CandidateConstructorSemanticListRun env Us candidates raws
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons head tail, unique =>
    .cons (head.semanticOfUnique unique.1) (tail.semanticOfUnique unique.2)

/-- Choice-free family interpretation: the family type and every
post-insertion constructor view are computed by the deterministic
translator. -/
def CandidateFamilySemanticInput.semanticOfUnique
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.CandidateFamily source} {raw : VInductiveType}
    (input : CandidateFamilySemanticInput env Us candidate raw)
    (uniqueType : TypeChecker.CandidateExprTraceViewIsUnique
      candidate.familyType.type.trace)
    (uniqueCtors : candidate.constructors.ViewTranslationUnique) :
    CandidateFamilySemanticRun env Us candidate raw where
  name_eq := input.name_eq
  uvars_eq := input.uvars_eq
  type := input.type.semanticOfUnique uniqueType
  typeEnv := input.typeEnv
  addType := input.addType
  constructors := input.constructors.semanticOfUnique uniqueCtors

/-- Choice-free singleton semantic hierarchy: every normalized Theory view
in the family and constructor list is computed by the deterministic
translator, with `Nonempty` interpretation transferred onto the computed
values. -/
def NormalizationCandidateSemanticInput.semanticOfUnique
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : NormalizationCandidateSemanticInput env Us candidate rawDecl)
    (uniqueType : TypeChecker.CandidateExprTraceViewIsUnique
      candidate.families.singleton.familyType.type.trace)
    (uniqueCtors :
      candidate.families.singleton.constructors.ViewTranslationUnique) :
    NormalizationCandidateSemanticRun env Us candidate rawDecl where
  raw := input.raw
  raw_types_eq := input.raw_types_eq
  uvars_eq := input.uvars_eq
  family := input.family.semanticOfUnique uniqueType uniqueCtors

/-- The executable D3 gate's uniqueness Bool supplies the family strict-view
certificate consumed by the choice-free semantic assembly. -/
theorem StagedNormalizationCandidatePreFamilyInput.familyViewUnique
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl) :
    TypeChecker.CandidateExprTraceViewIsUnique
      candidate.families.singleton.familyType.type.trace := by
  have h := input.safety.translationUnique
  simp only [Bool.and_eq_true] at h
  exact AddInductive.CandidateExprTrace.viewTranslationUnique_sound _
    ((AddInductive.CandidateExprTrace.viewTranslationUnique_eq _).trans h.1)

/-- The executable D3 gate's uniqueness Bool likewise supplies the
constructor-list strict-view certificate. -/
theorem StagedNormalizationCandidatePreFamilyInput.constructorViewsUnique
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us candidate rawDecl) :
    candidate.families.singleton.constructors.ViewTranslationUnique := by
  have h := input.safety.translationUnique
  simp only [Bool.and_eq_true] at h
  exact AddInductive.CandidateList.viewTranslationUnique_sound _ h.2

/-- Exact, source-indexed refinement of the public producer package.

The public `ProducedGenerationCandidatePackage` deliberately erases its
dependent source, normalization, and generation indices.  Keeping those
indices in this closure result lets clients choose the `Nonempty` witness and
still recover a package whose projections reduce to the requested source and
generation. -/
structure ExactProducedGenerationCandidatePackage
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (env : VEnv) (Us : List Name)
    (producedCandidate : ProducedGenerationShapeCandidate source raw
      kernelSource numNested isUnsafe context)
    (generation : GenerationChecked source) where
  normalization : NormalizationCandidateSemanticRun env Us
    producedCandidate.candidate source
  raw_eq : raw = normalization.raw
  semantic : GenerationCandidateSemanticRun normalization generation

/-- Erase only the exact dependent indices retained by the generic closure.
The ordinary producer equation is copied from the same strengthened producer
value; it contributes provenance, not semantic authority. -/
def ExactProducedGenerationCandidatePackage.package
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context} {env : VEnv} {Us : List Name}
    {producedCandidate : ProducedGenerationShapeCandidate source raw
      kernelSource numNested isUnsafe context}
    {generation : GenerationChecked source}
    (exact : ExactProducedGenerationCandidatePackage env Us
      producedCandidate generation) :
    ProducedGenerationCandidatePackage env Us :=
  exact.semantic.producedPackage context source.nparams numNested isUnsafe
    producedCandidate.produced

/-- Close one strengthened singleton producer choice-free.  The semantic
hierarchy is computed by the deterministic translator under the executable
D3 strict-view gate carried by the staged owner, so the retained package is
data rather than a `Classical.choice` selection from `Nonempty`. -/
def ProducedGenerationShapeCandidate.exactProducedPackage
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {raw : VInductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (producedCandidate : ProducedGenerationShapeCandidate source raw
      kernelSource numNested isUnsafe context)
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us producedCandidate.candidate source)
    (rawOwnerEq : raw =
      input.postFamilyInput.universeInput.staged.raw)
    (generation : GenerationChecked source)
    (analysis : ∀ normalization : NormalizationCandidateSemanticRun env Us
        producedCandidate.candidate source,
      normalization.root.normalization.generation? = some generation) :
    ExactProducedGenerationCandidatePackage env Us
      producedCandidate generation :=
  let normalization :=
    input.postFamilyInput.universeInput.staged.semanticInput.semanticOfUnique
      input.familyViewUnique input.constructorViewsUnique
  { normalization := normalization
    raw_eq := rawOwnerEq
    semantic := GenerationCandidateSemanticRun.ofGenerationShape input
      normalization generation (analysis normalization)
      (by
        have hraw : normalization.raw =
            input.postFamilyInput.universeInput.staged.raw := rfl
        simpa only [NormalizationCandidateSemanticRun.generationShape,
          rawOwnerEq, hraw] using producedCandidate.shape) }

/-- Close one strengthened singleton producer from the staged D1--D4 owner
without choosing a semantic hierarchy at the API boundary, while retaining
the exact dependent source and generation indices needed by consumers. -/
theorem ProducedGenerationShapeCandidate.exactProducedPackage_nonempty
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {raw : VInductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (producedCandidate : ProducedGenerationShapeCandidate source raw
      kernelSource numNested isUnsafe context)
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us producedCandidate.candidate source)
    (rawOwnerEq : raw =
      input.postFamilyInput.universeInput.staged.raw)
    (generation : GenerationChecked source)
    (analysis : ∀ normalization : NormalizationCandidateSemanticRun env Us
        producedCandidate.candidate source,
      normalization.root.normalization.generation? = some generation) :
    Nonempty (ExactProducedGenerationCandidatePackage env Us
      producedCandidate generation) := by
  obtain ⟨preFamily⟩ := input.exists
  let normalization := preFamily.postFamily.produced.semantic
  have semanticRawEq : normalization.raw =
      input.postFamilyInput.universeInput.staged.raw := by
    have singletonEq := normalization.raw_types_eq.symm.trans
      input.postFamilyInput.universeInput.staged.raw_types_eq
    injection singletonEq
  have rawEq := rawOwnerEq.trans semanticRawEq.symm
  let semantic := GenerationCandidateSemanticRun.ofGenerationShape input
    normalization generation (analysis normalization) (by
      simpa only [NormalizationCandidateSemanticRun.generationShape,
        rawEq] using producedCandidate.shape)
  exact ⟨{ normalization, raw_eq := rawEq, semantic }⟩

/-- Close one strengthened singleton producer from the staged D1--D4 owner
without choosing a semantic hierarchy at the API boundary.

`analysis` is exact for every checker-selected semantic normalization owned by
the staged input.  The proof eliminates `input.exists` only into `Nonempty`,
then applies D4 to that exact selected normalization.  The ordinary producer
equation and the independent generation-shape gate remain the two fields of
`producedCandidate`; neither supplies Theory meaning by itself. -/
theorem ProducedGenerationShapeCandidate.producedPackage_nonempty
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {raw : VInductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (producedCandidate : ProducedGenerationShapeCandidate source raw
      kernelSource numNested isUnsafe context)
    (input : StagedNormalizationCandidatePreFamilyInput familyContext
      constructorContext env Us producedCandidate.candidate source)
    (rawOwnerEq : raw =
      input.postFamilyInput.universeInput.staged.raw)
    (generation : GenerationChecked source)
    (analysis : ∀ normalization : NormalizationCandidateSemanticRun env Us
        producedCandidate.candidate source,
      normalization.root.normalization.generation? = some generation) :
    Nonempty (ProducedGenerationCandidatePackage env Us) := by
  obtain ⟨exact⟩ := producedCandidate.exactProducedPackage_nonempty input
    rawOwnerEq generation analysis
  exact ⟨exact.package⟩

end VInductDecl

namespace VInductDecl

/- The D4 closure roots intentionally inherit the exact transitional Verify
axiom set already present in the staged semantic inputs. -/
#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidatePreFamilyInput.checkedWF [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidatePreFamilyInput.viewDeclWF [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateSemanticRun.ofGenerationShape [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateSemanticRun.producedPackageOfGenerationShape [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.ProducedGenerationShapeCandidate.producedPackage [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.ProducedGenerationShapeCandidate.exactProducedPackage_nonempty [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidatePreFamilyInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidatePostFamilyInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

/- The wrapper projections expose their exact existing Verify closure.  The
new universe bridge itself remains separately guarded above; staging does not
hide the transitional dependencies already present in the semantic owner. -/
#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidateUniverseInput.semanticValidation [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidateUniverseInput.universeSemantics [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidateUniverseInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

end VInductDecl
end Ix.Theory.Named
