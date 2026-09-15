/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Reference.Inductive.ValidationTrace

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

namespace AddInductive
open TypeChecker

/-- Exact successful traversal of the singleton-constructor branch of
`isLargeEliminator`. Non-parameter fields retain the precise `ensureType`
observation used to decide whether their local is relevant to the terminal
index-occurrence check. -/
inductive LargeEliminatorLoopTrace (stats : InductiveStats) :
    (context : Context) → (source : Expr) → (argIdx : Nat) →
      (toCheck : Array Expr) → (fuel : Nat) → (result : Bool) → Type where
  | parameter
      (context : Context) (fuel argIdx : Nat) (toCheck : Array Expr)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (isParameter : argIdx < stats.params.size)
      (tail : LargeEliminatorLoopTrace stats
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) toCheck fuel result) :
      LargeEliminatorLoopTrace stats context
        (.forallE name domain body binderInfo) argIdx toCheck (fuel + 1) result
  | proofField
      (context : Context) (fuel argIdx : Nat) (toCheck : Array Expr)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (sortResult : Expr)
      (isField : argIdx ≥ stats.params.size)
      (ensureType : ConstructorEnsureTypeStep.Valid
        ⟨context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain), domain, sortResult⟩)
      (isProp : sortResult.sortLevel!.isAlwaysZero = true)
      (tail : LargeEliminatorLoopTrace stats
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) toCheck fuel result) :
      LargeEliminatorLoopTrace stats context
        (.forallE name domain body binderInfo) argIdx toCheck (fuel + 1) result
  | dataField
      (context : Context) (fuel argIdx : Nat) (toCheck : Array Expr)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (sortResult : Expr)
      (isField : argIdx ≥ stats.params.size)
      (ensureType : ConstructorEnsureTypeStep.Valid
        ⟨context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain), domain, sortResult⟩)
      (isProp : sortResult.sortLevel!.isAlwaysZero = false)
      (tail : LargeEliminatorLoopTrace stats
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1)
        (toCheck.push context.freshExpr) fuel result) :
      LargeEliminatorLoopTrace stats context
        (.forallE name domain body binderInfo) argIdx toCheck (fuel + 1) result
  | terminal
      (context : Context) (source : Expr) (fuel argIdx : Nat)
      (toCheck : Array Expr) (notForall : source.isForall = false) :
      LargeEliminatorLoopTrace stats context source argIdx toCheck (fuel + 1)
        (toCheck.all source.getAppArgs.contains)

namespace LargeEliminatorLoopTrace

def parameterCount
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.parameterCount + 1
  | .proofField (tail := tail) .. => tail.parameterCount
  | .dataField (tail := tail) .. => tail.parameterCount
  | .terminal .. => 0

def proofFieldCount
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.proofFieldCount
  | .proofField (tail := tail) .. => tail.proofFieldCount + 1
  | .dataField (tail := tail) .. => tail.proofFieldCount
  | .terminal .. => 0

def dataFieldCount
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.dataFieldCount
  | .proofField (tail := tail) .. => tail.dataFieldCount
  | .dataField (tail := tail) .. => tail.dataFieldCount + 1
  | .terminal .. => 0

/-- Erasing the retained singleton trace replays the exact ordinary checker
loop, including every `ensureType` call and local declaration. -/
theorem run
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) :
    isLargeEliminator.loop stats source argIdx toCheck fuel context =
      .ok result := by
  induction trace with
  | parameter context fuel argIdx toCheck name domain body binderInfo
      isParameter tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [isLargeEliminator.loop.eq_2, withLocalDecl_apply]
      have notField : ¬ argIdx ≥ stats.params.size :=
        Nat.not_le.mpr isParameter
      simp only [notField, if_false, Bind.bind]
      exact ih
  | proofField context fuel argIdx toCheck name domain body binderInfo
      sortResult isField ensureStep isProp tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [isLargeEliminator.loop.eq_2, withLocalDecl_apply]
      simp only [isField, if_true, ReaderT.bind, Bind.bind,
        liftTypeChecker_apply]
      rw [ensureStep]
      simp only [Except.bind, isProp, Bool.not_true, Bool.false_eq_true, if_false]
      exact ih
  | dataField context fuel argIdx toCheck name domain body binderInfo
      sortResult isField ensureStep isProp tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [isLargeEliminator.loop.eq_2, withLocalDecl_apply]
      simp only [isField, if_true, ReaderT.bind, Bind.bind,
        liftTypeChecker_apply]
      rw [ensureStep]
      simp only [Except.bind, isProp, Bool.not_false, if_true]
      exact ih
  | terminal context source fuel argIdx toCheck notForall =>
      cases source <;>
        simp_all [isLargeEliminator.loop, ReaderT.pure, Pure.pure,
          Except.pure, Expr.isForall]

/-- Execute the singleton branch once while retaining the exact branch and
checker observations that produced its Boolean result. -/
def buildExecution (stats : InductiveStats) (context : Context)
    (source : Expr) (argIdx : Nat) (toCheck : Array Expr) :
    (fuel : Nat) → Except Exception
      (Sigma fun result => LargeEliminatorLoopTrace stats context source
        argIdx toCheck fuel result)
  | 0 => .error .deepRecursion
  | fuel + 1 =>
      match hforall : source.isForall with
      | false => .ok ⟨toCheck.all source.getAppArgs.contains,
          .terminal context source fuel argIdx toCheck hforall⟩
      | true =>
        match source with
        | .forallE name domain body binderInfo =>
          let nextContext := context.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain)
          let nextSource := body.instantiate1 context.freshExpr
          if isParameter : argIdx < stats.params.size then
            match buildExecution stats nextContext nextSource (argIdx + 1)
                toCheck fuel with
            | .error error => .error error
            | .ok ⟨result, tail⟩ => .ok ⟨result,
                .parameter context fuel argIdx toCheck name domain body
                  binderInfo isParameter tail⟩
          else
            match hensure : TypeChecker.M.run nextContext.env nextContext.safety
                nextContext.lctx nextContext.lparams nextContext.fuel
                (TypeChecker.ensureType domain) with
            | .error error => .error error
            | .ok sortResult =>
                if isProp : sortResult.sortLevel!.isAlwaysZero then
                  match buildExecution stats nextContext nextSource
                      (argIdx + 1) toCheck fuel with
                  | .error error => .error error
                  | .ok ⟨result, tail⟩ => .ok ⟨result,
                      .proofField context fuel argIdx toCheck name domain body
                        binderInfo sortResult (Nat.le_of_not_gt isParameter)
                        hensure isProp tail⟩
                else
                  match buildExecution stats nextContext nextSource
                      (argIdx + 1) (toCheck.push context.freshExpr) fuel with
                  | .error error => .error error
                  | .ok ⟨result, tail⟩ => .ok ⟨result,
                      .dataField context fuel argIdx toCheck name domain body
                        binderInfo sortResult (Nat.le_of_not_gt isParameter)
                        hensure (by
                          cases h : sortResult.sortLevel!.isAlwaysZero <;> simp_all)
                        tail⟩
        | _ => .error <| .other
            "large-eliminator source shape disagrees with isForall"

end LargeEliminatorLoopTrace

/-- The source identity and exact loop retained when the singleton branch of
`isLargeEliminator` is selected. -/
structure LargeEliminatorSingletonExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) (result : Bool) where
  indType : InductiveType
  indTypes_eq : indTypes = #[indType]
  ctor : Constructor
  ctors_eq : indType.ctors = [ctor]
  trace : LargeEliminatorLoopTrace stats context ctor.type 0 #[]
    context.fuel.inductiveFuel result

/-- One exact successful execution of `isLargeEliminator`. The ordinary
equation is always retained; the singleton payload additionally exposes all
field-sort observations made by the executable. -/
structure LargeEliminatorExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) where
  result : Bool
  singleton : Option
    (LargeEliminatorSingletonExecution stats indTypes context result)
  run_eq : isLargeEliminator stats indTypes context = .ok result

namespace LargeEliminatorExecution

/-- Execute the ordinary decision and retain a transparent refinement of its
singleton traversal. -/
def buildExecution (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) :
    Except Exception (LargeEliminatorExecution stats indTypes context) :=
  match hrun : isLargeEliminator stats indTypes context with
  | .error error => .error error
  | .ok result =>
      if stats.isNotZero then
        .ok { result, singleton := none, run_eq := hrun }
      else
        match htypes : indTypes with
        | #[indType] =>
            match hctors : indType.ctors with
            | [ctor] =>
                match LargeEliminatorLoopTrace.buildExecution stats context
                    ctor.type 0 #[] context.fuel.inductiveFuel with
                | .error error => .error error
                | .ok ⟨traceResult, trace⟩ =>
                    if hsame : traceResult = result then
                      .ok {
                        result
                        singleton := some {
                          indType
                          indTypes_eq := rfl
                          ctor
                          ctors_eq := hctors
                          trace := hsame ▸ trace }
                        run_eq := by simpa only [htypes] using hrun }
                    else
                      .error <| .other
                        "large-eliminator trace disagrees with ordinary result"
            | _ => .ok {
                result
                singleton := none
                run_eq := by simpa only [htypes] using hrun }
        | _ => .ok {
            result
            singleton := none
            run_eq := by simpa only [htypes] using hrun }

end LargeEliminatorExecution

/-- Exact `getElimLevel` execution paired with the retained large-elimination
decision that controls it. `level_eq` exposes both the zero and fresh-parameter
branches without unfolding the monadic checker again. -/
structure ElimLevelExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) where
  large : LargeEliminatorExecution stats indTypes context
  level : Level
  level_eq : level = if large.result then
    .param (getFreshElimParam context.lparams) else .zero
  run_eq : getElimLevel stats indTypes context = .ok level

namespace ElimLevelExecution

/-- Recompose `getElimLevel` from the retained exact large-elimination run. -/
theorem run_of_large
    (large : LargeEliminatorExecution stats indTypes context) :
    getElimLevel stats indTypes context = .ok
      (if large.result then .param (getFreshElimParam context.lparams)
        else .zero) := by
  unfold getElimLevel
  simp only [ReaderT.bind, Bind.bind]
  rw [large.run_eq]
  cases large.result <;> rfl

def buildExecution (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) :
    Except Exception (ElimLevelExecution stats indTypes context) := do
  let large ← LargeEliminatorExecution.buildExecution stats indTypes context
  let level := if large.result then
    .param (getFreshElimParam context.lparams) else .zero
  pure {
    large
    level
    level_eq := rfl
    run_eq := run_of_large large }

theorem level_eq_zero (execution : ElimLevelExecution stats indTypes context)
    (small : execution.large.result = false) :
    execution.level = .zero := by
  rw [execution.level_eq, small]
  rfl

theorem level_eq_param
    (execution : ElimLevelExecution stats indTypes context)
    (large : execution.large.result = true) :
    execution.level = .param (getFreshElimParam context.lparams) := by
  rw [execution.level_eq, large]
  rfl

/-- A small eliminator preserves the source universe-level order in recursor
applications. -/
theorem recLevels_eq_small
    (execution : ElimLevelExecution stats indTypes context)
    (small : execution.large.result = false) (levels : List Level) :
    getRecLevels execution.level levels = levels := by
  rw [execution.level_eq_zero small]
  rfl

/-- A large eliminator prepends its fresh elimination level to every source
universe used by recursive calls. -/
theorem recLevels_eq_large
    (execution : ElimLevelExecution stats indTypes context)
    (large : execution.large.result = true) (levels : List Level) :
    getRecLevels execution.level levels =
      .param (getFreshElimParam context.lparams) :: levels := by
  rw [execution.level_eq_param large]
  rfl

/-- A small eliminator preserves the stored source level-parameter order. -/
theorem recLevelParams_eq_small
    (execution : ElimLevelExecution stats indTypes context)
    (small : execution.large.result = false) (lparams : List Name) :
    getRecLevelParams execution.level lparams = lparams := by
  rw [execution.level_eq_zero small]
  rfl

/-- A large eliminator stores the fresh elimination parameter before every
source level parameter. -/
theorem recLevelParams_eq_large
    (execution : ElimLevelExecution stats indTypes context)
    (large : execution.large.result = true) (lparams : List Name) :
    getRecLevelParams execution.level lparams =
      getFreshElimParam context.lparams :: lparams := by
  rw [execution.level_eq_param large]
  rfl

end ElimLevelExecution

/-- Exact traversal of the constructor-shape fragment of `isKTarget`. The
trace stops at the first visible non-parameter binder, just as the executable
does; it never treats K eligibility as evidence for large elimination. -/
inductive KTargetCtorTrace (nparams : Nat) :
    (source : Expr) → (argIdx : Nat) → (result : Bool) → Type where
  | parameter
      (argIdx : Nat) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (isParameter : argIdx < nparams)
      (tail : KTargetCtorTrace nparams body (argIdx + 1) result) :
      KTargetCtorTrace nparams (.forallE name domain body binderInfo)
        argIdx result
  | field
      (argIdx : Nat) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (isField : argIdx ≥ nparams) :
      KTargetCtorTrace nparams (.forallE name domain body binderInfo)
        argIdx false
  | terminal
      (source : Expr) (argIdx : Nat)
      (notForall : source.isForall = false) :
      KTargetCtorTrace nparams source argIdx true

namespace KTargetCtorTrace

def parameterCount
    (trace : KTargetCtorTrace nparams source argIdx result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.parameterCount + 1
  | .field .. => 0
  | .terminal .. => 0

/-- The K-target walk stops at the first visible constructor field, so this
count is either zero or one. -/
def fieldCount
    (trace : KTargetCtorTrace nparams source argIdx result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.fieldCount
  | .field .. => 1
  | .terminal .. => 0

/-- Erasing the retained constructor trace yields the exact Boolean consumed
by `isKTarget`. -/
theorem run
    (trace : KTargetCtorTrace nparams source argIdx result) :
    isKTargetCtor nparams argIdx source = result := by
  induction trace with
  | parameter argIdx name domain body binderInfo isParameter tail ih =>
      simp [isKTargetCtor, isParameter, ih]
  | field argIdx name domain body binderInfo isField =>
      have notParameter : ¬ argIdx < nparams := Nat.not_lt.mpr isField
      simp [isKTargetCtor, notParameter]
  | terminal source argIdx notForall =>
      cases source <;> simp_all [isKTargetCtor, Expr.isForall]

/-- Compute the K-target constructor branch while retaining the exact point
where the parameter prefix ends. -/
def buildExecution (nparams : Nat) :
    (source : Expr) → (argIdx : Nat) →
      Sigma fun result => KTargetCtorTrace nparams source argIdx result
  | .bvar i, argIdx => ⟨true, .terminal (.bvar i) argIdx rfl⟩
  | .fvar id, argIdx => ⟨true, .terminal (.fvar id) argIdx rfl⟩
  | .mvar id, argIdx => ⟨true, .terminal (.mvar id) argIdx rfl⟩
  | .sort level, argIdx => ⟨true, .terminal (.sort level) argIdx rfl⟩
  | .const name levels, argIdx =>
      ⟨true, .terminal (.const name levels) argIdx rfl⟩
  | .app fn arg, argIdx => ⟨true, .terminal (.app fn arg) argIdx rfl⟩
  | .lam name domain body binderInfo, argIdx =>
      ⟨true, .terminal (.lam name domain body binderInfo) argIdx rfl⟩
  | .forallE name domain body binderInfo, argIdx =>
      if isParameter : argIdx < nparams then
        let ⟨result, tail⟩ := buildExecution nparams body (argIdx + 1)
        ⟨result, .parameter argIdx name domain body binderInfo
          isParameter tail⟩
      else
        ⟨false, .field argIdx name domain body binderInfo
          (Nat.le_of_not_gt isParameter)⟩
  | .letE name type value body nondep, argIdx =>
      ⟨true, .terminal (.letE name type value body nondep) argIdx rfl⟩
  | .lit literal, argIdx => ⟨true, .terminal (.lit literal) argIdx rfl⟩
  | .mdata data expr, argIdx =>
      ⟨true, .terminal (.mdata data expr) argIdx rfl⟩
  | .proj typeName idx struct, argIdx =>
      ⟨true, .terminal (.proj typeName idx struct) argIdx rfl⟩

end KTargetCtorTrace

/-- The singleton-Prop branch data of one exact `isKTarget` execution. -/
structure KTargetSingletonExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (result : Bool) where
  indType : InductiveType
  indTypes_eq : indTypes = #[indType]
  resultLevelZero : stats.resultLevel.isAlwaysZero = true
  ctor : Constructor
  ctors_eq : indType.ctors = [ctor]
  trace : KTargetCtorTrace stats.params.size ctor.type 0 result

/-- One exact successful execution of `isKTarget`. The ordinary monadic
equation is always retained; a singleton candidate additionally exposes the
constructor-prefix trace that decided its flag. -/
structure KTargetExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) where
  result : Bool
  singleton : Option (KTargetSingletonExecution stats indTypes result)
  run_eq : isKTarget stats indTypes context = .ok result

namespace KTargetExecution

def buildExecution (stats : InductiveStats)
    (indTypes : Array InductiveType) (context : Context) :
    Except Exception (KTargetExecution stats indTypes context) :=
  match hrun : isKTarget stats indTypes context with
  | .error error => .error error
  | .ok result =>
      match _htypes : indTypes with
      | #[indType] =>
          if hzero : stats.resultLevel.isAlwaysZero then
            match hctors : indType.ctors with
            | [ctor] =>
                let ⟨traceResult, trace⟩ :=
                  KTargetCtorTrace.buildExecution stats.params.size ctor.type 0
                if hsame : traceResult = result then
                  .ok {
                    result
                    singleton := some {
                      indType
                      indTypes_eq := rfl
                      resultLevelZero := hzero
                      ctor
                      ctors_eq := hctors
                      trace := hsame ▸ trace }
                    run_eq := hrun }
                else
                  .error <| .other
                    "K-target trace disagrees with ordinary result"
            | _ => .ok { result, singleton := none, run_eq := hrun }
          else
            .ok { result, singleton := none, run_eq := hrun }
      | _ => .ok { result, singleton := none, run_eq := hrun }

end KTargetExecution

/-- The normalization/validation execution extended through constructor
declaration and the exact elimination-level and K-target decisions used by
`run`. This is an operational refinement only: erasing the added fields leaves the existing
normalization candidate and checker equations unchanged. -/
structure NormalizationEliminationExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) where
  normalization : NormalizationCandidateExecution nparams types numNested
    isUnsafe candidateContext
  constructorEnv : Environment
  declareConstructorsRun :
    declareConstructors normalization.stats types.toArray isUnsafe
      { normalization.validationContext with
        env := normalization.familyEnv } = .ok constructorEnv
  elimination : ElimLevelExecution normalization.stats types.toArray
    { normalization.validationContext with env := constructorEnv }
  kTarget : KTargetExecution normalization.stats types.toArray
    { normalization.validationContext with env := constructorEnv }

namespace NormalizationEliminationExecution

def candidate
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : NormalizationCandidate types :=
  execution.normalization.candidate

/-- Execute the existing detailed candidate producer, declare the already
validated constructors, and retain both recursor decisions at precisely the
post-constructor context used by `run`. -/
def buildExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) :
    Except Exception (NormalizationEliminationExecution nparams types
      numNested isUnsafe candidateContext) := do
  let normalization ← buildNormalizationCandidateExecution nparams types
    numNested isUnsafe candidateContext
  let constructorContext : Context :=
    { normalization.validationContext with env := normalization.familyEnv }
  match hdeclare : declareConstructors normalization.stats types.toArray
      isUnsafe constructorContext with
  | .error error => .error error
  | .ok constructorEnv =>
      let eliminationContext : Context :=
        { normalization.validationContext with env := constructorEnv }
      match ElimLevelExecution.buildExecution normalization.stats
          types.toArray eliminationContext with
      | .error error => .error error
      | .ok elimination =>
          match KTargetExecution.buildExecution normalization.stats
              types.toArray eliminationContext with
          | .error error => .error error
          | .ok kTarget => .ok {
              normalization
              constructorEnv
              declareConstructorsRun := by
                simpa [constructorContext] using hdeclare
              elimination := by simpa [eliminationContext] using elimination
              kTarget := by simpa [eliminationContext] using kTarget }

/-- The level list supplied to generated recursive calls. -/
def recLevels
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : List Level :=
  getRecLevels execution.elimination.level execution.normalization.stats.levels

/-- The level-parameter list stored in generated recursor metadata. -/
def recLevelParams
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : List Name :=
  getRecLevelParams execution.elimination.level
    execution.normalization.validationContext.lparams

end NormalizationEliminationExecution

#guard_named_axioms Ix.Theory.Named.AddInductive.KTargetCtorTrace.run [propext]

#guard_named_axioms Ix.Theory.Named.AddInductive.KTargetExecution.buildExecution [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.LargeEliminatorLoopTrace.run [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.LargeEliminatorExecution.buildExecution [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ElimLevelExecution.run_of_large [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ElimLevelExecution.recLevelParams_eq_large [propext, Classical.choice, Quot.sound]

end AddInductive
end Ix.Theory.Named
