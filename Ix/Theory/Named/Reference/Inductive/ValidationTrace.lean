/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Reference.Inductive.Add

set_option linter.unusedSimpArgs false

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

namespace AddInductive
open TypeChecker

/-- The constructor root check runs with no validation-local declarations,
while retaining every other field of the post-family checker context. -/
def Context.withEmptyLocalContext (context : Context) : Context :=
  { context with lctx := {} }

/-- One exact successful `ensureType` execution used for an ordinary
constructor field. -/
structure ConstructorEnsureTypeStep where
  context : Context
  source : Expr
  result : Expr

def ConstructorEnsureTypeStep.Valid
    (step : ConstructorEnsureTypeStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.ensureType step.source) =
    .ok step.result

/-- The two successful universe branches of `checkConstructors`: either the
transparent structural comparison succeeds, or the exact fallback comparison
does. Keeping the branch choice prevents a trace from silently replacing the
executable universe test with a stronger premise. -/
inductive ConstructorUniverseTrace (resultLevel fieldLevel : Level) : Type where
  | structural
      (valid : levelStructGe resultLevel fieldLevel = true) :
      ConstructorUniverseTrace resultLevel fieldLevel
  | fallback
      (structuralFailed : levelStructGe resultLevel fieldLevel = false)
      (valid : (resultLevel.isAlwaysZero || resultLevel.geq fieldLevel) = true) :
      ConstructorUniverseTrace resultLevel fieldLevel

namespace ConstructorUniverseTrace

/-- A field rejected by both executable universe comparisons cannot have a
successful universe trace. -/
theorem not_nonempty_of_rejected
    (structuralRejected : levelStructGe resultLevel fieldLevel = false)
    (fallbackRejected :
      (resultLevel.isAlwaysZero || resultLevel.geq fieldLevel) = false) :
    ¬ Nonempty (ConstructorUniverseTrace resultLevel fieldLevel) := by
  rintro ⟨trace⟩
  cases trace with
  | structural valid => simp_all
  | fallback _ valid => simp_all

end ConstructorUniverseTrace

/-- Complete successful traversal of `checkPositivity.loop`, indexed by the
exact source expression, checker context, and remaining fuel. The recursive
constructor records the precise local declaration used by the executable
traversal; the terminal constructor records the accepted recursive target. -/
inductive ConstructorPositivityTrace
    (stats : InductiveStats) (ctor : Name) (argIdx : Nat) :
    (context : Context) → (source : Expr) → (fuel : Nat) → Type where
  | absent
      (context : Context) (source result : Expr) (fuel : Nat)
      (whnf : CandidateWhnfStep.Valid ⟨context, source, result⟩)
      (occurs : hasIndOcc stats.indConsts result = false) :
      ConstructorPositivityTrace stats ctor argIdx context source (fuel + 1)
  | forallE
      (context : Context) (source : Expr) (fuel : Nat)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (whnf : CandidateWhnfStep.Valid
        ⟨context, source, .forallE name domain body binderInfo⟩)
      (occurs : hasIndOcc stats.indConsts
        (.forallE name domain body binderInfo) = true)
      (domainFree : hasIndOcc stats.indConsts domain = false)
      (tail : ConstructorPositivityTrace stats ctor argIdx
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel) :
      ConstructorPositivityTrace stats ctor argIdx context source (fuel + 1)
  | target
      (context : Context) (source result : Expr) (fuel targetIdx : Nat)
      (whnf : CandidateWhnfStep.Valid ⟨context, source, result⟩)
      (occurs : hasIndOcc stats.indConsts result = true)
      (terminal : result.isForall = false)
      (valid : isValidIndApp? stats result = some targetIdx) :
      ConstructorPositivityTrace stats ctor argIdx context source (fuel + 1)

namespace ConstructorPositivityTrace

/-- Observable recursive-target data retained by the positivity traversal.
`binderDepth` counts positive Pi domains traversed before the terminal family
application. -/
structure Target where
  familyIdx : Nat
  binderDepth : Nat
  deriving DecidableEq, Repr

/-- Erase proof fields while retaining the exact sibling-family ordinal and
positive-Pi depth selected by the executable positivity run. -/
def target? :
    ConstructorPositivityTrace stats ctor argIdx context source fuel →
      Option Target
  | .absent _ _ _ _ _ _ => none
  | .forallE _ _ _ _ _ _ _ _ _ _ tail =>
      tail.target?.map fun target =>
        { target with binderDepth := target.binderDepth + 1 }
  | .target _ _ _ _ familyIdx _ _ _ _ =>
      some { familyIdx, binderDepth := 0 }

/-- Erasing a positivity trace replays the exact executable traversal. -/
theorem run
    (trace : ConstructorPositivityTrace stats ctor argIdx context source fuel) :
    checkPositivity.loop stats ctor argIdx source fuel context = .ok () := by
  induction trace with
  | absent context source result fuel whnf occurs =>
      unfold checkPositivity.loop
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind]
      rw [occurs]
      rfl
  | forallE context source fuel name domain body binderInfo whnf occurs
      domainFree tail ih =>
      unfold checkPositivity.loop
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind]
      rw [occurs]
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
        ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
        Except.bind, Except.pure]
      rw [domainFree]
      simp only [Bool.false_eq_true, if_false, withLocalDecl_apply]
      exact ih
  | target context source result fuel targetIdx whnf occurs terminal valid =>
      unfold checkPositivity.loop
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind]
      rw [occurs]
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
        ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
        Except.bind, Except.pure]
      cases result <;>
        simp_all [Expr.isForall, ReaderT.pure, Pure.pure, Except.pure]

/-- Every successful executable positivity traversal decomposes into the
source-indexed trace above. -/
theorem exists_of_run
    (success : checkPositivity.loop stats ctor argIdx source fuel context =
      .ok ()) :
    Nonempty (ConstructorPositivityTrace stats ctor argIdx
      context source fuel) := by
  induction fuel generalizing context source with
  | zero =>
      rw [checkPositivity.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [checkPositivity.loop.eq_2] at success
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
      cases hwhnf : TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf source) with
      | error err => simp_all [Except.bind]
      | ok result =>
          rw [hwhnf] at success
          simp only [Except.bind] at success
          cases hocc : hasIndOcc stats.indConsts result with
          | false => exact ⟨.absent context source result fuel hwhnf hocc⟩
          | true =>
            rw [hocc] at success
            simp only [Bool.not_true, Bool.false_eq_true, if_false,
              ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
              Except.bind, Except.pure] at success
            cases result
            case forallE name domain body binderInfo =>
                simp only at success
                cases hdomain : hasIndOcc stats.indConsts domain with
                | false =>
                  rw [hdomain] at success
                  simp only [Bool.false_eq_true, if_false,
                    withLocalDecl_apply] at success
                  obtain ⟨tail⟩ := ih success
                  exact ⟨.forallE context source fuel name domain body
                    binderInfo hwhnf hocc hdomain tail⟩
                | true =>
                  rw [hdomain] at success
                  change Except.error _ = Except.ok () at success
                  contradiction
            all_goals
              simp only at success
              cases hvalid : isValidIndApp? stats _ with
              | none =>
                  rw [hvalid] at success
                  change Except.error _ = Except.ok () at success
                  contradiction
              | some targetIdx =>
                  exact ⟨.target context source _ fuel targetIdx
                    hwhnf hocc rfl hvalid⟩

/-- Execute the positivity traversal while retaining its exact dependent
trace as data. Unlike `exists_of_run`, this decomposition is transparent and
therefore remains available to later executable alignment audits; erasing the
result with `run` recovers the ordinary checker execution. -/
def buildExecution (stats : InductiveStats) (ctor : Name) (argIdx : Nat)
    (context : Context) (source : Expr) :
    (fuel : Nat) → Except Exception
      (ConstructorPositivityTrace stats ctor argIdx context source fuel)
  | 0 => .error .deepRecursion
  | fuel + 1 =>
      match hwhnf : TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf source) with
      | .error error => .error error
      | .ok result =>
          match hoccurs : hasIndOcc stats.indConsts result with
          | false => .ok (.absent context source result fuel hwhnf hoccurs)
          | true =>
              match hforall : result.isForall with
              | true =>
                  match result with
                  | .forallE name domain body binderInfo =>
                      match hdomain : hasIndOcc stats.indConsts domain with
                      | true => .error <| .other
                          s!"arg #{argIdx + 1} of '{ctor}' has a non positive occurrence of the datatypes being declared"
                      | false =>
                          match buildExecution stats ctor argIdx
                              (context.pushLocalDecl name binderInfo
                                (consumeTypeAnnotations domain))
                              (body.instantiate1 context.freshExpr) fuel with
                          | .error error => .error error
                          | .ok tail => .ok (.forallE context source fuel name
                              domain body binderInfo hwhnf hoccurs hdomain tail)
                  | _ => .error <| .other
                      "positivity WHNF shape disagrees with isForall"
              | false =>
                  match hvalid : isValidIndApp? stats result with
                  | none => .error <| .other
                      s!"arg #{argIdx + 1} of '{ctor}' has a non valid occurrence of the datatypes being declared"
                  | some targetIdx => .ok (.target context source result fuel
                      targetIdx hwhnf hoccurs hforall hvalid)

/-- The transparent decomposition succeeds on every input accepted by the
executable positivity traversal, so retained-trace construction needs no
choice principle. -/
theorem buildExecution_ok_of_run
    (success : checkPositivity.loop stats ctor argIdx source fuel context =
      .ok ()) :
    ∃ trace, buildExecution stats ctor argIdx context source fuel =
      .ok trace := by
  induction fuel generalizing context source with
  | zero =>
      rw [checkPositivity.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [checkPositivity.loop.eq_2] at success
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
      unfold buildExecution
      split
      next error heq =>
        rw [heq] at success
        simp [Except.bind] at success
      next result heq =>
        rw [heq] at success
        simp only [Except.bind] at success
        split
        next hoccurs => exact ⟨_, rfl⟩
        next hoccurs =>
          rw [hoccurs] at success
          simp only [Bool.not_true, Bool.false_eq_true, if_false,
            ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
            Except.bind, Except.pure] at success
          cases result <;> simp only [Expr.isForall] <;> simp only at success
          case forallE name domain body binderInfo =>
            split
            next hdomain =>
              rw [hdomain] at success
              change Except.error _ = Except.ok () at success
              contradiction
            next hdomain =>
              rw [hdomain] at success
              have tailSuccess :
                  checkPositivity.loop stats ctor argIdx
                    (body.instantiate1 context.freshExpr) fuel
                    (context.pushLocalDecl name binderInfo
                      (consumeTypeAnnotations domain)) = .ok () := success
              obtain ⟨tail, htail⟩ := ih tailSuccess
              rw [htail]
              exact ⟨_, rfl⟩
          all_goals
            split
            next hvalid =>
              rw [hvalid] at success
              change Except.error _ = Except.ok () at success
              contradiction
            next targetIdx hvalid => exact ⟨_, rfl⟩

/-- An exact positivity failure, including its diagnostic payload, excludes a
successful trace at precisely that source/context/fuel position. -/
theorem not_nonempty_of_error
    (failure : checkPositivity.loop stats ctor argIdx source fuel context =
      .error err) :
    ¬ Nonempty (ConstructorPositivityTrace stats ctor argIdx
      context source fuel) := by
  rintro ⟨trace⟩
  have success := trace.run
  rw [failure] at success
  contradiction

end ConstructorPositivityTrace

/-- Whether positivity was executed or skipped by the exact `isUnsafe`
branch of constructor validation. -/
inductive ConstructorPositivityModeTrace
    (stats : InductiveStats) (isUnsafe : Bool)
    (ctor : Name) (argIdx : Nat) (context : Context) (source : Expr) : Type where
  | skipped
      (isUnsafe_eq : isUnsafe = true) :
      ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source
  | safe
      (isUnsafe_eq : isUnsafe = false)
      (trace : ConstructorPositivityTrace stats ctor argIdx context source
        context.fuel.inductiveFuel) :
      ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source

namespace ConstructorPositivityModeTrace

/-- Observable recursive target for the exact safe/unsafe positivity branch.
Unsafe validation deliberately exposes no positivity claim. -/
def target? :
    ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source →
      Option ConstructorPositivityTrace.Target
  | .skipped _ => none
  | .safe _ trace => trace.target?

theorem run
    (trace : ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source) :
    (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .ok () := by
  cases trace with
  | skipped h => simp [h, ReaderT.pure, Pure.pure, Except.pure]
  | safe h trace =>
      simp only [h, Bool.not_false, if_true]
      unfold checkPositivity
      simpa only [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure] using trace.run

/-- Execute the recorded positivity branch and then an exact continuation. -/
theorem bind_run
    (trace : ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source)
    (next : M α) (result : α)
    (nextRun : next context = .ok result) :
    (do
      if !isUnsafe then checkPositivity stats source ctor argIdx
      next) context = .ok result := by
  cases trace with
  | skipped h =>
      simp [h, nextRun, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.bind, Except.pure]
  | safe h trace =>
      have positivityRun :
          checkPositivity stats source ctor argIdx context = .ok () := by
        unfold checkPositivity
        simpa only [readThe, MonadReaderOf.read, ReaderT.read,
          ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
          Except.bind, Except.pure] using trace.run
      simp [h, positivityRun, nextRun, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.bind, Except.pure]

/-- A successful executable positivity branch determines whether validation
was skipped for an unsafe declaration or supplies the full safe trace. -/
theorem exists_of_run
    (success :
      (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .ok ()) :
    Nonempty (ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source) := by
  cases hUnsafe : isUnsafe with
  | false =>
      simp only [hUnsafe, Bool.not_false, if_true] at success
      unfold checkPositivity at success
      simp only [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure] at success
      obtain ⟨trace⟩ := ConstructorPositivityTrace.exists_of_run success
      exact ⟨.safe rfl trace⟩
  | true => exact ⟨.skipped rfl⟩

/-- Transparently retain the exact safe/unsafe positivity branch selected by
constructor validation. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (ctor : Name) (argIdx : Nat) (context : Context) (source : Expr) :
    Except Exception
      (ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source) :=
  match isUnsafe with
  | true => .ok (.skipped rfl)
  | false =>
      match ConstructorPositivityTrace.buildExecution stats ctor argIdx
          context source context.fuel.inductiveFuel with
      | .error error => .error error
      | .ok trace => .ok (.safe rfl trace)

/-- The retained safe/unsafe branch decomposition succeeds whenever the
executable positivity branch does. -/
theorem buildExecution_ok_of_run
    (success :
      (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .ok ()) :
    ∃ trace, buildExecution stats isUnsafe ctor argIdx context source =
      .ok trace := by
  cases isUnsafe with
  | true => exact ⟨_, rfl⟩
  | false =>
      simp only [Bool.not_false, if_true] at success
      unfold checkPositivity at success
      simp only [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure] at success
      obtain ⟨trace, htrace⟩ :=
        ConstructorPositivityTrace.buildExecution_ok_of_run success
      unfold buildExecution
      rw [htrace]
      exact ⟨_, rfl⟩

/-- Failure of the exact safe/unsafe positivity branch excludes its retained
mode trace without changing the executable diagnostic. -/
theorem not_nonempty_of_error
    (failure :
      (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .error err) :
    ¬ Nonempty (ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source) := by
  rintro ⟨trace⟩
  have success := trace.run
  rw [failure] at success
  contradiction

end ConstructorPositivityModeTrace

/-- Exact successful validation of one constructor type from its root through
its parameter prefix, ordinary fields, positivity checks, and terminal family
application. Every recursive index is selected by the executable traversal. -/
inductive ConstructorTypeValidationTrace
    (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (ctor : Name) :
    (context : Context) → (source : Expr) →
      (argIdx fuel : Nat) → Type where
  | parameter
      (context : Context) (fuel argIdx : Nat)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (param parameterType : Expr)
      (parameterAt : stats.params[argIdx]? = some param)
      (parameterTypeRun : getType param context = .ok parameterType)
      (defeq : CandidateIsDefEqStep.Valid
        ⟨context, domain, parameterType⟩)
      (tail : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (body.instantiate1 param) (argIdx + 1) fuel) :
      ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (.forallE name domain body binderInfo) argIdx (fuel + 1)
  | ordinary
      (context : Context) (fuel argIdx : Nat)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (sortResult : Expr)
      (noParameter : stats.params[argIdx]? = none)
      (ensureType : ConstructorEnsureTypeStep.Valid
        ⟨context, domain, sortResult⟩)
      (universeTrace : ConstructorUniverseTrace
        stats.resultLevel sortResult.sortLevel!)
      (positivity : ConstructorPositivityModeTrace
        stats isUnsafe ctor argIdx context domain)
      (tail : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) fuel) :
      ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (.forallE name domain body binderInfo) argIdx (fuel + 1)
  | terminal
      (context : Context) (source : Expr) (fuel argIdx : Nat)
      (terminal : source.isForall = false)
      (valid : isValidIndAppIdx stats source familyIdx = true) :
      ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context source argIdx (fuel + 1)

namespace ConstructorTypeValidationTrace

/-- Field-ordered recursive-target observations for one constructor. Parameter
binders are omitted; every ordinary constructor field contributes one slot. -/
def targets :
    ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel →
      List (Option ConstructorPositivityTrace.Target)
  | .parameter _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.targets
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ positivity tail =>
      positivity.target? :: tail.targets
  | .terminal _ _ _ _ _ _ => []

/-- Erasing one constructor-type trace replays the exact inner
`checkConstructorType.loop` execution. -/
theorem run
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) :
    checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .ok () := by
  induction trace with
  | parameter context fuel argIdx name domain body binderInfo param
      parameterType parameterAt parameterTypeRun defeq tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [checkConstructorType.loop.eq_2]
      rw [parameterAt]
      simp only [ReaderT.bind, Bind.bind]
      rw [parameterTypeRun]
      simp only [Except.bind, liftTypeChecker_apply]
      rw [defeq]
      simp only [if_true, ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
        Except.bind, Except.pure]
      exact ih
  | ordinary context fuel argIdx name domain body binderInfo sortResult noParameter
      ensureType universeTrace positivity tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [checkConstructorType.loop.eq_2]
      rw [noParameter]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [ensureType]
      simp only [Except.bind]
      let next : M PUnit :=
        withLocalDecl name binderInfo (consumeTypeAnnotations domain) fun arg =>
          checkConstructorType.loop stats isUnsafe familyIdx ctor
            (body.instantiate1 arg) (argIdx + 1) fuel
      have nextRun : next context = .ok () := by
        simp only [next, withLocalDecl_apply]
        exact ih
      have restRun :
          (do
            if !isUnsafe then checkPositivity stats domain ctor argIdx
            next) context = .ok () :=
        positivity.bind_run next () nextRun
      cases universeTrace with
      | structural valid =>
          rw [valid]
          simp only [if_true, ReaderT.pure, Pure.pure,
            ReaderT.bind, Bind.bind, Except.bind, Except.pure]
          exact restRun
      | fallback structuralFailed valid =>
          rw [structuralFailed, valid]
          simp only [Bool.true_eq_false, Bool.not_true, if_false,
            Bool.false_eq_true,
            ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
            Except.bind, Except.pure]
          exact restRun
  | terminal context source fuel argIdx terminal valid =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      cases source <;>
        simp_all [checkConstructorType.loop, Expr.isForall,
          ReaderT.pure, Pure.pure, Except.pure]

/-- Every successful one-constructor telescope traversal decomposes into the
exact parameter, field, universe, positivity, and terminal trace. -/
theorem exists_of_run
    (success :
      checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .ok ()) :
    Nonempty (ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) := by
  induction fuel generalizing context source argIdx with
  | zero =>
      rw [checkConstructorType.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega] at success
      cases source
      case forallE name domain body binderInfo =>
        rw [checkConstructorType.loop.eq_2] at success
        simp only at success
        cases hparam : stats.params[argIdx]? with
        | some param =>
            rw [hparam] at success
            simp only [ReaderT.bind, Bind.bind] at success
            cases hget : getType param context with
            | error err => simp_all [Except.bind]
            | ok parameterType =>
                rw [hget] at success
                simp only [Except.bind, liftTypeChecker_apply] at success
                cases hdefeq : TypeChecker.M.run context.env context.safety
                    context.lctx context.lparams context.fuel
                    (TypeChecker.isDefEq domain parameterType) with
                | error err => simp_all [Except.bind]
                | ok equal =>
                    rw [hdefeq] at success
                    simp only [Except.bind] at success
                    cases equal with
                    | false =>
                        change Except.error _ = Except.ok () at success
                        contradiction
                    | true =>
                        simp only [if_true, ReaderT.pure, Pure.pure,
                          ReaderT.bind, Bind.bind, Except.bind,
                          Except.pure] at success
                        obtain ⟨tail⟩ := ih success
                        exact ⟨.parameter context fuel argIdx name domain body
                          binderInfo param parameterType hparam hget hdefeq tail⟩
        | none =>
            rw [hparam] at success
            simp only [ReaderT.bind, Bind.bind,
              liftTypeChecker_apply] at success
            cases hensure : TypeChecker.M.run context.env context.safety
                context.lctx context.lparams context.fuel
                (TypeChecker.ensureType domain) with
            | error err => simp_all [Except.bind]
            | ok sortResult =>
                rw [hensure] at success
                simp only [Except.bind] at success
                have finish
                    (universeTrace : ConstructorUniverseTrace
                      stats.resultLevel sortResult.sortLevel!)
                    (restSuccess :
                      (do
                        if !isUnsafe then
                          checkPositivity stats domain ctor argIdx
                        withLocalDecl name binderInfo
                            (consumeTypeAnnotations domain) fun arg =>
                          checkConstructorType.loop stats isUnsafe familyIdx ctor
                            (body.instantiate1 arg) (argIdx + 1) fuel)
                        context = .ok ()) :
                    Nonempty (ConstructorTypeValidationTrace stats isUnsafe
                      familyIdx ctor context
                      (.forallE name domain body binderInfo) argIdx (fuel + 1)) := by
                  cases isUnsafe with
                  | false =>
                      simp only [Bool.not_false, if_true,
                        ReaderT.bind, Bind.bind] at restSuccess
                      cases hpos : checkPositivity stats domain ctor argIdx context with
                      | error err => simp_all [Except.bind]
                      | ok typeUnit =>
                          cases typeUnit
                          rw [hpos] at restSuccess
                          simp only [Except.bind, withLocalDecl_apply] at restSuccess
                          have hposLoop :
                              checkPositivity.loop stats ctor argIdx domain
                                  context.fuel.inductiveFuel context = .ok () := by
                            unfold checkPositivity at hpos
                            simpa only [readThe, MonadReaderOf.read, ReaderT.read,
                              ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
                              Except.bind, Except.pure] using hpos
                          obtain ⟨positivityTrace⟩ :=
                            ConstructorPositivityTrace.exists_of_run hposLoop
                          obtain ⟨tail⟩ := ih restSuccess
                          exact ⟨.ordinary context fuel argIdx name domain body
                            binderInfo sortResult hparam hensure universeTrace
                            (.safe rfl positivityTrace) tail⟩
                  | true =>
                      simp only [Bool.not_true, if_false,
                        ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                        Except.bind, Except.pure,
                        withLocalDecl_apply] at restSuccess
                      obtain ⟨tail⟩ := ih restSuccess
                      exact ⟨.ordinary context fuel argIdx name domain body
                        binderInfo sortResult hparam hensure universeTrace
                        (.skipped rfl) tail⟩
                cases hstruct : levelStructGe stats.resultLevel
                    sortResult.sortLevel! with
                | true =>
                    rw [hstruct] at success
                    simp only [if_true, ReaderT.pure, Pure.pure,
                      ReaderT.bind, Bind.bind, Except.bind,
                      Except.pure] at success
                    exact finish (.structural hstruct) success
                | false =>
                    rw [hstruct] at success
                    simp only [Bool.false_eq_true, if_false] at success
                    cases hfallback :
                        (stats.resultLevel.isAlwaysZero ||
                          stats.resultLevel.geq sortResult.sortLevel!) with
                    | false =>
                        rw [hfallback] at success
                        change Except.error _ = Except.ok () at success
                        contradiction
                    | true =>
                        rw [hfallback] at success
                        simp only [Bool.true_eq_false, Bool.not_true, if_false,
                          ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                          Except.bind, Except.pure] at success
                        exact finish (.fallback hstruct hfallback) success
      all_goals
        unfold checkConstructorType.loop at success
        simp only at success
        cases hvalid : isValidIndAppIdx stats _ familyIdx with
        | false =>
            rw [hvalid] at success
            change Except.error _ = Except.ok () at success
            contradiction
        | true =>
            exact ⟨.terminal context _ fuel argIdx rfl hvalid⟩

/-- Execute one constructor telescope while retaining the exact parameter,
universe, positivity, and terminal choices made by the ordinary validator.
The returned data is transparent, so later executable gates can inspect the
same trace without selecting it through `Classical.choice`. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (ctor : Name) (context : Context) (source : Expr)
    (argIdx : Nat) :
    (fuel : Nat) → Except Exception
      (ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context source argIdx fuel)
  | 0 => .error .deepRecursion
  | fuel + 1 =>
      match hforall : source.isForall with
      | false =>
          match hvalid : isValidIndAppIdx stats source familyIdx with
          | false => .error <| .other s!"invalid return type for '{ctor}'"
          | true => .ok (.terminal context source fuel argIdx hforall hvalid)
      | true =>
          match source with
          | .forallE name domain body binderInfo =>
              match hparam : stats.params[argIdx]? with
              | some param =>
                  match hget : getType param context with
                  | .error error => .error error
                  | .ok parameterType =>
                      match hdefeq : TypeChecker.M.run context.env
                          context.safety context.lctx context.lparams
                          context.fuel
                          (TypeChecker.isDefEq domain parameterType) with
                      | .error error => .error error
                      | .ok false => .error <| .other
                          s!"arg #{argIdx + 1} of '{ctor}' does not match inductive datatype parameters"
                      | .ok true =>
                          match buildExecution stats isUnsafe familyIdx ctor
                              context (body.instantiate1 param) (argIdx + 1)
                              fuel with
                          | .error error => .error error
                          | .ok tail => .ok (.parameter context fuel argIdx
                              name domain body binderInfo param parameterType
                              hparam hget hdefeq tail)
              | none =>
                  match hensure : TypeChecker.M.run context.env context.safety
                      context.lctx context.lparams context.fuel
                      (TypeChecker.ensureType domain) with
                  | .error error => .error error
                  | .ok sortResult =>
                      let finish (universeTrace : ConstructorUniverseTrace
                          stats.resultLevel sortResult.sortLevel!) :=
                        match ConstructorPositivityModeTrace.buildExecution
                            stats isUnsafe ctor argIdx context domain with
                        | .error error => .error error
                        | .ok positivity =>
                            match buildExecution stats isUnsafe familyIdx ctor
                                (context.pushLocalDecl name binderInfo
                                  (consumeTypeAnnotations domain))
                                (body.instantiate1 context.freshExpr)
                                (argIdx + 1) fuel with
                            | .error error => .error error
                            | .ok tail => .ok (.ordinary context fuel argIdx
                                name domain body binderInfo sortResult hparam
                                hensure universeTrace positivity tail)
                      match hstruct : levelStructGe stats.resultLevel
                          sortResult.sortLevel! with
                      | true => finish (.structural hstruct)
                      | false =>
                          match hfallback : stats.resultLevel.isAlwaysZero ||
                              stats.resultLevel.geq sortResult.sortLevel! with
                          | false => .error <| .other
                              s!"universe level of type_of(arg #{argIdx + 1}) of '{ctor}' is too big for the corresponding inductive datatype"
                          | true => finish (.fallback hstruct hfallback)
          | _ => .error <| .other
              "constructor source shape disagrees with isForall"

/-- The transparent telescope decomposition succeeds on every constructor
type accepted by the inner executable validator. -/
theorem buildExecution_ok_of_run
    (success :
      checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .ok ()) :
    ∃ trace, buildExecution stats isUnsafe familyIdx ctor context source
      argIdx fuel = .ok trace := by
  induction fuel generalizing context source argIdx with
  | zero =>
      rw [checkConstructorType.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega] at success
      cases source
      case forallE name domain body binderInfo =>
        rw [checkConstructorType.loop.eq_2] at success
        simp only at success
        unfold buildExecution
        simp only [Expr.isForall]
        split
        next param hparam =>
          rw [hparam] at success
          simp only [ReaderT.bind, Bind.bind] at success
          split
          next error heq =>
            rw [heq] at success
            simp [Except.bind] at success
          next parameterType heq =>
            rw [heq] at success
            simp only [Except.bind, liftTypeChecker_apply] at success
            split
            next error heq2 =>
              rw [heq2] at success
              simp [Except.bind] at success
            next heq2 =>
              rw [heq2] at success
              simp only [Except.bind] at success
              change Except.error _ = Except.ok () at success
              contradiction
            next heq2 =>
              rw [heq2] at success
              simp only [Except.bind, if_true, ReaderT.pure, Pure.pure,
                ReaderT.bind, Bind.bind, Except.pure] at success
              obtain ⟨tail, htail⟩ := ih success
              rw [htail]
              exact ⟨_, rfl⟩
        next hparam =>
          rw [hparam] at success
          simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
          split
          next error heq =>
            rw [heq] at success
            simp [Except.bind] at success
          next sortResult heq =>
            rw [heq] at success
            simp only [Except.bind] at success
            have finish :
                (do
                  if !isUnsafe then checkPositivity stats domain ctor argIdx
                  withLocalDecl name binderInfo (consumeTypeAnnotations domain)
                      fun arg =>
                    checkConstructorType.loop stats isUnsafe familyIdx ctor
                      (body.instantiate1 arg) (argIdx + 1) fuel)
                    context = .ok () →
                (∃ positivity,
                  ConstructorPositivityModeTrace.buildExecution stats isUnsafe
                    ctor argIdx context domain = .ok positivity) ∧
                ∃ tail,
                  buildExecution stats isUnsafe familyIdx ctor
                    (context.pushLocalDecl name binderInfo
                      (consumeTypeAnnotations domain))
                    (body.instantiate1 context.freshExpr) (argIdx + 1) fuel =
                    .ok tail := by
              intro restSuccess
              cases isUnsafe with
              | false =>
                  simp only [Bool.not_false, if_true,
                    ReaderT.bind, Bind.bind] at restSuccess
                  cases hpos : checkPositivity stats domain ctor argIdx
                      context with
                  | error err => simp_all [Except.bind]
                  | ok posUnit =>
                      cases posUnit
                      rw [hpos] at restSuccess
                      simp only [Except.bind,
                        withLocalDecl_apply] at restSuccess
                      have hpmSuccess :
                          (if !false then
                            checkPositivity stats domain ctor argIdx
                          else pure ()) context = .ok () := by
                        simpa using hpos
                      exact ⟨ConstructorPositivityModeTrace.buildExecution_ok_of_run
                        hpmSuccess, ih restSuccess⟩
              | true =>
                  simp only [Bool.not_true, if_false,
                    ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                    Except.bind, Except.pure,
                    withLocalDecl_apply] at restSuccess
                  have hpmSuccess :
                      (if !true then
                        checkPositivity stats domain ctor argIdx
                      else pure ()) context = .ok () := by
                    simp [ReaderT.pure, Pure.pure, Except.pure]
                  exact ⟨ConstructorPositivityModeTrace.buildExecution_ok_of_run
                    hpmSuccess, ih restSuccess⟩
            split
            next hstruct =>
              rw [hstruct] at success
              simp only [if_true, ReaderT.pure, Pure.pure,
                ReaderT.bind, Bind.bind, Except.bind, Except.pure] at success
              obtain ⟨⟨positivity, hpm⟩, tail, htail⟩ := finish success
              rw [hpm, htail]
              exact ⟨_, rfl⟩
            next hstruct =>
              rw [hstruct] at success
              simp only [Bool.false_eq_true, if_false] at success
              split
              next hfallback =>
                rw [hfallback] at success
                change Except.error _ = Except.ok () at success
                contradiction
              next hfallback =>
                rw [hfallback] at success
                simp only [Bool.true_eq_false, Bool.not_true, if_false,
                  ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                  Except.bind, Except.pure] at success
                obtain ⟨⟨positivity, hpm⟩, tail, htail⟩ := finish success
                rw [hpm, htail]
                exact ⟨_, rfl⟩
      all_goals
        unfold checkConstructorType.loop at success
        simp only at success
        unfold buildExecution
        simp only [Expr.isForall]
        split
        next hvalid =>
          rw [hvalid] at success
          change Except.error _ = Except.ok () at success
          contradiction
        next hvalid => exact ⟨_, rfl⟩

/-- Erasing the inner trace also replays the public one-constructor checker,
including its exact context-fuel read. -/
theorem check_run
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source 0 context.fuel.inductiveFuel) :
    checkConstructorType stats isUnsafe familyIdx ctor source context = .ok () := by
  unfold checkConstructorType
  simpa only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure] using trace.run

/-- Any exact inner constructor-telescope failure excludes a trace at that
same parameter/field/terminal position and retains the original error value. -/
theorem not_nonempty_of_error
    (failure :
      checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .error err) :
    ¬ Nonempty (ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) := by
  rintro ⟨trace⟩
  have success := trace.run
  rw [failure] at success
  contradiction

end ConstructorTypeValidationTrace

/-- Source-ordered validation of a constructor list. The `seen` index makes
duplicate-name checks part of the trace and prevents reordering or omission.
Root closedness and full type checking are retained before the recursive type
trace, exactly as in `checkConstructors`. -/
inductive ConstructorListValidationTrace
    (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (context : Context) :
    NameSet → List Constructor → Type where
  | nil (seen : NameSet) :
      ConstructorListValidationTrace stats isUnsafe familyIdx context seen []
  | cons
      (seen : NameSet) (head : Constructor) (tail : List Constructor)
      (fresh : seen.contains head.name = false)
      (closed : context.env.checkNoMVarNoFVar head.name head.type = .ok ())
      (rootCheck : CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type)
      (typeTrace : ConstructorTypeValidationTrace
        stats isUnsafe familyIdx head.name context head.type 0
        context.fuel.inductiveFuel)
      (tailTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail) :
      ConstructorListValidationTrace stats isUnsafe familyIdx context
        seen (head :: tail)

namespace ConstructorListValidationTrace

/-- Constructor-ordered positivity observations for one family. -/
def targets :
    ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors →
      List (List (Option ConstructorPositivityTrace.Target))
  | .nil _ => []
  | .cons _ _ _ _ _ _ typeTrace tailTrace =>
      typeTrace.targets :: tailTrace.targets

/-- Execute the source-ordered constructor fold while retaining its exact
dependent validation trace.  Every stored equation is obtained from the same
checker call made by `checkConstructorFold`; no semantic premise participates
in acceptance. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (context : Context) :
    (seen : NameSet) → (constructors : List Constructor) →
      Except Exception
        (ConstructorListValidationTrace stats isUnsafe familyIdx context
          seen constructors)
  | seen, [] => .ok (.nil seen)
  | seen, head :: tail =>
      match hfresh : seen.contains head.name with
      | true => .error <| .other s!"duplicate constructor name '{head.name}'"
      | false =>
          match hclosed : context.env.checkNoMVarNoFVar
              head.name head.type with
          | .error error => .error error
          | .ok () =>
              match hroot : TypeChecker.M.run context.env context.safety {}
                  context.lparams context.fuel
                  (TypeChecker.checkType head.type) with
              | .error error => .error error
              | .ok inferred =>
                  let rootCheck : CandidateCheckTypeObservation
                      context.withEmptyLocalContext head.type :=
                    ⟨inferred, by
                      simpa only [CandidateCheckTypeStep.Valid,
                        Context.withEmptyLocalContext] using hroot⟩
                  match ConstructorTypeValidationTrace.buildExecution stats
                      isUnsafe familyIdx head.name context head.type 0
                      context.fuel.inductiveFuel with
                  | .error error => .error error
                  | .ok typeTrace =>
                      match buildExecution stats isUnsafe familyIdx context
                          (seen.insert head.name) tail with
                      | .error error => .error error
                      | .ok tailTrace => .ok (.cons seen head tail hfresh
                          hclosed rootCheck typeTrace tailTrace)

end ConstructorListValidationTrace

/-- A transparent presentation of the constructor portion of the executable
validator, discarding only the final duplicate-name accumulator. -/
def checkConstructorList
    (stats : InductiveStats) (isUnsafe : Bool) (familyIdx : Nat)
    (context : Context) (seen : NameSet) (ctors : List Constructor) :
    Except Exception Unit := do
  _ ← checkConstructorFold context.env stats isUnsafe familyIdx seen ctors context
  pure ()

/-- For one family, the named list recursion is exactly the array/list shell
of the real constructor validator. -/
theorem checkConstructors_singleton_eq_checkConstructorList
    (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) :
    checkConstructors #[indType] stats isUnsafe context =
      checkConstructorList stats isUnsafe 0 context {} indType.ctors := by
  unfold checkConstructors
  simp only [ReaderT.bind, Bind.bind]
  rw [liftTypeChecker_apply]
  have hget :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel TypeChecker.getEnv =
        .ok context.env := by rfl
  rw [hget]
  simp only [Except.bind]
  simp only [checkConstructorsLoop]
  unfold checkConstructorList
  simp only [ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]

namespace ConstructorListValidationTrace

def finalSeen : NameSet → List Constructor → NameSet
  | seen, [] => seen
  | seen, head :: tail => finalSeen (seen.insert head.name) tail

/-- Exact inversion for a nonempty source list. In particular the recursive
trace is indexed by the literal source tail and the accumulator obtained from
the literal source head, so omission, insertion, duplication, or reordering
cannot be hidden behind an unindexed traversal. -/
theorem nonempty_cons_iff_exact_source :
    Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) ↔
      seen.contains head.name = false ∧
      context.env.checkNoMVarNoFVar head.name head.type = .ok () ∧
      Nonempty (CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type) ∧
      Nonempty (ConstructorTypeValidationTrace stats isUnsafe familyIdx
        head.name context head.type 0 context.fuel.inductiveFuel) ∧
      Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail) := by
  constructor
  · rintro ⟨trace⟩
    cases trace with
    | cons _ _ _ fresh closed rootCheck typeTrace tailTrace =>
        exact ⟨fresh, closed, ⟨rootCheck⟩, ⟨typeTrace⟩, ⟨tailTrace⟩⟩
  · rintro ⟨fresh, closed, ⟨rootCheck⟩, ⟨typeTrace⟩, ⟨tailTrace⟩⟩
    exact ⟨.cons seen head tail fresh closed rootCheck typeTrace tailTrace⟩

/-- A duplicate at the current source position fails before all later
constructor phases, exactly as in the executable fold. -/
theorem not_nonempty_of_duplicate
    (duplicate : seen.contains head.name = true) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  have fresh := (nonempty_cons_iff_exact_source.mp trace).1
  simp_all

/-- A closedness error at the current source position excludes the trace before
the root type check or constructor telescope is entered. -/
theorem not_nonempty_of_closedness_error
    (failure : context.env.checkNoMVarNoFVar head.name head.type = .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  have closed := (nonempty_cons_iff_exact_source.mp trace).2.1
  rw [failure] at closed
  contradiction

/-- A closed-root `checkType` error excludes the trace at that exact source
constructor, before parameter and field validation. -/
theorem not_nonempty_of_root_error
    (failure : TypeChecker.M.run context.env context.safety {}
      context.lparams context.fuel (TypeChecker.checkType head.type) =
        .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  obtain ⟨rootCheck⟩ :=
    (nonempty_cons_iff_exact_source.mp trace).2.2.1
  have success := rootCheck.valid
  change TypeChecker.M.run context.withEmptyLocalContext.env
      context.withEmptyLocalContext.safety
      context.withEmptyLocalContext.lctx
      context.withEmptyLocalContext.lparams
      context.withEmptyLocalContext.fuel
      (TypeChecker.checkType head.type) = .ok rootCheck.inferred at success
  simp only [Context.withEmptyLocalContext] at success
  rw [failure] at success
  contradiction

/-- An inner parameter, field, universe, positivity, recursive-target, or
terminal-family error excludes the trace at the current constructor. -/
theorem not_nonempty_of_type_error
    (failure : checkConstructorType stats isUnsafe familyIdx
      head.name head.type context = .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  obtain ⟨typeTrace⟩ :=
    (nonempty_cons_iff_exact_source.mp trace).2.2.2.1
  have success := typeTrace.check_run
  rw [failure] at success
  contradiction

/-- Erasing an ordered trace replays the exact stateful constructor fold. -/
theorem fold_run
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) :
    checkConstructorFold context.env stats isUnsafe familyIdx seen ctors context =
      .ok (finalSeen seen ctors) := by
  induction trace with
  | nil => rfl
  | cons seen head tail fresh closed rootCheck typeTrace tailTrace ih =>
      have hroot := rootCheck.valid
      change TypeChecker.M.run context.withEmptyLocalContext.env
          context.withEmptyLocalContext.safety
          context.withEmptyLocalContext.lctx
          context.withEmptyLocalContext.lparams
          context.withEmptyLocalContext.fuel
          (TypeChecker.checkType head.type) =
        .ok rootCheck.inferred at hroot
      simp only [Context.withEmptyLocalContext] at hroot
      unfold checkConstructorFold
      simp only
      rw [fresh]
      simp only [Bool.false_eq_true, if_false,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure]
      rw [closed]
      simp only [ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure, liftExcept_apply]
      rw [withEmptyLocalContext_apply]
      rw [liftTypeChecker_apply]
      rw [hroot]
      simp only [Except.bind, readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.pure, Pure.pure, Except.pure]
      rw [typeTrace.check_run]
      change checkConstructorFold context.env stats isUnsafe familyIdx
        (seen.insert head.name) tail context =
          .ok (finalSeen (seen.insert head.name) tail)
      exact ih

/-- Any successful stateful constructor fold decomposes into the complete
source-ordered list trace; the final accumulator value itself is irrelevant. -/
theorem exists_of_fold_run
    (success : checkConstructorFold context.env stats isUnsafe familyIdx
      seen ctors context = .ok result) :
    Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) := by
  induction ctors generalizing seen result with
  | nil => exact ⟨.nil seen⟩
  | cons head tail ih =>
      unfold checkConstructorFold at success
      simp only at success
      cases hfresh : seen.contains head.name with
      | true =>
          rw [hfresh] at success
          change Except.error _ = Except.ok result at success
          contradiction
      | false =>
          rw [hfresh] at success
          simp only [Bool.false_eq_true, if_false,
            ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
            Except.bind, Except.pure] at success
          cases hclosed : context.env.checkNoMVarNoFVar
              head.name head.type with
          | error err => simp_all [liftExcept_apply, Except.bind]
          | ok closedResult =>
              cases closedResult
              rw [hclosed] at success
              simp only [liftExcept_apply, Except.bind] at success
              rw [withEmptyLocalContext_apply, liftTypeChecker_apply] at success
              cases hroot : TypeChecker.M.run context.env context.safety {}
                  context.lparams context.fuel
                  (TypeChecker.checkType head.type) with
              | error err => simp_all [Except.bind]
              | ok inferred =>
                  rw [hroot] at success
                  simp only [Except.bind] at success
                  cases htype : checkConstructorType stats isUnsafe familyIdx
                      head.name head.type context with
                  | error err => simp_all [Except.bind]
                  | ok typeResult =>
                      cases typeResult
                      rw [htype] at success
                      simp only [Except.bind, ReaderT.pure, Pure.pure,
                        Except.pure] at success
                      have htypeLoop :
                          checkConstructorType.loop stats isUnsafe familyIdx
                              head.name head.type 0 context.fuel.inductiveFuel
                              context = .ok () := by
                        unfold checkConstructorType at htype
                        simpa only [readThe, MonadReaderOf.read, ReaderT.read,
                          ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
                          Except.bind, Except.pure] using htype
                      obtain ⟨typeTrace⟩ :=
                        ConstructorTypeValidationTrace.exists_of_run htypeLoop
                      have rootCheck : CandidateCheckTypeObservation
                          context.withEmptyLocalContext head.type :=
                        ⟨inferred, by
                          simpa only [CandidateCheckTypeStep.Valid,
                            Context.withEmptyLocalContext] using hroot⟩
                      change checkConstructorFold context.env stats isUnsafe
                        familyIdx (seen.insert head.name) tail context =
                          .ok result at success
                      obtain ⟨tailTrace⟩ := ih success
                      exact ⟨.cons seen head tail hfresh hclosed rootCheck
                        typeTrace tailTrace⟩

/-- The transparent list decomposition succeeds on every constructor list
accepted by the executable stateful fold. -/
theorem buildExecution_ok_of_fold_run
    (success : checkConstructorFold context.env stats isUnsafe familyIdx
      seen ctors context = .ok result) :
    ∃ trace, buildExecution stats isUnsafe familyIdx context seen ctors =
      .ok trace := by
  induction ctors generalizing seen result with
  | nil => exact ⟨_, rfl⟩
  | cons head tail ih =>
      unfold checkConstructorFold at success
      simp only at success
      unfold buildExecution
      split
      next hfresh =>
        rw [hfresh] at success
        change Except.error _ = Except.ok result at success
        contradiction
      next hfresh =>
        rw [hfresh] at success
        simp only [Bool.false_eq_true, if_false,
          ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
          Except.bind, Except.pure] at success
        split
        next error heq =>
          rw [heq] at success
          simp [liftExcept_apply, Except.bind] at success
        next heq =>
          rw [heq] at success
          simp only [liftExcept_apply, Except.bind] at success
          rw [withEmptyLocalContext_apply, liftTypeChecker_apply] at success
          split
          next error heq2 =>
            rw [heq2] at success
            simp [Except.bind] at success
          next inferred heq2 =>
            rw [heq2] at success
            simp only [Except.bind] at success
            cases htype : checkConstructorType stats isUnsafe familyIdx
                head.name head.type context with
            | error err => simp_all [Except.bind]
            | ok typeResult =>
                cases typeResult
                rw [htype] at success
                simp only [Except.bind, ReaderT.pure, Pure.pure,
                  Except.pure] at success
                have htypeLoop :
                    checkConstructorType.loop stats isUnsafe familyIdx
                        head.name head.type 0 context.fuel.inductiveFuel
                        context = .ok () := by
                  unfold checkConstructorType at htype
                  simpa only [readThe, MonadReaderOf.read, ReaderT.read,
                    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
                    Except.bind, Except.pure] using htype
                obtain ⟨typeTrace, hT⟩ :=
                  ConstructorTypeValidationTrace.buildExecution_ok_of_run
                    htypeLoop
                rw [hT]
                change checkConstructorFold context.env stats isUnsafe
                  familyIdx (seen.insert head.name) tail context =
                    .ok result at success
                obtain ⟨tailTrace, htl⟩ := ih success
                rw [htl]
                exact ⟨_, rfl⟩

/-- The stateful list fold's exact error value excludes a complete trace for
that same source list and incoming duplicate-name accumulator. -/
theorem not_nonempty_of_fold_error
    (failure : checkConstructorFold context.env stats isUnsafe familyIdx
      seen ctors context = .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) := by
  rintro ⟨trace⟩
  have success := trace.fold_run
  rw [failure] at success
  contradiction

/-- Erasing an ordered list trace replays the transparent list validator. -/
theorem run
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) :
    checkConstructorList stats isUnsafe familyIdx context seen ctors = .ok () := by
  unfold checkConstructorList
  rw [trace.fold_run]
  rfl

end ConstructorListValidationTrace

/-! ## Arbitrary mutual-block validation owners -/

/-- The exact result selected when the ordinary family validator reaches its
continuation.  Retaining the reader context matters: later constructor
validation uses the shared parameters and local declarations installed by
that very run. -/
structure FamilyValidationBlockResult where
  stats : InductiveStats
  validationContext : Context

/-- Observe the successful continuation of `checkInductiveTypes` without
changing any validation branch or error. -/
def observeFamilyValidationBlock (nparams : Nat)
    (indTypes : List InductiveType) (context : Context) :
    Except Exception FamilyValidationBlockResult :=
  checkInductiveTypes nparams indTypes.toArray
    (fun stats => fun validationContext =>
      .ok ⟨stats, validationContext⟩) context

/-- Complete retained family-validation run for an arbitrary source-ordered
block.

`run` is the real validator execution, so every later family has already
passed the kernel's definitional parameter comparison and result-level
equivalence phase.  The remaining equations expose the terminal invariants
which Lean asserts before invoking the continuation. -/
structure FamilyValidationBlockRun (nparams : Nat)
    (indTypes : List InductiveType) (context : Context) where
  result : FamilyValidationBlockResult
  run : observeFamilyValidationBlock nparams indTypes context = .ok result
  params_size : result.stats.params.size = nparams
  nindices_size : result.stats.nindices.size = indTypes.length
  indConsts_size : result.stats.indConsts.size = indTypes.length

namespace FamilyValidationBlockRun

/-- Execute and retain the ordinary family validator.  The explicit terminal
checks mirror its internal assertions and make malformed instrumentation fail
instead of yielding a weaker certificate. -/
def buildExecution (nparams : Nat) (indTypes : List InductiveType)
    (context : Context) :
    Except Exception (FamilyValidationBlockRun nparams indTypes context) :=
  match hrun : observeFamilyValidationBlock nparams indTypes context with
  | .error error => .error error
  | .ok result =>
    if hparams : result.stats.params.size = nparams then
      if hnindices : result.stats.nindices.size = indTypes.length then
        if hconsts : result.stats.indConsts.size = indTypes.length then
          .ok {
            result
            run := hrun
            params_size := hparams
            nindices_size := hnindices
            indConsts_size := hconsts }
        else .error (.other "family-validation constant-count invariant failed")
      else .error (.other "family-validation index-count invariant failed")
    else .error (.other "family-validation parameter-count invariant failed")

/-- Shared parameters selected by the first family and definitionally checked
against every later family. -/
def parameters (run : FamilyValidationBlockRun nparams indTypes context) :
    Array Expr :=
  run.result.stats.params

/-- Common result universe selected by the first family and equivalence-
checked against every later family. -/
def resultLevel (run : FamilyValidationBlockRun nparams indTypes context) :
    Level :=
  run.result.stats.resultLevel

end FamilyValidationBlockRun

/-- Source-indexed constructor traces for every family in a block.  The
natural index advances with the source list, so a trace for one family cannot
be reused at another family ordinal. -/
inductive ConstructorBlockValidationTraces
    (stats : InductiveStats) (isUnsafe : Bool) (context : Context) :
    Nat → List InductiveType → Type where
  | nil {familyIdx : Nat} :
      ConstructorBlockValidationTraces stats isUnsafe context familyIdx []
  | cons {familyIdx : Nat} {type : InductiveType}
      {types : List InductiveType}
      (head : ConstructorListValidationTrace stats isUnsafe familyIdx
        context {} type.ctors)
      (tail : ConstructorBlockValidationTraces stats isUnsafe context
        (familyIdx + 1) types) :
      ConstructorBlockValidationTraces stats isUnsafe context familyIdx
        (type :: types)

namespace ConstructorBlockValidationTraces

/-- Family-, constructor-, and field-ordered recursive-target matrix selected
by the executable arbitrary-block validator. -/
def targets :
    ConstructorBlockValidationTraces stats isUnsafe context familyIdx types →
      List (List (List (Option ConstructorPositivityTrace.Target)))
  | .nil => []
  | .cons head tail => head.targets :: tail.targets

/-- Execute each source-indexed list trace in the one shared post-family
context. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (context : Context) :
    (familyIdx : Nat) → (types : List InductiveType) →
      Except Exception
        (ConstructorBlockValidationTraces stats isUnsafe context
          familyIdx types)
  | _, [] => .ok .nil
  | familyIdx, type :: types =>
    match ConstructorListValidationTrace.buildExecution stats isUnsafe
        familyIdx context {} type.ctors with
    | .error error => .error error
    | .ok head =>
      match buildExecution stats isUnsafe context (familyIdx + 1) types with
      | .error error => .error error
      | .ok tail => .ok (.cons head tail)

end ConstructorBlockValidationTraces

/-- Complete operational constructor-validation owner for an arbitrary
mutual block.  `run` is the actual block call; `traces` retains every
family/constructor/field branch, including cross-family target ordinals and
recursive-Pi paths. -/
structure ConstructorBlockValidationRun
    (indTypes : List InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) where
  traces : ConstructorBlockValidationTraces stats isUnsafe context 0 indTypes
  run : checkConstructors indTypes.toArray stats isUnsafe context = .ok ()

namespace ConstructorBlockValidationRun

/-- Execute the real block validator and retain the exact dependent trace
hierarchy for that same source list. -/
def buildExecution (indTypes : List InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (context : Context) :
    Except Exception
      (ConstructorBlockValidationRun indTypes stats isUnsafe context) :=
  match hrun : checkConstructors indTypes.toArray stats isUnsafe context with
  | .error error => .error error
  | .ok () =>
    match ConstructorBlockValidationTraces.buildExecution stats isUnsafe
        context 0 indTypes with
    | .error error => .error error
    | .ok traces => .ok ⟨traces, hrun⟩

end ConstructorBlockValidationRun

/-- The complete retained operational constructor-validation run for one
singleton family. -/
structure ConstructorValidationRun
    (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) where
  trace : ConstructorListValidationTrace stats isUnsafe 0 context {}
    indType.ctors

namespace ConstructorValidationRun

/-- Transparent decomposition of the ordinary singleton constructor
validator.  Successful output is executable data rather than a
`Classical.choice`, which lets subsequent D2/D3 audits compute over the exact
retained branch structure. -/
def buildExecution (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) :
    Except Exception
      (ConstructorValidationRun indType stats isUnsafe context) :=
  match ConstructorListValidationTrace.buildExecution stats isUnsafe 0
      context {} indType.ctors with
  | .error error => .error error
  | .ok trace => .ok ⟨trace⟩

/-- The transparent singleton decomposition succeeds on every source family
accepted by the real constructor validator. -/
theorem buildExecution_ok_of_run
    (success : checkConstructors #[indType] stats isUnsafe context = .ok ()) :
    ∃ validation, buildExecution indType stats isUnsafe context =
      .ok validation := by
  rw [checkConstructors_singleton_eq_checkConstructorList] at success
  unfold checkConstructorList at success
  cases hfold : checkConstructorFold context.env stats isUnsafe 0 {}
      indType.ctors context with
  | error err => simp_all [Functor.map, Except.map]
  | ok result =>
      obtain ⟨trace, htrace⟩ :=
        ConstructorListValidationTrace.buildExecution_ok_of_fold_run hfold
      unfold buildExecution
      rw [htrace]
      exact ⟨_, rfl⟩

/-- Recomposition: retained operational evidence replays the real singleton
`checkConstructors` execution exactly. -/
theorem run
    (validation : ConstructorValidationRun indType stats isUnsafe context) :
    checkConstructors #[indType] stats isUnsafe context = .ok () := by
  rw [checkConstructors_singleton_eq_checkConstructorList]
  exact validation.trace.run

/-- Decomposition: every successful real singleton `checkConstructors` run
has complete retained operational evidence. -/
theorem nonempty_of_run
    (success : checkConstructors #[indType] stats isUnsafe context = .ok ()) :
    Nonempty (ConstructorValidationRun indType stats isUnsafe context) := by
  rw [checkConstructors_singleton_eq_checkConstructorList] at success
  unfold checkConstructorList at success
  cases hfold : checkConstructorFold context.env stats isUnsafe 0 {}
      indType.ctors context with
  | error err =>
      simp_all [Functor.map, Except.map]
  | ok result =>
      obtain ⟨trace⟩ :=
        ConstructorListValidationTrace.exists_of_fold_run hfold
      exact ⟨⟨trace⟩⟩

/-- Choose the operational shape supplied by a successful run by replaying
the transparent decomposition.  The success premise only discharges the
impossible error branch, so the retained evidence is computed by
`buildExecution` rather than selected through `Classical.choice`. -/
def of_run
    (success : checkConstructors #[indType] stats isUnsafe context = .ok ()) :
    ConstructorValidationRun indType stats isUnsafe context :=
  match h : buildExecution indType stats isUnsafe context with
  | .ok validation => validation
  | .error _ => absurd (buildExecution_ok_of_run success) (by simp [h])

/-- Exact decomposition/recomposition contract for singleton constructor
validation. -/
theorem nonempty_iff_checkConstructors_ok :
    Nonempty (ConstructorValidationRun indType stats isUnsafe context) ↔
      checkConstructors #[indType] stats isUnsafe context = .ok () := by
  constructor
  · rintro ⟨validation⟩
    exact validation.run
  · exact nonempty_of_run

/-- Any phase-specific executable error excludes a successful retained run. -/
theorem not_nonempty_of_error
    (failure : checkConstructors #[indType] stats isUnsafe context = .error err) :
    ¬ Nonempty (ConstructorValidationRun indType stats isUnsafe context) := by
  intro validation
  have success := nonempty_iff_checkConstructors_ok.mp validation
  rw [failure] at success
  contradiction

end ConstructorValidationRun

#guard_named_axioms Ix.Theory.Named.AddInductive.FamilyValidationBlockRun.buildExecution [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorBlockValidationRun.buildExecution [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorListValidationTrace.nonempty_cons_iff_exact_source [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorValidationRun.run [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorValidationRun.nonempty_of_run [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorValidationRun.of_run [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorValidationRun.nonempty_iff_checkConstructors_ok [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.AddInductive.ConstructorValidationRun.not_nonempty_of_error [propext, Classical.choice, Quot.sound]

end AddInductive
end Ix.Theory.Named
