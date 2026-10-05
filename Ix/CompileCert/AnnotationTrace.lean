import Ix.CompileCert.Installed

/-! # Annotation traces of the checker's runs

`AnnotationTrace`: the cached checker's annotation of binders, lets,
definition, opaque and theorem declarations, followed through `checkDecls`
runs, so that each installed value is denoted in the strong model.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

namespace AnnotationTrace

open Kernel Kernel.Cached

/-- The exact pure trace of an actual cached annotation, including memo
hits. The fuel belongs to the proved specification trace; it is not asserted
equal to the cached knot's fuel or to another installation's fuel. -/
theorem cached_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {expression result : Kernel.Expr} {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth expression)
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth expression initial = .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      ∃ pureFuel, annotateCore mode env pureFuel depth expression = .ok result := by
  obtain ⟨state', pureResult, ⟨same, resultScope⟩, pureFuel, pureRun⟩ :=
    (ssimC verified env environment fuel).annotate state rfl scope result final run
  cases same
  exact ⟨state', resultScope, pureFuel, pureRun⟩

theorem constant_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {name : Kernel.Name} {levels : List Kernel.Level} {result : Kernel.Expr}
    (run : annotateCore mode env fuel depth (.const name levels) = .ok result) :
    result = .const name levels := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel =>
    rw [annotateCore_succ] at run
    simpa only [annotateBody, pure, Except.pure, Except.ok.injEq] using run.symm

/-- Actual constant annotation keeps the exact name/levels on a cache hit
as well as a miss. This is a syntax statement, not proof that the constant
resolves or that two models assign its instance the same value. -/
theorem constant_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {name : Kernel.Name} {levels : List Kernel.Level} {result : Kernel.Expr}
    {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial)
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (.const name levels) initial =
      .ok (result, final)) : result = .const name levels := by
  obtain ⟨_, _, _, pureRun⟩ := cached_pure verified environment state
    (Kernel.Expr.WScoped.of_not_hasFvar rfl) run
  exact constant_pure pureRun

/-- Two independently successful constant annotations retain the supplied
name/universe image without equating the installations or their cache states. -/
theorem paired_constant_cached {sourceMode targetMode : CheckMode}
    {sourceEnv targetEnv : Env} {sourceFuel targetFuel depth : Nat}
    {sourceInitial sourceFinal targetInitial targetFinal : CState}
    {name : Kernel.Name} {levels : List Kernel.Level} {sourceResult targetResult : Kernel.Expr}
    (rename : InstalledRenaming)
    (sourceVerified : sourceMode.verifiedChecks = true) (targetVerified : targetMode.verifiedChecks = true)
    (sourceEnvironment : EnvWF sourceEnv) (targetEnvironment : EnvWF targetEnv)
    (sourceState : CSOK sourceMode sourceEnv sourceInitial) (targetState : CSOK targetMode targetEnv targetInitial)
    (sourceRun : (coreKnotI sourceMode (mkFEnv sourceEnv) sourceFuel).annotate depth (.const name levels)
      sourceInitial = .ok (sourceResult, sourceFinal))
    (targetRun : (coreKnotI targetMode (mkFEnv targetEnv) targetFuel).annotate depth
      (.const (rename.name name) (rename.universes name levels)) targetInitial = .ok (targetResult, targetFinal)) :
    targetResult = rename.expr sourceResult := by
  rw [constant_cached sourceVerified sourceEnvironment sourceState sourceRun,
    constant_cached targetVerified targetEnvironment targetState targetRun]
  rfl

/-- The pure specification's actual application subtraces. This does not
claim that a cached hit reruns either subexpression. -/
def ApplicationAnnotation (mode : CheckMode) (env : Env) (depth : Nat)
    (function argument result : Kernel.Expr) : Prop :=
  ∃ fuel, ∃ annotatedFunction annotatedArgument,
    annotateCore mode env fuel depth function = .ok annotatedFunction ∧
    annotateCore mode env fuel depth argument = .ok annotatedArgument ∧
    result = .app annotatedFunction annotatedArgument

theorem application_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {function argument result : Kernel.Expr}
    (run : annotateCore mode env fuel depth (.app function argument) = .ok result) :
    ApplicationAnnotation mode env depth function argument result := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel =>
    obtain ⟨annotatedFunction, annotatedArgument, functionRun, argumentRun, shape⟩ := annotateCore_app_inv run
    exact ⟨fuel, annotatedFunction, annotatedArgument, functionRun, argumentRun, shape⟩

theorem application_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {function argument result : Kernel.Expr} {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth (.app function argument))
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (.app function argument) initial =
      .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      ApplicationAnnotation mode env depth function argument result := by
  obtain ⟨state', resultScope, _, pureRun⟩ := cached_pure verified environment state scope run
  exact ⟨state', resultScope, application_pure pureRun⟩

inductive AnnotationBinder where
  | lam | pi

def AnnotationBinder.expr : AnnotationBinder → Kernel.Expr → Kernel.Expr → BinderMeta → Kernel.Expr
  | .lam => .lam
  | .pi => .forallE

def AnnotationBinder.write (kind : AnnotationBinder) (mode : CheckMode) (env : Env)
    (fuel depth : Nat) (body : Kernel.Expr) : CheckM PropWhen :=
  match kind with
  | .lam => annotPwLam (pureFns mode env fuel) env depth body
  | .pi => annotPwPi (pureFns mode env fuel) env depth body

/-- Actual binder annotation data, including the write/reuse branch for
its PropWhen datum. The datum's semantic validity and cross-installation
regime agreement are not conclusions of this annotation-only receipt. -/
structure BinderAnnotationTrace (kind : AnnotationBinder) (mode : CheckMode) (env : Env)
    (depth : Nat) (type body : Kernel.Expr) (metadata : BinderMeta) (result : Kernel.Expr) where
  fuel : Nat
  annotatedType : Kernel.Expr
  annotatedBody : Kernel.Expr
  datum : PropWhen
  typeRun : annotateCore mode env fuel depth type = .ok annotatedType
  bodyRun : annotateCore mode env fuel (depth + 1)
    (body.instantiate1 (.fvar depth annotatedType)) = .ok annotatedBody
  datumRun :
    (pwWritten metadata.pw = false ∧
      kind.write mode env fuel (depth + 1) annotatedBody = .ok datum) ∨
    (pwWritten metadata.pw = true ∧ datum = metadata.pw)
  shape : result = kind.expr annotatedType (annotatedBody.abstract1 depth) ⟨datum⟩

private theorem annotate_binder_succ (kind : AnnotationBinder) (mode : CheckMode) (env : Env)
    (fuel depth : Nat) (type body : Kernel.Expr) (metadata : BinderMeta) :
    annotateCore mode env (fuel + 1) depth (kind.expr type body metadata) = (do
      let annotatedType ← annotateCore mode env fuel depth type
      let annotatedBody ← annotateCore mode env fuel (depth + 1)
        (body.instantiate1 (.fvar depth annotatedType))
      let datum ← if !pwWritten metadata.pw then
          kind.write mode env fuel (depth + 1) annotatedBody
        else pure metadata.pw
      pure (kind.expr annotatedType (annotatedBody.abstract1 depth) ⟨datum⟩)) := by
  cases kind <;> rw [annotateCore_succ] <;> rfl

theorem binder_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type body result : Kernel.Expr} {metadata : BinderMeta} (kind : AnnotationBinder)
    (run : annotateCore mode env fuel depth (kind.expr type body metadata) = .ok result) :
    Nonempty (BinderAnnotationTrace kind mode env depth type body metadata result) := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel =>
    rw [annotate_binder_succ] at run
    cases typeRun : annotateCore mode env fuel depth type with
    | error reason => simp [typeRun, bind, Except.bind] at run
    | ok annotatedType =>
      simp only [typeRun, bind, Except.bind] at run
      cases bodyRun : annotateCore mode env fuel (depth + 1)
          (body.instantiate1 (.fvar depth annotatedType)) with
      | error reason => simp [bodyRun] at run
      | ok annotatedBody =>
        simp only [bodyRun] at run
        cases written : pwWritten metadata.pw with
        | false =>
          simp only [written, Bool.not_false, ↓reduceIte] at run
          cases datumRun : kind.write mode env fuel (depth + 1) annotatedBody with
          | error reason => simp [datumRun] at run
          | ok datum =>
            simp only [datumRun, pure, Except.pure, Except.ok.injEq] at run
            exact ⟨⟨fuel, annotatedType, annotatedBody, datum, typeRun, bodyRun,
              .inl ⟨written, datumRun⟩, run.symm⟩⟩
        | true =>
          simp [written, pure, Except.pure] at run
          exact ⟨⟨fuel, annotatedType, annotatedBody, metadata.pw, typeRun, bodyRun,
            .inr ⟨written, rfl⟩, run.symm⟩⟩

theorem binder_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type body result : Kernel.Expr} {metadata : BinderMeta} {initial final : CState}
    (kind : AnnotationBinder)
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth (kind.expr type body metadata))
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (kind.expr type body metadata) initial =
      .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      Nonempty (BinderAnnotationTrace kind mode env depth type body metadata result) := by
  obtain ⟨state', resultScope, _, pureRun⟩ := cached_pure verified environment state scope run
  exact ⟨state', resultScope, binder_pure kind pureRun⟩

/-- Reassembly uses the actual annotated domain, opened body and datum on
each side. In particular the datum correspondence remains an explicit
obligation; raw source normalization cannot supply it. -/
theorem BinderAnnotationTrace.paired_image {kind : AnnotationBinder}
    {sourceMode targetMode : CheckMode} {sourceEnv targetEnv : Env} {depth : Nat}
    {sourceType sourceBody sourceResult targetType targetBody targetResult : Kernel.Expr}
    {sourceMetadata targetMetadata : BinderMeta}
    (source : BinderAnnotationTrace kind sourceMode sourceEnv depth sourceType sourceBody sourceMetadata sourceResult)
    (target : BinderAnnotationTrace kind targetMode targetEnv depth targetType targetBody targetMetadata targetResult)
    (rename : InstalledRenaming)
    (domainImage : target.annotatedType = rename.expr source.annotatedType)
    (bodyImage : target.annotatedBody = rename.expr source.annotatedBody)
    (datumImage : (⟨target.datum⟩ : BinderMeta) = rename.binder ⟨source.datum⟩) :
    targetResult = rename.expr sourceResult := by
  rw [source.shape, target.shape, domainImage, bodyImage, datumImage, ← rename.abstract1]
  cases kind <;> rfl

/-- Semantic binder reassembly from the actual annotation receipts. The
domain/body premises are semantic images, not syntactic/canonical equality.
The exact selected-universe datum image supplies regime agreement; no such
agreement is inferred merely from both annotation runs succeeding. -/
theorem BinderAnnotationTrace.semantic_image {V : Type u} [Kernel.SetTheory V]
    {kind : AnnotationBinder} {sourceMode targetMode : CheckMode}
    {sourceEnv targetEnv : Env} {depth : Nat}
    {sourceType sourceBody sourceResult targetType targetBody targetResult : Kernel.Expr}
    {sourceMetadata targetMetadata : BinderMeta}
    (source : BinderAnnotationTrace kind sourceMode sourceEnv depth sourceType sourceBody sourceMetadata sourceResult)
    (target : BinderAnnotationTrace kind targetMode targetEnv depth targetType targetBody targetMetadata targetResult)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V)
    (domainImage : InstalledExprImage sourceValues targetValues sourceEnv targetEnv
      (image.valuation targetLevels) targetLevels source.annotatedType target.annotatedType)
    (bodyImage : InstalledExprImage sourceValues targetValues sourceEnv targetEnv
      (image.valuation targetLevels) targetLevels (source.annotatedBody.abstract1 depth)
      (target.annotatedBody.abstract1 depth))
    (datumImage : target.datum = image.datum source.datum) :
    InstalledExprImage sourceValues targetValues sourceEnv targetEnv
      (image.valuation targetLevels) targetLevels sourceResult targetResult := by
  have regimes : Kernel.regime (image.valuation targetLevels) source.datum =
      Kernel.regime targetLevels target.datum := by
    rw [datumImage]
    exact (image.regime targetLevels ⟨source.datum⟩).symm
  rw [source.shape, target.shape]
  cases kind with
  | lam => exact .lam domainImage bodyImage regimes
  | pi => exact .forallE domainImage bodyImage regimes

/-- The checked let-elimination trace, including all official let checks.
The reduct substitutes the immutable original value, not the independently
annotated value. The latter remains the subject of value-type checking. -/
def LetAnnotation (mode : CheckMode) (env : Env) (depth : Nat)
    (type value body result : Kernel.Expr) : Prop :=
  ∃ fuel, ∃ annotatedType annotatedValue : Kernel.Expr,
    annotateCore mode env fuel depth type = .ok annotatedType ∧
    annotateCore mode env fuel depth value = .ok annotatedValue ∧
    annotateCore mode env fuel depth (body.instantiate1 value) = .ok result ∧
    ∃ typeType sortLevel valueType,
      inferTypeCore mode env fuel depth annotatedType = .ok typeType ∧
      ensureSortCore mode env fuel depth typeType = .ok sortLevel ∧
      inferTypeCore mode env fuel depth annotatedValue = .ok valueType ∧
      isDefEqCore mode env fuel depth valueType annotatedType = .ok true

theorem let_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type value body result : Kernel.Expr}
    (run : annotateCore mode env fuel depth (.letE type value body) = .ok result) :
    LetAnnotation mode env depth type value body result := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel => exact ⟨fuel, annotateCore_letE_inv run⟩

/-- Actual cached-call attachment using the existing invariant-state
simulation. Prefix `EnvWF`/`CSOK` remain explicit; neither a cache hit nor a
successful target installation is used to invent a source-prefix invariant. -/
theorem let_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type value body result : Kernel.Expr} {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth (.letE type value body))
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (.letE type value body) initial =
      .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      LetAnnotation mode env depth type value body result := by
  obtain ⟨state', pureResult, ⟨same, resultScope⟩, pureFuel, pureRun⟩ :=
    (ssimC verified env environment fuel).annotate state rfl scope result final run
  cases same
  exact ⟨state', resultScope, let_pure pureRun⟩

/-- Both successful let annotations reach the exact related raw residuals.
Their fuels and checking/annotation traces remain independent. This records
the endpoint square needed by a recursive annotation simulation; it does not
assert that merely normalizing the source relates the final annotations. -/
theorem LetAnnotation.paired_residuals {sourceMode targetMode : CheckMode}
    {sourceEnv targetEnv : Env} {depth : Nat}
    {type value body sourceResult targetResult : Kernel.Expr}
    (rename : InstalledRenaming)
    (source : LetAnnotation sourceMode sourceEnv depth type value body sourceResult)
    (target : LetAnnotation targetMode targetEnv depth (rename.expr type) (rename.expr value)
      (rename.expr body) targetResult) :
    ∃ sourceFuel targetFuel,
      annotateCore sourceMode sourceEnv sourceFuel depth (body.instantiate1 value) = .ok sourceResult ∧
      annotateCore targetMode targetEnv targetFuel depth (rename.expr (body.instantiate1 value)) =
        .ok targetResult := by
  obtain ⟨sourceFuel, _, _, _, _, sourceRun, _⟩ := source
  obtain ⟨targetFuel, _, _, _, _, targetRun, _⟩ := target
  exact ⟨sourceFuel, targetFuel, sourceRun, (rename.instantiate1 body value 0).symm ▸ targetRun⟩

/-- Full header provenance for the actual cached annotation call. This is
not a claim that annotation preserves the raw expression's denotation. -/
theorem header_fields {mode : CheckMode} {fe : FEnv} {cv cvA : Kernel.ConstantVal}
    {jty : Kernel.Expr} {initial final : CState}
    (run : annotConstantValC mode fe cv initial = .ok ((cvA, jty), final)) :
    cvA = { cv with type := jty } ∧ ∃ afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 cv.type initial = .ok (jty, afterAnnotation) := by
  unfold annotConstantValC at run
  by_cases h1 : (fe.find? cv.name).isSome = true
  · rw [ite_eq_left h1] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h1] at run
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [ite_eq_left h2] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h2] at run
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [ite_eq_left h3] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h3] at run
  by_cases h4 : Kernel.Name.nodup cv.levelParams = true
  case neg => rw [ite_eq_right h4] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h4] at run
  by_cases h5 : Kernel.Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [ite_eq_right h5] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h5] at run
  by_cases h6 : Kernel.Expr.hasFvar cv.type = true
  · rw [ite_eq_left h6] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h6] at run
  obtain ⟨annotated, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases h7 : Kernel.Expr.allLevelParamsDefinedC cv.levelParams annotated = true
  case neg => rw [ite_eq_right h7] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h7] at run
  by_cases h8 : constsResolveFC fe annotated = true
  case neg => rw [ite_eq_right h8] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h8] at run
  obtain ⟨result, _⟩ := pureC_ok run
  have pair := Prod.mk.inj result
  obtain rfl := pair.2
  exact ⟨pair.1.symm, afterAnnotation, annotation⟩

theorem theorem_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (run : annotStepC mode pins index fe pending (.thmDecl header value) initial =
      .ok ((fe', pending'), final)) :
    ∃ annotated afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed =
        .ok (annotated, afterAnnotation) ∧
      fe'.env.consts = .thmInfo { header with type := annotated } value :: fe.env.consts := by
  unfold annotStepC at run
  simp only [] at run
  obtain ⟨_, afterFlush, flush, run⟩ := bindC_ok run
  rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
  have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
  subst flushed
  obtain ⟨pair, afterHeader, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, annotated⟩ := pair
  obtain ⟨rfl, afterAnnotation, annotation⟩ := header_fields headerRun
  obtain ⟨_, afterRecord, _, run⟩ := bindC_ok run
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
  exact ⟨annotated, afterAnnotation, annotation, rfl⟩

/-- Exact annotation call for the value half; the guards and cache record
are not confused with a raw-to-annotated semantic preservation theorem. -/
theorem value_fields {mode : CheckMode} {fe : FEnv} {header : Kernel.ConstantVal}
    {type value annotated : Kernel.Expr} {record : Bool} {initial final : CState}
    (run : annotValC mode fe header type value record initial = .ok (annotated, final)) :
    ∃ afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 value initial = .ok (annotated, afterAnnotation) := by
  unfold annotValC at run
  by_cases bounded : value.looseBVarsBounded 0 = true
  case neg => rw [ite_eq_right bounded] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left bounded] at run
  by_cases free : value.hasFvar = true
  · rw [ite_eq_left free] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right free] at run
  obtain ⟨image, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases levels : image.allLevelParamsDefinedC header.levelParams = true
  case neg => rw [ite_eq_right levels] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left levels] at run
  by_cases resolved : constsResolveFC fe image = true
  case neg => rw [ite_eq_right resolved] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left resolved] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨rfl, _⟩ := pureC_ok run
  exact ⟨afterAnnotation, annotation⟩

theorem prepared_value_fields {mode : CheckMode} {fe : FEnv}
    {header installedHeader : Kernel.ConstantVal} {value type annotated : Kernel.Expr}
    {record : Bool} {initial final : CState}
    (run : annotValueC mode fe header value record initial = .ok ((installedHeader, type, annotated), final)) :
    installedHeader = { header with type := type } ∧
    ∃ afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode fe header initial.flushed = .ok ((installedHeader, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) := by
  unfold annotValueC at run
  obtain ⟨_, afterFlush, flush, run⟩ := bindC_ok run
  rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
  have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
  subst flushed
  obtain ⟨pair, beforeValue, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, typeA⟩ := pair
  obtain ⟨image, _, valueRun, run⟩ := bindC_ok run
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ result
  obtain ⟨headerShape, afterType, typeRun⟩ := header_fields headerRun
  obtain ⟨afterValue, annotation⟩ := value_fields valueRun
  exact ⟨headerShape, afterType, beforeValue, afterValue, typeRun, headerRun, annotation⟩

/-- Primitive paths use the checking header routine, which performs inference
after annotation. Its final cache state must not be identified with the
ordinary install-only header routine's state. -/
theorem checked_header_fields {mode : CheckMode} {fe : FEnv}
    {header installedHeader : Kernel.ConstantVal} {type : Kernel.Expr} {initial final : CState}
    (run : checkConstantValC mode fe header initial = .ok ((installedHeader, type), final)) :
    installedHeader = { header with type := type } ∧ ∃ afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial = .ok (type, afterAnnotation) := by
  unfold checkConstantValC at run
  by_cases h1 : (fe.find? header.name).isSome = true
  · rw [ite_eq_left h1] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h1] at run
  by_cases h2 : reservedBasisNames.contains header.name = true
  · rw [ite_eq_left h2] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h2] at run
  by_cases h3 : header.name.isProjFnShape = true
  · rw [ite_eq_left h3] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h3] at run
  by_cases h4 : Kernel.Name.nodup header.levelParams = true
  case neg => rw [ite_eq_right h4] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h4] at run
  by_cases h5 : Kernel.Expr.looseBVarsBounded 0 header.type = true
  case neg => rw [ite_eq_right h5] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h5] at run
  by_cases h6 : Kernel.Expr.hasFvar header.type = true
  · rw [ite_eq_left h6] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h6] at run
  obtain ⟨annotated, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases h7 : Kernel.Expr.allLevelParamsDefinedC header.levelParams annotated = true
  case neg => rw [ite_eq_right h7] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h7] at run
  by_cases h8 : constsResolveFC fe annotated = true
  case neg => rw [ite_eq_right h8] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h8] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨result, _⟩ := pureC_ok run
  have pair := Prod.mk.inj result
  obtain rfl := pair.2
  exact ⟨pair.1.symm, afterAnnotation, annotation⟩

theorem checked_definition_fields {mode : CheckMode} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {type value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (run : checkDefnValC mode fe header type value hint initial = .ok (finalEnv, final)) :
    ∃ annotated afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 value initial = .ok (annotated, afterAnnotation) ∧
      finalEnv = fe.push (.defnInfo header annotated hint) := by
  unfold checkDefnValC at run
  by_cases bounded : value.looseBVarsBounded 0 = true
  case neg => rw [ite_eq_right bounded] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left bounded] at run
  by_cases free : value.hasFvar = true
  · rw [ite_eq_left free] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right free] at run
  obtain ⟨image, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases levels : image.allLevelParamsDefinedC header.levelParams = true
  case neg => rw [ite_eq_right levels] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left levels] at run
  by_cases resolved : constsResolveFC fe image = true
  case neg => rw [ite_eq_right resolved] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left resolved] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨equal, _, _, run⟩ := bindC_ok run
  cases equal with
  | false => exact absurd run throwC_bind_ok
  | true =>
    obtain ⟨result, _⟩ := pureC_ok run
    exact ⟨image, afterAnnotation, annotation, result.symm⟩

theorem checked_opaque_fields {mode : CheckMode} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {type value : Kernel.Expr} {initial final : CState}
    (run : checkOpaqueValC mode fe header type value initial = .ok (finalEnv, final)) :
    ∃ annotated afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 value initial = .ok (annotated, afterAnnotation) ∧
      finalEnv = fe.push (.axiomInfo header) := by
  unfold checkOpaqueValC at run
  by_cases bounded : value.looseBVarsBounded 0 = true
  case neg => rw [ite_eq_right bounded] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left bounded] at run
  by_cases free : value.hasFvar = true
  · rw [ite_eq_left free] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right free] at run
  obtain ⟨image, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases levels : image.allLevelParamsDefinedC header.levelParams = true
  case neg => rw [ite_eq_right levels] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left levels] at run
  by_cases resolved : constsResolveFC fe image = true
  case neg => rw [ite_eq_right resolved] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left resolved] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨equal, _, _, run⟩ := bindC_ok run
  cases equal with
  | false => exact absurd run throwC_bind_ok
  | true =>
    obtain ⟨result, _⟩ := pureC_ok run
    exact ⟨image, afterAnnotation, annotation, result.symm⟩

private theorem yields_result {α : Type} {action : CheckCM α} {initial final : CState}
    {result : α} {property : α → Prop}
    (run : action initial = .ok (result, final)) (guarantee : Yields action property) : property result :=
  guarantee initial result final run

theorem checked_definition_decl {mode : CheckMode} {pins : List NatOpPinSet} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (run : checkDeclC mode pins fe (.defnDecl header value hint) initial = .ok (finalEnv, final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial = .ok (type, afterType) ∧
      checkConstantValC mode fe header initial =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      finalEnv = fe.push (.defnInfo { header with type := type } annotated hint) := by
  unfold checkDeclC at run
  obtain ⟨pair, beforeValue, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type⟩ := pair
  obtain ⟨rfl, afterType, typeRun⟩ := checked_header_fields headerRun
  by_cases pinned : (natOpNames.contains header.name || natDivModNames.contains header.name) = true
  · simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, valueRun, run⟩ := bindC_ok run
    have unchanged : finalEnv = checkedEnv := yields_result (property := fun result => result = checkedEnv) run (by
      yields
      all_goals exact Yields.pure rfl)
    subst finalEnv
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_definition_fields valueRun
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩
  · simp only [pinned] at run
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_definition_fields run
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩

theorem checked_opaque_decl {mode : CheckMode} {pins : List NatOpPinSet} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (run : checkDeclC mode pins fe (.opaqueDecl header value) initial = .ok (finalEnv, final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial = .ok (type, afterType) ∧
      checkConstantValC mode fe header initial =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      finalEnv = fe.push (.axiomInfo { header with type := type }) := by
  unfold checkDeclC at run
  obtain ⟨pair, beforeValue, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type⟩ := pair
  obtain ⟨rfl, afterType, typeRun⟩ := checked_header_fields headerRun
  by_cases pinned : reduceOpNames.contains header.name = true
  · simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, valueRun, run⟩ := bindC_ok run
    obtain ⟨_, _, _, run⟩ := bindC_ok run
    obtain ⟨rfl, _⟩ := pureC_ok run
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_opaque_fields valueRun
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩
  · simp only [pinned] at run
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_opaque_fields run
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩

/-- Ordinary definitions retain both actual annotation calls and their real
prefix/cache states. Nat-operation pin routes are separate, not silently
included in this branch's statement or excluded from the source domain. -/
def DefinitionInstalled (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (hint : Kernel.ReducibilityHint) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
    ∃ type annotated : Kernel.Expr,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      Kernel.ConstantInfo.defnInfo { header with type := type } annotated hint ∈ env.consts

theorem definition_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false)
    (run : annotStepC mode pins index fe pending (.defnDecl header value hint) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode fe header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      fe'.env.consts = .defnInfo { header with type := type } annotated hint :: fe.env.consts := by
  unfold annotStepC at run
  simp only [ordinary, Bool.false_eq_true, ↓reduceIte] at run
  obtain ⟨triple, _, valueRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type, annotated⟩ := triple
  obtain ⟨rfl, afterType, beforeValue, afterValue, typeRun, headerRun, annotation⟩ :=
    prepared_value_fields valueRun
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
  exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, rfl⟩

theorem definition_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint}
    (ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false)
    (present : Declaration.defnDecl header value hint ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    DefinitionInstalled mode header value hint finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, installed⟩ :=
        definition_step ordinary stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, afterType, beforeValue, afterValue, type, annotated,
        typeRun, headerRun, valueRun, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem definition_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false)
    (present : Declaration.defnDecl header value hint ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    DefinitionInstalled mode header value hint env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact definition_run ordinary (Array.mem_toList_iff.mpr present) run rfl

open Kernel.SetTheory in
theorem DefinitionInstalled.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalled mode header value hint env)
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
      ∃ type annotated : Kernel.Expr, ∃ semanticType : V,
        (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
        annotConstantValC mode before header initial.flushed =
          .ok (({ header with type := type }, type), beforeValue) ∧
        (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
        Kernel.Denotes strong.public.cval env levels ρ type semanticType ∧
        strong.public.cval header.name levels ∈ˢ semanticType ∧
        Kernel.Denotes strong.public.cval env levels ρ annotated (strong.public.cval header.name levels) := by
  obtain ⟨before, initial, afterType, beforeValue, afterValue, type, annotated,
    typeRun, headerRun, valueRun, present⟩ := receipt
  obtain ⟨semanticType, typeRead, member⟩ := strong.public.mem _ present levels ρ
  exact ⟨before, initial, afterType, beforeValue, afterValue, type, annotated, semanticType,
    typeRun, headerRun, valueRun, typeRead, member,
    strong.definition_values _ _ _ present levels ρ⟩

/-- Opaque body annotation/checking is retained as provenance, while its
installed semantic entry is an axiom. No transparent value equation follows. -/
def OpaqueInstalled (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
    ∃ type annotated : Kernel.Expr,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      Kernel.ConstantInfo.axiomInfo { header with type := type } ∈ env.consts

theorem opaque_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (ordinary : reduceOpNames.contains header.name = false)
    (run : annotStepC mode pins index fe pending (.opaqueDecl header value) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode fe header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      fe'.env.consts = .axiomInfo { header with type := type } :: fe.env.consts := by
  unfold annotStepC at run
  simp only [ordinary, Bool.false_eq_true, ↓reduceIte] at run
  obtain ⟨triple, _, valueRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type, annotated⟩ := triple
  obtain ⟨rfl, afterType, beforeValue, afterValue, typeRun, headerRun, annotation⟩ :=
    prepared_value_fields valueRun
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
  exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, rfl⟩

theorem opaque_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (ordinary : reduceOpNames.contains header.name = false)
    (present : Declaration.opaqueDecl header value ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    OpaqueInstalled mode header value finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, installed⟩ :=
        opaque_step ordinary stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, afterType, beforeValue, afterValue, type, annotated,
        typeRun, headerRun, valueRun, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem opaque_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (ordinary : reduceOpNames.contains header.name = false)
    (present : Declaration.opaqueDecl header value ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    OpaqueInstalled mode header value env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact opaque_run ordinary (Array.mem_toList_iff.mpr present) run rfl

/-- Both real header routes, with the branch's exact final state retained.
The disjunction distinguishes install-only annotation from primitive checking;
it does not assert their caches or operational behavior coincide. -/
def ValueAnnotationCalls (mode : CheckMode) (before : FEnv) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (initial : CState) (type annotated : Kernel.Expr) : Prop :=
  ∃ afterType beforeValue afterValue : CState,
    (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
    (annotConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∨
      checkConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue)) ∧
    (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue)

/-- Let checking at the actual value-annotation state. Both the ordinary
header-annotation branch and the primitive header-check branch preserve the
required invariant; their states are not identified with each other. -/
theorem ValueAnnotationCalls.let_trace {mode : CheckMode} {env : Env}
    {header : Kernel.ConstantVal} {type value body annotatedType annotatedValue : Kernel.Expr}
    {initial : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env) (state : CSOKF initial)
    (scope : Kernel.Expr.WScoped 0 (.letE type value body))
    (calls : ValueAnnotationCalls mode (mkFEnv env) header (.letE type value body)
      initial annotatedType annotatedValue) :
    LetAnnotation mode env 0 type value body annotatedValue := by
  obtain ⟨afterType, beforeValue, afterValue, _, headerRun, valueRun⟩ := calls
  have valueState : CSOK mode env beforeValue := by
    rcases headerRun with install | check
    · exact (annotConstantValC_run verified environment (flushC_csok state) install).1
    · exact (checkConstantValC_sim verified environment (flushC_csok state) rfl
        _ beforeValue check).1
  exact (let_cached verified environment valueState scope valueRun).2.2

def DefinitionInstalledAll (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (hint : Kernel.ReducibilityHint) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.defnInfo { header with type := type } annotated hint ∈ env.consts

def OpaqueInstalledAll (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.axiomInfo { header with type := type } ∈ env.consts

theorem definition_all_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (run : annotStepC mode pins index fe pending (.defnDecl header value hint) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated, ValueAnnotationCalls mode fe header value initial type annotated ∧
      fe'.env.consts = .defnInfo { header with type := type } annotated hint :: fe.env.consts := by
  by_cases ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false
  · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, stored⟩ :=
      definition_step ordinary run
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inl headerRun, valueRun⟩, stored⟩
  · have pinned : (natOpNames.contains header.name || natDivModNames.contains header.name) = true := by
      cases h : (natOpNames.contains header.name || natDivModNames.contains header.name) <;> simp_all
    unfold annotStepC at run
    simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, checkedRun, run⟩ := bindC_ok run
    obtain ⟨result, _⟩ := pureC_ok run
    obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
    unfold checkDeclStepC at checkedRun
    obtain ⟨_, afterFlush, flush, checkedRun⟩ := bindC_ok checkedRun
    rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
    have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
    subst flushed
    obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, rfl⟩ :=
      checked_definition_decl checkedRun
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inr headerRun, valueRun⟩, rfl⟩

theorem opaque_all_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (run : annotStepC mode pins index fe pending (.opaqueDecl header value) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated, ValueAnnotationCalls mode fe header value initial type annotated ∧
      fe'.env.consts = .axiomInfo { header with type := type } :: fe.env.consts := by
  by_cases ordinary : reduceOpNames.contains header.name = false
  · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, stored⟩ :=
      opaque_step ordinary run
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inl headerRun, valueRun⟩, stored⟩
  · have pinned : reduceOpNames.contains header.name = true := by
      cases h : reduceOpNames.contains header.name <;> simp_all
    unfold annotStepC at run
    simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, checkedRun, run⟩ := bindC_ok run
    obtain ⟨result, _⟩ := pureC_ok run
    obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
    unfold checkDeclStepC at checkedRun
    obtain ⟨_, afterFlush, flush, checkedRun⟩ := bindC_ok checkedRun
    rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
    have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
    subst flushed
    obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, rfl⟩ :=
      checked_opaque_decl checkedRun
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inr headerRun, valueRun⟩, rfl⟩

theorem definition_all_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    DefinitionInstalledAll mode header value hint finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, calls, installed⟩ := definition_all_step stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, type, annotated, calls, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

/-- Full definition provenance with the actual prefix's environment and
fresh-state invariants. These come from the accepting fold's model walk,
including its pending checks, rather than from the final target environment. -/
def DefinitionCheckedPrefix (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (hint : Kernel.ReducibilityHint) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    before = mkFEnv before.env ∧ EnvWF before.env ∧ CSOKF initial ∧
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.defnInfo { header with type := type } annotated hint ∈ env.consts

/-- The actual installation boundary of any declaration kind, including
mutual/inductive blocks. Both prefix states, canonical indices and the full
extension to the final environment are retained. This is operational
provenance; kind-specific annotation and semantic laws remain separate. -/
def CheckedDeclarationPrefix (mode : CheckMode) (pins : List NatOpPinSet)
    (declaration : Declaration) (env : Env) : Prop :=
  ∃ index, ∃ before : FEnv, ∃ pending : Array PendingCheck, ∃ initial : CState,
    ∃ next : FEnv, ∃ nextPending : Array PendingCheck, ∃ after : CState,
      before = mkFEnv before.env ∧ EnvWF before.env ∧ CSOKF initial ∧
      annotStepC mode pins index before pending declaration initial = .ok ((next, nextPending), after) ∧
      next = mkFEnv next.env ∧ EnvWF next.env ∧ CSOKF after ∧
      PushChain next.env (mkFEnv env)

theorem declaration_prefix_run {V : Type u} [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : List Declaration} {declaration : Declaration}
    (present : declaration ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env)
    (model : Kernel.Model.EnvModelOk V mode start.2.1.env) (state : CSOKF initial)
    (unique : NodupNames finish.2.1.env)
    (checked : ∀ pc ∈ finish.2.2.toList, ∃ after, checkPending mode finish.2.1 pc {} = .ok ((), after)) :
    CheckedDeclarationPrefix mode pins declaration finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons current rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 current
        initial (nextEnv, nextPending) afterStep stepRun).1
    obtain ⟨tailChain, newPending, pending⟩ :=
      installRun_trace mode restRun (PushChain.self chain.canon)
    obtain ⟨nextModel, nextState, _⟩ :=
      annotStepC_model verified canonical chain.canon model state stepRun tailChain pending unique checked
    rcases List.mem_cons.mp present with rfl | restPresent
    · have beforeWF : EnvWF start.2.1.env := by
        obtain ⟨witness⟩ := model.1
        exact witness.toEnvFacts.wf
      have nextWF : EnvWF nextEnv.env := by
        obtain ⟨witness⟩ := nextModel.1
        exact witness.toEnvFacts.wf
      refine ⟨start.1, start.2.1, start.2.2, initial, nextEnv, nextPending, afterStep,
        canonical, beforeWF, state, stepRun, chain.canon, nextWF, nextState, ?_⟩
      rw [← tailChain.canon]
      exact tailChain
    · exact ih restPresent chain.canon nextModel nextState unique checked

/-- Every actual input declaration receives the boundary above from the
same accepting fold. No restriction to singleton definition/theorem records
is used in this provenance theorem. -/
theorem declaration_prefix_checked (V : Type u) [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : Array Declaration} {env : Env} {declaration : Declaration}
    (present : declaration ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    CheckedDeclarationPrefix mode pins declaration env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  have chain := installRun_trace mode run (PushChain.refl Env.empty)
  exact declaration_prefix_run (V := V) verified (Array.mem_toList_iff.mpr present) run rfl
    ⟨⟨Kernel.Model.EnvModelM.empty V mode⟩, Kernel.EtaFamiliesClosed.empty⟩
    CSOKF.empty (chain.1.2.2 List.nodup_nil) fullyChecked.records

theorem CheckedDeclarationPrefix.definition {mode : CheckMode} {pins : List NatOpPinSet}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint} {env : Env}
    (receipt : CheckedDeclarationPrefix mode pins (.defnDecl header value hint) env) :
    DefinitionCheckedPrefix mode header value hint env := by
  obtain ⟨_, before, _, initial, _, _, _, canonical, environment, state, step, _, _, _, chain⟩ := receipt
  obtain ⟨type, annotated, calls, stored⟩ := definition_all_step step
  refine ⟨before, initial, type, annotated, canonical, environment, state, calls, ?_⟩
  obtain ⟨new, extension⟩ := chain.2.1
  change env.consts = _ at extension
  rw [extension]
  exact List.mem_append_right _ (stored ▸ List.mem_cons_self)

/-- An opaque body is checked and annotated at its actual prefix, but its
stored semantic entry is an axiom. This records no equation between the
opaque value and its checking body. -/
def OpaqueCheckedPrefix (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    before = mkFEnv before.env ∧ EnvWF before.env ∧ CSOKF initial ∧
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.axiomInfo { header with type := type } ∈ env.consts

theorem CheckedDeclarationPrefix.opaque_value {mode : CheckMode} {pins : List NatOpPinSet}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {env : Env}
    (receipt : CheckedDeclarationPrefix mode pins (.opaqueDecl header value) env) :
    OpaqueCheckedPrefix mode header value env := by
  obtain ⟨_, before, _, initial, _, _, _, canonical, environment, state, step, _, _, _, chain⟩ := receipt
  obtain ⟨type, annotated, calls, stored⟩ := opaque_all_step step
  refine ⟨before, initial, type, annotated, canonical, environment, state, calls, ?_⟩
  obtain ⟨new, extension⟩ := chain.2.1
  change env.consts = _ at extension
  rw [extension]
  exact List.mem_append_right _ (stored ▸ List.mem_cons_self)

theorem definition_prefix_run {V : Type u} [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env)
    (model : Kernel.Model.EnvModelOk V mode start.2.1.env) (state : CSOKF initial)
    (unique : NodupNames finish.2.1.env)
    (checked : ∀ pc ∈ finish.2.2.toList, ∃ after, checkPending mode finish.2.1 pc {} = .ok ((), after)) :
    DefinitionCheckedPrefix mode header value hint finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    obtain ⟨tailChain, newPending, pending⟩ :=
      installRun_trace mode restRun (PushChain.self chain.canon)
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, calls, installed⟩ := definition_all_step stepRun
      have beforeWF : EnvWF start.2.1.env := by
        obtain ⟨witness⟩ := model.1
        exact witness.toEnvFacts.wf
      refine ⟨start.2.1, initial, type, annotated, canonical, beforeWF, state, calls, ?_⟩
      obtain ⟨_, ⟨new, extension⟩, _⟩ := tailChain
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · obtain ⟨nextModel, nextState, _⟩ :=
        annotStepC_model verified canonical chain.canon model state stepRun tailChain pending unique checked
      exact ih restPresent chain.canon nextModel nextState unique checked

theorem definition_prefix_checked (V : Type u) [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    DefinitionCheckedPrefix mode header value hint env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  have chain := installRun_trace mode run (PushChain.refl Env.empty)
  exact definition_prefix_run (V := V) verified (Array.mem_toList_iff.mpr present) run rfl
    ⟨⟨Kernel.Model.EnvModelM.empty V mode⟩, Kernel.EtaFamiliesClosed.empty⟩
    CSOKF.empty (chain.1.2.2 List.nodup_nil) fullyChecked.records

/-- An admitted let-bodied definition supplies the actual prefix and
annotation-state evidence needed by the let bridge. Only raw input scope
remains a separate source-export obligation here. -/
theorem DefinitionCheckedPrefix.let_trace {mode : CheckMode}
    {header : Kernel.ConstantVal} {type value body : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} {env : Env}
    (verified : mode.verifiedChecks = true)
    (receipt : DefinitionCheckedPrefix mode header (.letE type value body) hint env)
    (scope : Kernel.Expr.WScoped 0 (.letE type value body)) :
    ∃ priorEnv : Env, ∃ initial : CState, ∃ annotatedType annotatedValue : Kernel.Expr,
      EnvWF priorEnv ∧ CSOKF initial ∧
      ValueAnnotationCalls mode (mkFEnv priorEnv) header (.letE type value body)
        initial annotatedType annotatedValue ∧
      LetAnnotation mode priorEnv 0 type value body annotatedValue ∧
      Kernel.ConstantInfo.defnInfo { header with type := annotatedType } annotatedValue hint ∈ env.consts := by
  obtain ⟨before, initial, annotatedType, annotatedValue, canonical, environment, state, calls, present⟩ := receipt
  have actual : ValueAnnotationCalls mode (mkFEnv before.env) header (.letE type value body)
      initial annotatedType annotatedValue := canonical ▸ calls
  exact ⟨before.env, initial, annotatedType, annotatedValue, environment, state, actual,
    actual.let_trace verified environment state scope, present⟩

theorem opaque_all_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.opaqueDecl header value ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    OpaqueInstalledAll mode header value finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, calls, installed⟩ := opaque_all_step stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, type, annotated, calls, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem definition_all_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    DefinitionInstalledAll mode header value hint env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact definition_all_run (Array.mem_toList_iff.mpr present) run rfl

theorem opaque_all_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.opaqueDecl header value ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    OpaqueInstalledAll mode header value env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact opaque_all_run (Array.mem_toList_iff.mpr present) run rfl

/-- Actual checked folds have unique stored names, including the complete
ordinary, primitive and block installation paths. -/
theorem checked_unique_names {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env}
    (checked : checkDecls mode pins declarations = .ok env) : NodupNames env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  have chain := (installRun_trace mode run (PushChain.refl Env.empty)).1
  exact chain.2.2 (by simp [NodupNames, Env.empty])

theorem unique_member {constants : List Kernel.ConstantInfo}
    (unique : (constants.map Kernel.ConstantInfo.name).Nodup)
    {first second : Kernel.ConstantInfo}
    (firstPresent : first ∈ constants) (secondPresent : second ∈ constants)
    (names : first.name = second.name) : first = second := by
  induction constants with
  | nil => exact absurd firstPresent List.not_mem_nil
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp firstPresent with rfl | firstRest
    · rcases List.mem_cons.mp secondPresent with rfl | secondRest
      · rfl
      · exact False.elim (parts.1 (names ▸ List.mem_map.mpr ⟨second, secondRest, rfl⟩))
    · rcases List.mem_cons.mp secondPresent with rfl | secondRest
      · exact False.elim (parts.1 (names ▸ List.mem_map.mpr ⟨first, firstRest, rfl⟩))
      · exact ih parts.2 firstRest secondRest

theorem DefinitionInstalled.exact {mode : CheckMode} {header installedHeader : Kernel.ConstantVal}
    {value installedValue : Kernel.Expr} {hint installedHint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalled mode header value hint env) (unique : NodupNames env)
    (lookup : env.find? header.name = some (.defnInfo installedHeader installedValue installedHint)) :
    installedHeader = { header with type := installedHeader.type } ∧ installedHint = hint ∧
    ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed =
        .ok (installedHeader.type, afterType) ∧
      annotConstantValC mode before header initial.flushed =
        .ok ((installedHeader, installedHeader.type), beforeValue) ∧
      (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (installedValue, afterValue) := by
  obtain ⟨before, initial, afterType, beforeValue, afterValue, type, annotated,
    typeRun, headerRun, valueRun, present⟩ := receipt
  have same := unique_member unique present (Kernel.Semantics.Env.find?_mem lookup)
    (by simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal] using
      (Kernel.Semantics.Env.find?_name lookup).symm)
  cases same
  exact ⟨rfl, rfl, before, initial, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun⟩

theorem DefinitionInstalledAll.exact {mode : CheckMode} {header installedHeader : Kernel.ConstantVal}
    {value installedValue : Kernel.Expr} {hint installedHint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalledAll mode header value hint env) (unique : NodupNames env)
    (lookup : env.find? header.name = some (.defnInfo installedHeader installedValue installedHint)) :
    installedHeader = { header with type := installedHeader.type } ∧ installedHint = hint ∧
    ∃ before : FEnv, ∃ initial : CState,
      ValueAnnotationCalls mode before header value initial installedHeader.type installedValue := by
  obtain ⟨before, initial, type, annotated, calls, present⟩ := receipt
  have same := unique_member unique present (Kernel.Semantics.Env.find?_mem lookup)
    (by simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal] using
      (Kernel.Semantics.Env.find?_name lookup).symm)
  cases same
  exact ⟨rfl, rfl, before, initial, calls⟩

open Kernel.SetTheory in
theorem DefinitionInstalledAll.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalledAll mode header value hint env)
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr, ∃ semanticType : V,
      ValueAnnotationCalls mode before header value initial type annotated ∧
      Kernel.Denotes strong.public.cval env levels ρ type semanticType ∧
      strong.public.cval header.name levels ∈ˢ semanticType ∧
      Kernel.Denotes strong.public.cval env levels ρ annotated (strong.public.cval header.name levels) := by
  obtain ⟨before, initial, type, annotated, calls, present⟩ := receipt
  obtain ⟨semanticType, typeRead, member⟩ := strong.public.mem _ present levels ρ
  exact ⟨before, initial, type, annotated, semanticType, calls, typeRead, member,
    strong.definition_values _ _ _ present levels ρ⟩

open Kernel.SetTheory in
theorem OpaqueInstalledAll.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr} {env : Env}
    (receipt : OpaqueInstalledAll mode header value env)
    (model : Kernel.Model V env) (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr, ∃ semanticType : V,
      ValueAnnotationCalls mode before header value initial type annotated ∧
      Kernel.Denotes model.cval env levels ρ type semanticType ∧
      model.cval header.name levels ∈ˢ semanticType := by
  obtain ⟨before, initial, type, annotated, calls, present⟩ := receipt
  obtain ⟨semanticType, typeRead, member⟩ := model.mem _ present levels ρ
  exact ⟨before, initial, type, annotated, semanticType, calls, typeRead, member⟩

/-- The full theorem header, not merely its name/kind skeleton, survives
to the final environment. The prefix and annotation state are from its
actual installation step; the raw theorem proof remains opaque. -/
def TheoremInstalled (mode : CheckMode) (header : Kernel.ConstantVal) (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial afterAnnotation : CState, ∃ annotated : Kernel.Expr,
    (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed =
      .ok (annotated, afterAnnotation) ∧
    Kernel.ConstantInfo.thmInfo { header with type := annotated } value ∈ env.consts

theorem theorem_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.thmDecl header value ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    TheoremInstalled mode header value finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨annotated, afterAnnotation, annotation, installed⟩ := theorem_step stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, afterAnnotation, annotated, annotation, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem theorem_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.thmDecl header value ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    TheoremInstalled mode header value env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact theorem_run (Array.mem_toList_iff.mpr present) run rfl

open Kernel.SetTheory in
/-- Read the theorem through its actual installed type, retaining the
annotation call that produced that type. This does not read the raw input
type as though its binder regimes and lets had already been repaired. -/
theorem TheoremInstalled.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr} {env : Env}
    (receipt : TheoremInstalled mode header value env) (model : Kernel.Model V env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial afterAnnotation : CState, ∃ annotated : Kernel.Expr, ∃ type : V,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed =
        .ok (annotated, afterAnnotation) ∧
      Kernel.Denotes model.cval env levels ρ annotated type ∧
      model.cval header.name levels ∈ˢ type := by
  obtain ⟨before, initial, afterAnnotation, annotated, annotation, present⟩ := receipt
  obtain ⟨type, denoted, member⟩ := model.mem _ present levels ρ
  exact ⟨before, initial, afterAnnotation, annotated, type, annotation, denoted, member⟩

end AnnotationTrace

end Ix.CompileCert
