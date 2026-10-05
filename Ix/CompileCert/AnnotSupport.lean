import Ix.CompileCert.AnnotModel

/-! Literal-support checks follow occurrences in the expression being related.
An unrelated target capability cannot reject a literal-free source field.
The earlier global guard is retained only as a sufficient lemma. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics Kernel.Verify

def checkExprLiteralSupport (source target : Kernel.Env) : Kernel.Expr → Bool
  | .lit (.natVal _) => decide (Kernel.natLitSupported source = Kernel.natLitSupported target)
  | .lit (.strVal _) => decide (Kernel.strLitSupported source = Kernel.strLitSupported target)
  | .app f a => checkExprLiteralSupport source target f && checkExprLiteralSupport source target a
  | .lam domain body _ | .forallE domain body _ =>
      checkExprLiteralSupport source target domain && checkExprLiteralSupport source target body
  | .proj _ _ value => checkExprLiteralSupport source target value
  | .bvar _ | .fvar .. | .sort _ | .const .. | .letE .. => true

private theorem support_pair {first second : Bool} (checked : (first && second) = true) :
    first = true ∧ second = true := by
  simpa only [Bool.and_eq_true] using checked

private theorem substFn_empty (levels : Kernel.Name → Nat) (params : List Kernel.Name) :
    Kernel.Level.substFn levels params [] = levels := by
  cases params <;> rfl

theorem checked_natural_annotations_of_flag {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (support : Kernel.natLitSupported sourceEnv = Kernel.natLitSupported targetEnv)
    (n : Nat) (checked : checkInstalledPins sourceEnv names image naturalImagePins = some true)
    (d : Nat) :
    AnnotatedImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
      (.lit (.natVal n)) (.lit (.natVal n)) := by
  have pins := checkInstalledPins_annotated target association image targetLevels checked
  apply AnnotatedImage.natLit support
  · have zero := (pins (Kernel.natZeroName, []) (by simp [naturalImagePins]) d).constant_leaf
    simpa only [substFn_empty] using zero
  · have succ := (pins (Kernel.natSuccName, []) (by simp [naturalImagePins]) d).constant_leaf
    simpa only [substFn_empty] using succ

theorem checked_string_annotations_of_flag {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (support : Kernel.strLitSupported sourceEnv = Kernel.strLitSupported targetEnv)
    (s : String) (checked : checkInstalledPins sourceEnv names image stringImagePins = some true)
    (d : Nat) :
    AnnotatedImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
      (.lit (.strVal s)) (.lit (.strVal s)) := by
  have pins := checkInstalledPins_annotated target association image targetLevels checked
  apply AnnotatedImage.strLit support
  · intro name member
    have selected : (name, []) ∈ stringImagePins := by
      simpa [stringImagePins, naturalImagePins] using member
    have leaf := (pins (name, []) selected d).constant_leaf
    simpa only [substFn_empty] using leaf
  · exact (pins (Kernel.listNilName, [.zero]) (by simp [stringImagePins]) d).constant_leaf
  · exact (pins (Kernel.listConsName, [.zero]) (by simp [stringImagePins]) d).constant_leaf

theorem checkInstalledExpr_annotatedSyntax_local {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {source target : Kernel.Expr}
    (support : checkExprLiteralSupport sourceEnv targetEnv source = true)
    (checked : checkInstalledExpr sourceEnv targetEnv names image source target = some true) :
    AnnotatedSyntax
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations targetModel.internal.base2.acval)
      targetModel.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels
      source target := by
  induction source generalizing target with
  | bvar index =>
    cases target <;> simp [checkInstalledExpr] at checked
    case bvar other => subst other; exact .bvar index
  | fvar index type ih => cases target <;> simp [checkInstalledExpr] at checked
  | sort level =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case sort targetLevel =>
      exact .leaf (fun _ => .sort ((image.eval targetLevels level).symm.trans
        (Kernel.Level.isEquiv_sound checked targetLevels))) (by intros; rfl) (by intros; rfl)
  | const name levels =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case const targetName targetUs =>
      exact .leaf (checkInstalledConstant_annotated targetModel association image targetLevels checked)
        (by intros; rfl) (by intros; rfl)
  | app function argument ihF ihA =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case app targetFunction targetArgument =>
      obtain ⟨functionCheck, argumentCheck⟩ := bothChecks_true checked
      have guards := support_pair support
      exact .app (ihF guards.1 functionCheck) (ihA guards.2 argumentCheck)
  | lam domain body metadata ihD ihB =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case lam targetDomain targetBody targetMetadata =>
      obtain ⟨datumCheck, rest⟩ := bothChecks_true checked
      obtain ⟨domainCheck, bodyCheck⟩ := bothChecks_true rest
      have datum := of_decide_eq_true (Option.some.inj datumCheck)
      apply AnnotatedSyntax.lam (ihD (support_pair support).1 domainCheck) (ihB (support_pair support).2 bodyCheck)
      rw [datum]
      exact (image.regime targetLevels metadata).symm
  | forallE domain body metadata ihD ihB =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case forallE targetDomain targetBody targetMetadata =>
      obtain ⟨datumCheck, rest⟩ := bothChecks_true checked
      obtain ⟨domainCheck, bodyCheck⟩ := bothChecks_true rest
      have datum := of_decide_eq_true (Option.some.inj datumCheck)
      apply AnnotatedSyntax.forallE (ihD (support_pair support).1 domainCheck) (ihB (support_pair support).2 bodyCheck)
      rw [datum]
      exact (image.regime targetLevels metadata).symm
  | letE type value body ihT ihV ihB => cases target <;> simp [checkInstalledExpr] at checked
  | lit literal =>
    cases literal with
    | natVal value =>
      cases target <;> try simp only [checkInstalledExpr] at checked <;> try contradiction
      case lit targetLiteral =>
        cases targetLiteral <;> simp only [checkInstalledExpr] at checked <;> try contradiction
        case natVal other =>
          obtain ⟨same, pins⟩ := bothChecks_true checked
          have equal := of_decide_eq_true (Option.some.inj same)
          subst other
          exact .leaf (checked_natural_annotations_of_flag targetModel association image targetLevels
            (of_decide_eq_true support) value pins) (by intros; rfl) (by intros; rfl)
    | strVal value =>
      cases target <;> try simp only [checkInstalledExpr] at checked <;> try contradiction
      case lit targetLiteral =>
        cases targetLiteral <;> simp only [checkInstalledExpr] at checked <;> try contradiction
        case strVal other =>
          obtain ⟨same, pins⟩ := bothChecks_true checked
          have equal := of_decide_eq_true (Option.some.inj same)
          subst other
          exact .leaf (checked_string_annotations_of_flag targetModel association image targetLevels
            (of_decide_eq_true support) value pins) (by intros; rfl) (by intros; rfl)
  | proj owner field operand ih =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case proj targetOwner targetField targetOperand =>
      obtain ⟨position, operandCheck⟩ := bothChecks_true checked
      exact .projection (ih support operandCheck)
        (fun _ _ _ mapped => checkInstalledProjection_annotated (Option.some.inj position) mapped)


def checkTypeLiteralSupport (source target : Kernel.Env) : Bool :=
  source.consts.all fun entry => checkExprLiteralSupport source target entry.toConstantVal.type

def checkDefinitionLiteralSupport (source target : Kernel.Env) : Bool :=
  source.consts.all fun entry => match entry with
    | .defnInfo _ value _ => checkExprLiteralSupport source target value
    | _ => true

theorem checkInstalledMemberExpr_annotated_reading_local {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some sourceEntry)
    {source target : Kernel.Expr}
    (support : checkExprLiteralSupport sourceEnv targetEnv source = true)
    (checked : checkInstalledMemberExpr sourceEnv targetEnv names name source target = some true)
    (sourceLevels : Kernel.Name → Nat) (depth : Nat) :
    denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations targetModel.internal.base2.acval)
      sourceEnv sourceLevels depth source =
    denoteMeta targetModel.internal.base2.acval targetEnv
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name sourceLevels) depth target := by
  obtain ⟨targetEntry, targetLookup, sourceUnique, targetUnique, sameArity⟩ :=
    association name sourceEntry lookup
  simp only [checkInstalledMemberExpr, lookup, targetLookup] at checked
  split at checked
  next bounded =>
    have image := (checkInstalledExpr_annotatedSyntax_local targetModel association _
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name sourceLevels) support checked).opened depth
    refine (denoteMeta_params_at ?_ ?_ depth source bounded).trans image.reading
    · intro constant info present first second agree
      exact PullbackMap.annotations_params targetModel association present first second agree
    · intro parameter present
      simp only [PullbackMap.fromEnvs, lookup, targetLookup]
      exact (UniverseImage.telescope_recovery sourceLevels sourceUnique targetUnique sameArity parameter present).symm
  next => contradiction

open Kernel.SetTheory in
/-- The actual all-row type check establishes the three strong-model type
fields under target-derived annotations, at every original source valuation.
There is no per-member annotation-image or source-model premise. -/
theorem checkInstalledTypes_annotated_local {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (support : checkTypeLiteralSupport sourceEnv targetEnv = true)
    (checked : checkInstalledTypes sourceEnv targetEnv names = true)
    (sourceEntry : Kernel.ConstantInfo) (present : sourceEntry ∈ sourceEnv.consts)
    (levels : Kernel.Name → Nat) :
    ∃ annotation,
      denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
        sourceEnv levels 0 sourceEntry.toConstantVal.type = some annotation ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ annotation) ∧
      (∀ ρ : Nat → V, interp V ρ
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval
          sourceEntry.name levels) ∈ˢ interp V ρ annotation) := by
  obtain ⟨sourceLookup, targetEntry, targetLookup, comparison⟩ := checkInstalledTypes_member checked present
  have member := Kernel.Semantics.Env.find?_mem targetLookup
  obtain ⟨annotation, reading⟩ := target.internal.type_reads targetEntry member
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels sourceEntry.name levels)
  have transferred := checkInstalledMemberExpr_annotated_reading_local target association
    sourceLookup (List.all_eq_true.mp support sourceEntry present) comparison levels 0
  refine ⟨annotation, transferred.trans reading,
    target.internal.type_wellDenotedV targetEntry member _ annotation reading, ?_⟩
  intro ρ
  have membership := target.internal.mem_type targetEntry member _ annotation reading ρ
  have targetName := Kernel.Semantics.Env.find?_name targetLookup
  simpa only [PullbackMap.annotations, PullbackMap.fromEnvs, targetName] using membership

/-- The checked actual definition-body association supplies the source
`AcvalDefnInst` equation under the same pulled annotation carrier. This is
only for installed definitions; opaque/theorem checking bodies do not become
transparent value equations. -/
theorem checkInstalledDefinitions_annotated_local {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (support : checkDefinitionLiteralSupport sourceEnv targetEnv = true)
    (checked : checkInstalledDefinitions sourceEnv targetEnv names = true)
    (levels : Kernel.Name → Nat) (header : Kernel.ConstantVal) (value : Kernel.Expr)
    (present : ∃ hint : Kernel.ReducibilityHint,
      Kernel.ConstantInfo.defnInfo header value hint ∈ sourceEnv.consts) :
    denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      sourceEnv levels 0 value =
    some ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval
      header.name levels) := by
  obtain ⟨hint, member⟩ := present
  obtain ⟨sourceLookup, targetHeader, targetValue, targetHint, targetLookup, comparison⟩ :=
    checkInstalledDefinitions_member checked member
  have reading := target.internal.defn_reads
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels)
    targetHeader targetValue ⟨targetHint, Kernel.Semantics.Env.find?_mem targetLookup⟩
  have transferred := checkInstalledMemberExpr_annotated_reading_local target association
    sourceLookup (List.all_eq_true.mp support (.defnInfo header value hint) member) comparison levels 0
  have targetName := Kernel.Semantics.Env.find?_name targetLookup
  simpa only [Kernel.ConstantInfo.name, PullbackMap.annotations, PullbackMap.fromEnvs] using
    transferred.trans (reading.trans (congrArg some (congrArg
      (fun name => target.internal.base2.acval name
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels)) targetName)))


end Ix.CompileCert
