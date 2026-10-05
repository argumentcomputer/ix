import Ix.CompileCert.AnnotPullback

/-! Structural annotation correspondence before binder opening. A leaf must
be stable under term-variable instantiation; arbitrary public-value equality
cannot introduce a leaf. Opening preserves the relation, so the checker can
compare binder bodies before the semantic reader opens them. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

inductive AnnotatedSyntax
    (sa ta : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm)
    (se te : Kernel.Env) (sl tl : Kernel.Name → Nat) : Kernel.Expr → Kernel.Expr → Prop
  | bvar (i) : AnnotatedSyntax sa ta se te sl tl (.bvar i) (.bvar i)
  | leaf {s t} (reading : ∀ d, AnnotatedImage sa ta se te sl tl d s t)
      (sourceStable : ∀ v k, s.instantiate1 v k = s)
      (targetStable : ∀ v k, t.instantiate1 v k = t) : AnnotatedSyntax sa ta se te sl tl s t
  | app {sf sx tf tx} (function : AnnotatedSyntax sa ta se te sl tl sf tf)
      (argument : AnnotatedSyntax sa ta se te sl tl sx tx) :
      AnnotatedSyntax sa ta se te sl tl (.app sf sx) (.app tf tx)
  | lam {sd sb sm td tb tm} (domain : AnnotatedSyntax sa ta se te sl tl sd td)
      (body : AnnotatedSyntax sa ta se te sl tl sb tb)
      (bits : pwBit sl sm.pw = pwBit tl tm.pw) :
      AnnotatedSyntax sa ta se te sl tl (.lam sd sb sm) (.lam td tb tm)
  | forallE {sd sb sm td tb tm} (domain : AnnotatedSyntax sa ta se te sl tl sd td)
      (body : AnnotatedSyntax sa ta se te sl tl sb tb)
      (bits : pwBit sl sm.pw = pwBit tl tm.pw) :
      AnnotatedSyntax sa ta se te sl tl (.forallE sd sb sm) (.forallE td tb tm)
  | projection {sn si sx tn ti tx} (operand : AnnotatedSyntax sa ta se te sl tl sx tx)
      (position : ∀ d s t, AnnotatedImage sa ta se te sl tl d s t →
        AnnotatedImage sa ta se te sl tl d (.proj sn si s) (.proj tn ti t)) :
      AnnotatedSyntax sa ta se te sl tl (.proj sn si sx) (.proj tn ti tx)

theorem AnnotatedSyntax.fvar {sa ta se te sl tl} (i : Nat) (st tt : Kernel.Expr) :
    AnnotatedSyntax sa ta se te sl tl (.fvar i st) (.fvar i tt) :=
  .leaf (fun _ => .fvar) (by intros; rfl) (by intros; rfl)

/-- Opening uses the kernel's actual instantiation, including its unchanged
free-variable type metadata and incremented depth under both binder forms. -/
theorem AnnotatedSyntax.instantiate1 {sa ta se te sl tl s t sv tv}
    (image : AnnotatedSyntax sa ta se te sl tl s t)
    (value : AnnotatedSyntax sa ta se te sl tl sv tv) (k : Nat) :
    AnnotatedSyntax sa ta se te sl tl (s.instantiate1 sv k) (t.instantiate1 tv k) := by
  induction image generalizing k with
  | bvar i =>
    simp only [Kernel.Expr.instantiate1]
    split
    · exact value
    · split <;> exact .bvar _
  | leaf reading sourceStable targetStable =>
    rw [sourceStable, targetStable]
    exact .leaf reading sourceStable targetStable
  | app _ _ ihf iha => exact .app (ihf k) (iha k)
  | lam _ _ bits ihd ihb => exact .lam (ihd k) (ihb (k + 1)) bits
  | forallE _ _ bits ihd ihb => exact .forallE (ihd k) (ihb (k + 1)) bits
  | projection _ position ih => exact .projection (ih k) position

/-- Raw structural comparison is sufficient at every reader depth, because
the binder-opening step was proved rather than assumed in the caller. -/
theorem AnnotatedSyntax.opened {sa ta se te sl tl s t}
    (image : AnnotatedSyntax sa ta se te sl tl s t) (d : Nat) :
    AnnotatedImage sa ta se te sl tl d s t := by
  cases image with
  | bvar i => exact .bvar
  | leaf reading _ _ => exact reading d
  | app f a => exact .app (f.opened d) (a.opened d)
  | @lam sd sb sm td tb tm domain body bits =>
    exact .lam (domain.opened d)
      ((body.instantiate1 (.fvar d sd td) 0).opened (d + 1)) bits
  | @forallE sd sb sm td tb tm domain body bits =>
    exact .forallE (domain.opened d)
      ((body.instantiate1 (.fvar d sd td) 0).opened (d + 1)) bits
  | projection operand position => exact position d _ _ (operand.opened d)
termination_by s.sizeB
decreasing_by
  all_goals first
  | (simp only [Kernel.Expr.sizeB]; omega)
  | (rw [Kernel.Expr.sizeB_instantiate1 _ rfl]; simp only [Kernel.Expr.sizeB]; omega)

/-- Existing executable structural comparisons supply the raw relation.
Literal interpretation requires its separate capability/pinned-leaf bridge;
the two premises below expose exactly that remaining part, not a restriction
of the source domain. All binder-opening obligations are discharged here. -/
theorem checkInstalledExpr_annotatedSyntax {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (natural : ∀ n, checkInstalledPins sourceEnv names image naturalImagePins = some true →
      ∀ d, AnnotatedImage
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations targetModel.internal.base2.acval)
        targetModel.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
        (.lit (.natVal n)) (.lit (.natVal n)))
    (string : ∀ s, checkInstalledPins sourceEnv names image stringImagePins = some true →
      ∀ d, AnnotatedImage
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations targetModel.internal.base2.acval)
        targetModel.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
        (.lit (.strVal s)) (.lit (.strVal s)))
    {source target : Kernel.Expr}
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
      exact .app (ihF functionCheck) (ihA argumentCheck)
  | lam domain body metadata ihD ihB =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case lam targetDomain targetBody targetMetadata =>
      obtain ⟨datumCheck, rest⟩ := bothChecks_true checked
      obtain ⟨domainCheck, bodyCheck⟩ := bothChecks_true rest
      have datum := of_decide_eq_true (Option.some.inj datumCheck)
      apply AnnotatedSyntax.lam (ihD domainCheck) (ihB bodyCheck)
      rw [datum]
      exact (image.regime targetLevels metadata).symm
  | forallE domain body metadata ihD ihB =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case forallE targetDomain targetBody targetMetadata =>
      obtain ⟨datumCheck, rest⟩ := bothChecks_true checked
      obtain ⟨domainCheck, bodyCheck⟩ := bothChecks_true rest
      have datum := of_decide_eq_true (Option.some.inj datumCheck)
      apply AnnotatedSyntax.forallE (ihD domainCheck) (ihB bodyCheck)
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
          exact .leaf (natural value pins) (by intros; rfl) (by intros; rfl)
    | strVal value =>
      cases target <;> try simp only [checkInstalledExpr] at checked <;> try contradiction
      case lit targetLiteral =>
        cases targetLiteral <;> simp only [checkInstalledExpr] at checked <;> try contradiction
        case strVal other =>
          obtain ⟨same, pins⟩ := bothChecks_true checked
          have equal := of_decide_eq_true (Option.some.inj same)
          subst other
          exact .leaf (string value pins) (by intros; rfl) (by intros; rfl)
  | proj owner field operand ih =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case proj targetOwner targetField targetOperand =>
      obtain ⟨position, operandCheck⟩ := bothChecks_true checked
      exact .projection (ih operandCheck)
        (fun _ _ _ mapped => checkInstalledProjection_annotated (Option.some.inj position) mapped)

end Ix.CompileCert
