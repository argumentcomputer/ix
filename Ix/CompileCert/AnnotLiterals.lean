import Ix.CompileCert.AnnotSyntax

/-! Literal capability and pinned-leaf assembly for annotated transport.
The support flags are checked separately from name/telescope correspondence:
an unsupported literal reading cannot be silently made supported by a map. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics Kernel.Verify

def checkLiteralSupport (source target : Kernel.Env) : Bool :=
  decide (Kernel.natLitSupported source = Kernel.natLitSupported target ∧
    Kernel.strLitSupported source = Kernel.strLitSupported target)

theorem checkInstalledPins_annotated {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {pins : List (Kernel.Name × List Kernel.Level)}
    (checked : checkInstalledPins sourceEnv names image pins = some true) :
    ∀ pin ∈ pins, ∀ d, AnnotatedImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
      (.const pin.1 pin.2) (.const pin.1 pin.2) := by
  induction pins with
  | nil => simp
  | cons pin rest ih =>
    obtain ⟨first, remaining⟩ := bothChecks_true checked
    intro selected member d
    rcases List.mem_cons.mp member with rfl | member
    · exact checkInstalledConstant_annotated target association image targetLevels first d
    · exact ih remaining selected member d

theorem AnnotatedImage.constant_leaf {sa ta se te sl tl d sn tn sus tus}
    (image : AnnotatedImage sa ta se te sl tl d (.const sn sus) (.const tn tus)) :
    sa sn (Kernel.Level.substFn sl (levelParamsAt se sn) sus) =
      ta tn (Kernel.Level.substFn tl (levelParamsAt te tn) tus) := by
  cases image with
  | constant sourceLookup targetLookup _ _ leaf =>
    simpa only [levelParamsAt, sourceLookup, targetLookup] using leaf

private theorem substFn_empty (levels : Kernel.Name → Nat) (params : List Kernel.Name) :
    Kernel.Level.substFn levels params [] = levels := by
  cases params <;> rfl

theorem checked_natural_annotations {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    (n : Nat) (checked : checkInstalledPins sourceEnv names image naturalImagePins = some true)
    (d : Nat) :
    AnnotatedImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
      (.lit (.natVal n)) (.lit (.natVal n)) := by
  have flags := of_decide_eq_true support
  have pins := checkInstalledPins_annotated target association image targetLevels checked
  apply AnnotatedImage.natLit flags.1
  · have zero := (pins (Kernel.natZeroName, []) (by simp [naturalImagePins]) d).constant_leaf
    simpa only [substFn_empty] using zero
  · have succ := (pins (Kernel.natSuccName, []) (by simp [naturalImagePins]) d).constant_leaf
    simpa only [substFn_empty] using succ

theorem checked_string_annotations {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    (s : String) (checked : checkInstalledPins sourceEnv names image stringImagePins = some true)
    (d : Nat) :
    AnnotatedImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
      (.lit (.strVal s)) (.lit (.strVal s)) := by
  have flags := of_decide_eq_true support
  have pins := checkInstalledPins_annotated target association image targetLevels checked
  apply AnnotatedImage.strLit flags.2
  · intro name member
    have selected : (name, []) ∈ stringImagePins := by
      simpa [stringImagePins, naturalImagePins] using member
    have leaf := (pins (name, []) selected d).constant_leaf
    simpa only [substFn_empty] using leaf
  · exact (pins (Kernel.listNilName, [.zero]) (by simp [stringImagePins]) d).constant_leaf
  · exact (pins (Kernel.listConsName, [.zero]) (by simp [stringImagePins]) d).constant_leaf

/-- Whole-expression executable checks now establish actual annotated reading
equality, with both literal suppliers and binder opening discharged. The
additional support comparison is explicit, not inferred from public values. -/
theorem checkInstalledExpr_annotated {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    {sourceExpr targetExpr : Kernel.Expr}
    (checked : checkInstalledExpr sourceEnv targetEnv names image sourceExpr targetExpr = some true)
    (d : Nat) :
    AnnotatedImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels d
      sourceExpr targetExpr := by
  exact (checkInstalledExpr_annotatedSyntax target association image targetLevels
    (checked_natural_annotations target association image targetLevels support)
    (checked_string_annotations target association image targetLevels support) checked).opened d

end Ix.CompileCert
