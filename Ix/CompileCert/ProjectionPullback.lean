import Ix.CompileCert.SourceProjection

/-! # Projection laws through the pull-back

Source projection equations and functions transferred through an installed
pull-back to the checked target (`checked_constant_eq`,
`InstalledEquationFrame`).
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-- Transfer an actual source constant's specialized equation through its
checked installed type. Both endpoint grading and equality come from the
actual target constant; no equality with an independently chosen source
model is assumed. The target residual's exact pinned-Eq shape is an explicit
finite check, separate from type comparison and from original-source D11. -/
theorem checked_constant_eq {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (sourceConstant targetConstant : Kernel.ConstantInfo)
    (sourcePresent : sourceConstant ∈ sourceEnv.consts)
    (targetLookup : targetEnv.find? (names sourceConstant.name) = some targetConstant)
    (levels : Kernel.Name → Nat) {ρ finalρ : Nat → V} {arguments : List V}
    {sourceLevel targetLevel : Kernel.Level} {sourceCarrier sourceLeft sourceRight : Kernel.Expr}
    {targetCarrier targetLeft targetRight : Kernel.Expr} {leftValue rightValue : V}
    {binders : List (Kernel.Expr × Kernel.BinderMeta)}
    (typed : InstalledTelescope ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv levels ρ sourceConstant.toConstantVal.type arguments finalρ
      (.app (.app (.app (.const Kernel.eqName [sourceLevel]) sourceCarrier) sourceLeft) sourceRight))
    (targetShape : targetConstant.toConstantVal.type.stripPis arguments.length = some (binders,
      .app (.app (.app (.const Kernel.eqName [targetLevel]) targetCarrier) targetLeft) targetRight))
    (leftRead : Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv levels finalρ sourceLeft leftValue)
    (rightRead : Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv levels finalρ sourceRight rightValue) : leftValue = rightValue := by
  obtain ⟨sourceLookup, found, foundLookup, comparison⟩ := checkInstalledTypes_member types sourcePresent
  have same : found = targetConstant := Option.some.inj (foundLookup.symm.trans targetLookup)
  subst found
  have image := checkInstalledMemberExpr_sound target association sourceLookup comparison levels
  obtain ⟨result, targetTyped, residualImage⟩ := typed.image image
  have resultShape := targetTyped.result_of_stripPis targetShape
  subst result
  cases residualImage with
  | app prefixImage rightImage =>
    cases prefixImage with
    | app head leftImage =>
      have present := Kernel.Semantics.Env.find?_mem targetLookup
      have graded := target.graded_telescope targetConstant present targetTyped
      obtain ⟨type, reading, member⟩ := targetTyped.model_apply target.public present
      exact target.graded_public_eq_sound graded reading member
        (leftImage.denotes leftRead) (rightImage.denotes rightRead)

open Kernel.SetTheory in
/-- Source-owned projection computation at the target-derived source values.
The actual source equation is associated with a target installed constant;
its checked type and target grading supply the equality. This does not use
the independently installed source model's choice of values. -/
theorem SourceProjectionInstalled.constructor_computation_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation coverage.env targetEnv names)
    (types : checkInstalledTypes coverage.env targetEnv names = true)
    (model : Kernel.Model V coverage.env)
    (values : model.cval = (PullbackMap.fromEnvs coverage.env targetEnv names).values target.public.cval)
    (targetEquation : Kernel.ConstantInfo)
    (targetLookup : targetEnv.find? (names receipt.data.equation.name) = some targetEquation)
    {targetLevel : Kernel.Level} {targetCarrier targetLeft targetRight : Kernel.Expr}
    {binders : List (Kernel.Expr × Kernel.BinderMeta)}
    (targetShape : targetEquation.toConstantVal.type.stripPis
      (projection.site.owner.numParams + projection.site.ctor.numFields) = some (binders,
        .app (.app (.app (.const Kernel.eqName [targetLevel]) targetCarrier) targetLeft) targetRight))
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (fields : SourceFieldValues projection.site V)
    (valid : SourceCoverValidFields constructor model levels ρ parameters fields) :
    app (parameters.foldl app (model.cval projection.header.name levels))
      (originalConstructorValue projection.site model.cval levels parameters fields) =
        originalSelectedField projection.site fields := by
  have typed := receipt.typed_equation model levels ρ parameters parameterCount parameterTyping fields valid
  have leftRead := receipt.left_denotes model levels ρ parameters parameterCount fields
  have rightRead := receipt.right_denotes model levels ρ parameters fields
  rw [values] at typed leftRead rightRead ⊢
  exact checked_constant_eq target association types (.thmInfo receipt.data.equation receipt.data.proof)
    targetEquation (Kernel.Semantics.Env.find?_mem receipt.equationLookup) targetLookup levels typed
    (by simpa only [List.length_append, parameterCount, fields.property] using targetShape) leftRead rightRead

open Kernel.SetTheory in
/-- Arbitrary-member extensional projection correspondence in the pulled-back
source model. Coverage remains source-owned, and computation now comes from
the target's actual checked equation association. Target certificate/support
presence and the exact pinned-Eq residual remain explicit, finite obligations. -/
theorem SourceProjectionInstalled.arbitrary_value_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation coverage.env targetEnv names)
    (types : checkInstalledTypes coverage.env targetEnv names = true)
    (model : Kernel.Model V coverage.env)
    (values : model.cval = (PullbackMap.fromEnvs coverage.env targetEnv names).values target.public.cval)
    (targetEquation : Kernel.ConstantInfo)
    (targetLookup : targetEnv.find? (names receipt.data.equation.name) = some targetEquation)
    {targetLevel : Kernel.Level} {targetCarrier targetLeft targetRight : Kernel.Expr}
    {binders : List (Kernel.Expr × Kernel.BinderMeta)}
    (targetShape : targetEquation.toConstantVal.type.stripPis
      (projection.site.owner.numParams + projection.site.ctor.numFields) = some (binders,
        .app (.app (.app (.const Kernel.eqName [targetLevel]) targetCarrier) targetLeft) targetRight))
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName projection.site.ownerName) levels)) :
    OriginalProjectionValue projection.site model.cval levels parameters
      (SourceCoverValidFields constructor model levels ρ parameters) subject
      (app (parameters.foldl app (model.cval projection.header.name levels)) subject) ∧
    ∀ value, OriginalProjectionValue projection.site model.cval levels parameters
      (SourceCoverValidFields constructor model levels ρ parameters) subject value →
      value = app (parameters.foldl app (model.cval projection.header.name levels)) subject :=
  original_projection_extensional projection.site model.cval levels parameters
    (SourceCoverValidFields constructor model levels ρ parameters)
    (parameters.foldl app (model.cval (sourceName projection.site.ownerName) levels))
    (parameters.foldl app (model.cval projection.header.name levels))
    (constructor.semantic_cover model levels ρ parameters parameterCount parameterTyping)
    (receipt.constructor_computation_pullback target association types model values targetEquation
      targetLookup targetShape levels ρ parameters parameterCount parameterTyping)
    subject subjectTyped

/-- Exact installed equation endpoint. Declaration kind is retained in the
constant, although equality follows from checked type membership for any
actual constant. This grants no transparent body equation to opaque rows. -/
structure InstalledEquationFrame (env : Kernel.Env) (name : Kernel.Name) (arity : Nat) where
  constant : Kernel.ConstantInfo
  binders : List (Kernel.Expr × Kernel.BinderMeta)
  level : Kernel.Level
  carrier : Kernel.Expr
  left : Kernel.Expr
  right : Kernel.Expr
  lookup : env.find? name = some constant
  shape : constant.toConstantVal.type.stripPis arity = some (binders,
    .app (.app (.app (.const Kernel.eqName [level]) carrier) left) right)

/-- Read the exact requested target identity and exact argument count. No
reverse alias scan, display-name fabrication, or alternate Eq head is used. -/
def readInstalledEquationFrame (env : Kernel.Env) (name : Kernel.Name) (arity : Nat) :
    Option (InstalledEquationFrame env name arity) := do
  let some constant := env.find? name | none
  let some (binders, .app (.app (.app (.const _ [level]) carrier) left) right) :=
      constant.toConstantVal.type.stripPis arity | none
  if lookup : env.find? name = some constant then
    if shape : constant.toConstantVal.type.stripPis arity = some (binders,
        .app (.app (.app (.const Kernel.eqName [level]) carrier) left) right) then
      some ⟨constant, binders, level, carrier, left, right, lookup, shape⟩
    else none
  else none

open Kernel.SetTheory in
/-- Executable target endpoint receipt supplies all target identity/shape
premises of arbitrary source projection correspondence. The source-owned
coverage/equation receipts and full installed association remain separate. -/
theorem SourceProjectionInstalled.arbitrary_value_checkedTarget {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation coverage.env targetEnv names)
    (types : checkInstalledTypes coverage.env targetEnv names = true)
    (model : Kernel.Model V coverage.env)
    (values : model.cval = (PullbackMap.fromEnvs coverage.env targetEnv names).values target.public.cval)
    (frame : InstalledEquationFrame targetEnv (names receipt.data.equation.name)
      (projection.site.owner.numParams + projection.site.ctor.numFields))
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName projection.site.ownerName) levels)) :
    OriginalProjectionValue projection.site model.cval levels parameters
      (SourceCoverValidFields constructor model levels ρ parameters) subject
      (app (parameters.foldl app (model.cval projection.header.name levels)) subject) ∧
    ∀ value, OriginalProjectionValue projection.site model.cval levels parameters
      (SourceCoverValidFields constructor model levels ρ parameters) subject value →
      value = app (parameters.foldl app (model.cval projection.header.name levels)) subject :=
  receipt.arbitrary_value_pullback target association types model values frame.constant frame.lookup
    frame.shape levels ρ parameters parameterCount parameterTyping subject subjectTyped

open Kernel.SetTheory in
/-- Full source projection function value at pulled-back values. The actual
installed binder regime is retained; its agreement with original or target
annotation traces is a separate D11 obligation. -/
theorem SourceProjectionFunction.value_eq_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation coverage.env targetEnv names)
    (types : checkInstalledTypes coverage.env targetEnv names = true)
    (model : Kernel.Model V coverage.env)
    (values : model.cval = (PullbackMap.fromEnvs coverage.env targetEnv names).values target.public.cval)
    (frame : InstalledEquationFrame targetEnv (names receipt.data.equation.name)
      (projection.site.owner.numParams + projection.site.ctor.numFields))
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level)) :
    parameters.foldl app (model.cval projection.header.name levels) =
      Kernel.SetModel.lamR (Kernel.regime levels function.data.binder.pw)
        (parameters.foldl app (model.cval (sourceName projection.site.ownerName) levels))
        (originalProjectionSelection projection.site model.cval levels parameters
          (SourceCoverValidFields constructor model levels ρ parameters)) := by
  obtain ⟨codomain, typed, _⟩ := function.typed model levels ρ parameters parameterCount parameterTyping
  rw [← Kernel.SetModel.lamR_eta typed]
  apply Kernel.SetModel.lamR_congr
  intro subject subjectTyped
  have presented := constructor.constructor_presentation model levels ρ parameters
    parameterCount parameterTyping subject subjectTyped
  have selected := originalProjectionSelection_reading projection.site model.cval levels
    parameters (SourceCoverValidFields constructor model levels ρ parameters) subject presented
  exact ((receipt.arbitrary_value_checkedTarget target association types model values frame levels ρ
    parameters parameterCount parameterTyping subject subjectTyped).2 _ selected).symm

/-- The actual normalized annotated body denotes the original-field selector
at the target-derived source values. Transparent definition evidence comes
from the checked public value model; opaque/theorem checking bodies are not
silently promoted to unfolding equations. -/
theorem SourceProjectionFunction.body_application_denotes_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation coverage.env targetEnv names)
    (types : checkInstalledTypes coverage.env targetEnv names = true)
    (model : PublicValueModel V coverage.env)
    (values : model.model.cval = (PullbackMap.fromEnvs coverage.env targetEnv names).values target.public.cval)
    (frame : InstalledEquationFrame targetEnv (names receipt.data.equation.name)
      (projection.site.owner.numParams + projection.site.ctor.numFields))
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (expressions : List Kernel.Expr)
    (parameterRead : DenotesSpine model.model.cval coverage.env levels ρ expressions parameters) :
    Kernel.Denotes model.model.cval coverage.env levels ρ
      (Kernel.Expr.mkAppN receipt.data.value expressions)
      (Kernel.SetModel.lamR (Kernel.regime levels function.data.binder.pw)
        (parameters.foldl Kernel.SetTheory.app (model.model.cval (sourceName projection.site.ownerName) levels))
        (originalProjectionSelection projection.site model.model.cval levels parameters
          (SourceCoverValidFields constructor model.model levels ρ parameters))) := by
  have definition := model.definitions receipt.data.projection receipt.data.value receipt.data.hint
    (Kernel.Semantics.Env.find?_mem receipt.projectionLookup) levels ρ
  have projectionName := receipt.shape.2.2.2.2.2.1
  rw [projectionName] at definition
  have read := denotes_mkAppN definition parameterRead
  rw [function.value_eq_pullback target association types model.model values frame levels ρ
    parameters parameterCount parameterTyping] at read
  exact read

end Ix.CompileCert
