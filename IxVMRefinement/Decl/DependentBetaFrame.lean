import IxVMRefinement.Decl.ConstructorFramePair
import IxVMRefinement.Decl.NativeSortDomain
import IxVMRefinement.Decl.SortFunctionConversion

/-! # A checked local frame transport for dependent beta

The beta body returns its parameter, so the result depends on an earlier variable rather than
on a fixed constant. The actual application check supplies the argument comparison. A kind
origin for the earlier variable is transported through the same constructor rebuild, and the
final variable is checked in its own frame. No equality of frame interpretations or generic
conversion transitivity is used.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

/-- Inference of the identity beta redex retains its actual argument check and comparison. -/
theorem infer_identity_application {md : Mode} {env : Env md} {depth : Nat} {domainSort : Level}
    {argument inferred : Expr md} {metadata : BinderMeta}
    (typed : Rules.Infer env .full depth (.app (.lam (.sort domainSort) (.bvar 0) metadata) argument) inferred) :
    inferred = .sort domainSort ∧ ∃ argumentType,
      Rules.Infer env .full depth argument argumentType ∧
      Rules.DefEq env depth argumentType (.sort domainSort) := by
  obtain ⟨functionType, expectedDomain, resultBody, functionMeta, argumentType,
    functionTyped, functionReduced, argumentTyped, compared, result⟩ := Rules.Infer.app_inv typed
  cases functionTyped with
  | lam _ _ bodyTyped _ _ _ _ =>
    simp only [Expr.instantiate1, ↓reduceIte] at bodyTyped
    have bodyType := Rules.Infer.fvar_inv bodyTyped
    rw [bodyType] at functionReduced
    simp only [Expr.abstract1] at functionReduced
    obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid functionReduced rfl)
    exact ⟨by simpa only [Expr.instantiate1] using result, argumentType, argumentTyped, compared⟩

/-- A pair of actual variable entries whose type expressions share a computational kind origin.
This is stronger than merely pairing two checked frames and weaker than equating their types. -/
structure SortKindPair (env : Env .anon) (fuel index : Nat) (original final : Expr .anon) (kind : Level) : Prop
    extends TypedFVarPair env fuel index original final where
  originalKind : SortFunction kind 0 original.fvarTypeD
  finalKind : SortFunction kind 0 final.fvarTypeD

/-- The local kind relation is produced from the actual frame pair and the same normalization;
its final origin is derived, not supplied by the caller. -/
theorem sortKindPair_of_rebuild {env : Env .anon} {fuel nP nF slot : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon} {kind : Level}
    (frames : CheckedFramePair env fuel (nP + nF) originalVars finalVars)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original) (finalAt : finalVars[nP + slot]? = some final)
    (origin : SortFunction kind 0 original.fvarTypeD) : SortKindPair env fuel (nP + slot) original final kind where
  toTypedFVarPair := frames.entry originalAt finalAt
  originalKind := origin
  finalKind := normCtorVal_sortFunction_domain normalized originalOpen finalOpen originalAt finalAt origin

/-- The argument comparison from the original beta check pins the universe. The final
variable's own inference and sort check then give the same zero-ness despite its changed type. -/
theorem SortKindPair.identity_to_variable {env : Env .anon} {fuel index depth : Nat}
    {original final inputType outputType : Expr .anon} {kind domainSort inputSort outputSort : Level}
    {metadata : BinderMeta} (pair : SortKindPair env fuel index original final kind)
    (beforeTyped : Rules.Infer env .full depth
      (.app (.lam (.sort domainSort) (.bvar 0) metadata) original) inputType)
    (beforeSorted : Rules.Red env depth inputType (.sort inputSort))
    (afterTyped : Rules.Infer env .full depth final outputType)
    (afterSorted : Rules.Red env depth outputType (.sort outputSort)) :
    Rules.Infer env .full depth original original.fvarTypeD ∧
      Rules.DefEq env depth original.fvarTypeD (.sort domainSort) ∧
      Level.zeronessOf inputSort = Level.zeronessOf outputSort := by
  obtain ⟨inputTypeEq, argumentType, argumentTyped, compared⟩ := infer_identity_application beforeTyped
  have argumentTypeEq : argumentType = original.fvarTypeD := by
    rw [pair.originalIndex] at argumentTyped
    exact Rules.Infer.fvar_inv argumentTyped
  rw [argumentTypeEq] at argumentTyped compared
  have outputTypeEq : outputType = final.fvarTypeD := by
    rw [pair.finalIndex] at afterTyped
    exact Rules.Infer.fvar_inv afterTyped
  rw [inputTypeEq] at beforeSorted
  rw [outputTypeEq] at afterSorted
  have inputSortEq := Rules.Red.sort_eq beforeSorted
  have outputSortEq := (pair.finalKind.reduced afterSorted).sort_level
  have zero := sort_function_zero (.symm compared) pair.originalKind
  refine ⟨argumentTyped, compared, ?_⟩
  rw [inputSortEq, ← outputSortEq]
  exact zero

/-- Both use-site checks are extracted from the recorded paired constructor frames. The local
case identifies an identity beta before normalization and the corresponding variable after it. -/
theorem CheckedFramePair.identity_to_variable {env : Env .anon} {fuel count useSlot index : Nat}
    {originalVars finalVars : List (Expr .anon)} (frames : CheckedFramePair env fuel count originalVars finalVars)
    {original final oldUse newUse : Expr .anon} {kind domainSort : Level} {metadata : BinderMeta}
    (pair : SortKindPair env fuel index original final kind)
    (oldUseAt : originalVars[useSlot]? = some oldUse) (newUseAt : finalVars[useSlot]? = some newUse)
    (oldShape : oldUse.fvarTypeD = .app (.lam (.sort domainSort) (.bvar 0) metadata) original)
    (newShape : newUse.fvarTypeD = final) :
    ∃ inputType inputSort outputType outputSort,
      inferTypeCore .verified env fuel useSlot oldUse.fvarTypeD = .ok inputType ∧
      ensureSortCore .verified env fuel useSlot inputType = .ok inputSort ∧
      inferTypeCore .verified env fuel useSlot newUse.fvarTypeD = .ok outputType ∧
      ensureSortCore .verified env fuel useSlot outputType = .ok outputSort ∧
      Rules.DefEq env useSlot original.fvarTypeD (.sort domainSort) ∧
      Level.zeronessOf inputSort = Level.zeronessOf outputSort := by
  obtain ⟨inputType, inputSort, inputTyped, inputSorted⟩ := frames.original.domainChecks useSlot oldUse oldUseAt
  obtain ⟨outputType, outputSort, outputTyped, outputSorted⟩ := frames.final.domainChecks useSlot newUse newUseAt
  obtain ⟨_, compared, equal⟩ := pair.identity_to_variable
    (Rules.inferTypeCore_bridge (by simpa only [oldShape] using inputTyped))
    (Rules.whnf_bridge (ensureSortCore_inv inputSorted))
    (Rules.inferTypeCore_bridge (by simpa only [newShape] using outputTyped))
    (Rules.whnf_bridge (ensureSortCore_inv outputSorted))
  exact ⟨inputType, inputSort, outputType, outputSort, inputTyped, inputSorted,
    outputTyped, outputSorted, compared, equal⟩

end IxVM.Refinement.Decl
