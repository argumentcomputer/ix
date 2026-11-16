import IxVMRefinement.Decl.SortTailTransport
import IxVMRefinement.Decl.NamedAliasTail
import IxVMRefinement.Decl.DomainTransport

/-! # An exact rebuilt-domain case with invariant inferred sort

An opened field in the sort-returning fragment remains in that fragment through the actual
normalizer, telescope closing, reannotation, and reopening. Earlier fields may acquire different
annotations: closure under arbitrary substitution handles their effect on this fragment.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

/-- A selected original field retains the sort-returning fragment through the exact rebuild
and its actual final annotation, even when earlier free-variable annotations change. -/
theorem normCtorVal_sortFunction_domain {env : Env .anon} {fuel nP nF slot : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon} {sortLevel : Level}
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original)
    (finalAt : finalVars[nP + slot]? = some final)
    (shape : SortFunction sortLevel 0 original.fvarTypeD) : SortFunction sortLevel 0 final.fvarTypeD :=
  normCtorVal_domain_predicate (P := SortFunction sortLevel 0)
    (fun _ index cut h => h.abstract1 index cut) (fun _ value cut h => h.instantiate1 value cut)
    (fun h ann => h.annotated ann) (fun h run => h.normalized run)
    normalized originalOpen finalOpen originalAt finalAt shape

/-- Product telescopes ending in the fragment retain their shape through the same exact trace. -/
theorem normCtorVal_sortTail_domain {env : Env .anon} {fuel nP nF slot count : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon} {sortLevel : Level}
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original)
    (finalAt : finalVars[nP + slot]? = some final)
    (shape : SortTail sortLevel count original.fvarTypeD) : SortTail sortLevel count final.fvarTypeD :=
  normCtorVal_domain_predicate (P := SortTail sortLevel count)
    (fun _ index cut h => h.abstract1 index cut) (fun _ value cut h => h.instantiate1 value cut)
    (fun h ann => h.annotated ann) (fun h run => h.normalized run)
    normalized originalOpen finalOpen originalAt finalAt shape

/-- The actual named-alias tail is preserved through the same complete rebuild and annotation. -/
theorem normCtorVal_aliasTail_domain {env : Env .anon} {fuel nP nF slot count : Nat}
    {T aliasName targetName : Key .anon} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal .anon} {hint : ReducibilityHint} {caps : IndCaps .anon}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon}
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original)
    (finalAt : finalVars[nP + slot]? = some final)
    (shape : AliasTail aliasName targetName targetLevels count original.fvarTypeD) :
    AliasTail aliasName targetName targetLevels count final.fvarTypeD :=
  normCtorVal_domain_predicate (P := AliasTail aliasName targetName targetLevels count)
    (fun _ index cut h => h.abstract1 index cut) (fun _ value cut h => h.instantiate1 value cut)
    (fun h ann => h.annotated ann) (fun h run => h.normalized aliasFound noLevels targetFound run)
    normalized originalOpen finalOpen originalAt finalAt shape

end IxVM.Refinement.Decl
