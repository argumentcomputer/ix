import IxVMRefinement.FamilyAlias.FactsCheck
import IxVMRefinement.FamilyAlias.Fixtures.NestedTree
import IxVMRefinement.FamilyAlias.Fixtures.IndexedPair
import IxVMRefinement.FamilyAlias.Fixtures.NestedTreeUniv
import IxVMRefinement.FamilyAlias.Fixtures.LargePair

/-! # The family check's facts at four families in the advice layout

`FamilyCheckFacts` (`FamilyAlias/Facts.lean`) holds of the four families whose fixtures are at
placeholder keys, with the environment in the advice layout of IxCK's in-process model
(`FamilyAlias/AdviceLayout.lean`). These are not stored records: they show the facts at shapes
the two compiled families do not have, a nested family with a parameter (pins that mention the
parameter, recursors at a real permutation of the positions) and a pair of large eliminators.

Each is proved by evaluating the search `familyFactsCheck` in the kernel. -/

namespace IxVM.Refinement.Decl.FamilyAlias.Fixtures

open IxVM.Refinement.Core
open Ix.Kernel (Env)

set_option maxRecDepth 100000

namespace NestedTree

/-- The family's advice, read off its alias table. -/
def advice : FamilyAdvice := FamilyAdvice.ofTable tbl blk

set_option maxHeartbeats 40000000 in
/-- The search for the family check's facts succeeds (evaluated). -/
theorem facts_ok :
    isOk (familyFactsCheck 200 ⟨pre⟩ blk advice (tysM ++ tysR) rhsss) = true := by
  decide +kernel

/-- **The family check's facts hold of this family in the advice layout.** -/
theorem facts : FamilyCheckFacts ⟨pre⟩ blk advice (tysM ++ tysR) rhsss :=
  familyFacts_of_check facts_ok

end NestedTree

namespace IndexedPair

/-- The family's advice, read off its alias table. -/
def advice : FamilyAdvice := FamilyAdvice.ofTable tbl blk

set_option maxHeartbeats 40000000 in
/-- The search for the family check's facts succeeds (evaluated). -/
theorem facts_ok :
    isOk (familyFactsCheck 200 ⟨pre⟩ blk advice (tysM ++ tysR) rhsss) = true := by
  decide +kernel

/-- **The family check's facts hold of this family in the advice layout.** -/
theorem facts : FamilyCheckFacts ⟨pre⟩ blk advice (tysM ++ tysR) rhsss :=
  familyFacts_of_check facts_ok

end IndexedPair

namespace NestedTreeUniv

/-- The family's advice, read off its alias table. -/
def advice : FamilyAdvice := FamilyAdvice.ofTable tbl blk

set_option maxHeartbeats 40000000 in
/-- The search for the family check's facts succeeds (evaluated). -/
theorem facts_ok :
    isOk (familyFactsCheck 200 ⟨pre⟩ blk advice (tysM ++ tysR) rhsss) = true := by
  decide +kernel

/-- **The family check's facts hold of this family in the advice layout.** -/
theorem facts : FamilyCheckFacts ⟨pre⟩ blk advice (tysM ++ tysR) rhsss :=
  familyFacts_of_check facts_ok

end NestedTreeUniv

namespace LargePair

/-- The family's advice, read off its alias table. -/
def advice : FamilyAdvice := FamilyAdvice.ofTable tbl blk

set_option maxHeartbeats 40000000 in
/-- The search for the family check's facts succeeds (evaluated). -/
theorem facts_ok :
    isOk (familyFactsCheck 200 ⟨pre⟩ blk advice (tysM ++ tysR) rhsss) = true := by
  decide +kernel

/-- **The family check's facts hold of this family in the advice layout.** -/
theorem facts : FamilyCheckFacts ⟨pre⟩ blk advice (tysM ++ tysR) rhsss :=
  familyFacts_of_check facts_ok

end LargePair

end IxVM.Refinement.Decl.FamilyAlias.Fixtures
