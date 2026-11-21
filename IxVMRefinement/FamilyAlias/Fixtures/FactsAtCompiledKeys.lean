import IxVMRefinement.FamilyAlias.FactsCheck
import IxVMRefinement.FamilyAlias.Fixtures.NestedTreeCompiled
import IxVMRefinement.FamilyAlias.Fixtures.IndexedPairCompiled

/-! # The family check's facts at two families' compiled records

`FamilyCheckFacts` (`FamilyAlias/Facts.lean`) holds of the nested tree and of the indexed mutual
pair at their compiled keys: the family as IxC's reader reads the compiled block and recursor
records, the advice the compiled advice records give, and the environment IxC's fold stores for
the pinned basis, the container's record and the advice records (`pre` of the two fixtures).

Each is proved by evaluating the search `familyFactsCheck` in the kernel. So each stored-data
field is decided on the fixture's data, and each judgement is a derivation the rules bridge
gives from a run of IxC's executable checker at positions. What is not proved here is that the
fixture's data are what the records store: that was executed (the suite `ixvm-family-records`
writes the records, and the fixtures were generated from its output). -/

namespace IxVM.Refinement.Decl.FamilyAlias.Fixtures

open IxVM.Refinement.Core
open Ix.Kernel (Env)

set_option maxRecDepth 100000

namespace NestedTreeCompiled

/-- The family's advice, read off its alias table. -/
def advice : FamilyAdvice := FamilyAdvice.ofTable tbl blk

set_option maxHeartbeats 40000000 in
/-- The search for the family check's facts succeeds (evaluated). -/
theorem facts_ok :
    isOk (familyFactsCheck 200 ⟨pre⟩ blk advice (tysM ++ tysR) rhsss) = true := by
  decide +kernel

/-- **The family check's facts hold of the nested tree at its compiled keys.** -/
theorem facts : FamilyCheckFacts ⟨pre⟩ blk advice (tysM ++ tysR) rhsss :=
  familyFacts_of_check facts_ok

end NestedTreeCompiled

namespace IndexedPairCompiled

/-- The family's advice, read off its alias table. -/
def advice : FamilyAdvice := FamilyAdvice.ofTable tbl blk

set_option maxHeartbeats 40000000 in
/-- The search for the family check's facts succeeds (evaluated). -/
theorem facts_ok :
    isOk (familyFactsCheck 200 ⟨pre⟩ blk advice (tysM ++ tysR) rhsss) = true := by
  decide +kernel

/-- **The family check's facts hold of the indexed mutual pair at its compiled keys.** -/
theorem facts : FamilyCheckFacts ⟨pre⟩ blk advice (tysM ++ tysR) rhsss :=
  familyFacts_of_check facts_ok

end IndexedPairCompiled

end IxVM.Refinement.Decl.FamilyAlias.Fixtures
