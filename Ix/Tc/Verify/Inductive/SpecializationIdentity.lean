import Ix.Tc.Verify.Inductive.OccurrenceValidation

/-!
# Nested-inductive specialization identity

The positivity recursion stack and flat-block construction must agree on the
identity of an auxiliary.  Semantic universe equality and term DefEq are
intentionally broader than this identity: syntactically distinct applications
receive distinct generated auxiliaries even when they denote equal types.
-/

namespace Ix.Tc

/-- Exact flat-block identity represented by a nested positivity group and a
concrete application. -/
def PositivityFlatIdentity (group : PositivityGroup m) (family : Address)
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (nParams : Nat) : Prop :=
  group.params.size = nParams ∧
    (group.nestedSpecializationKey? family ==
      some (nestedApplicationSpecializationKey family us args nParams)) = true

namespace RecM

/-- The production positivity-stack match is exactly equality of the same key
used by flat-block auxiliary deduplication. -/
theorem positivityGroupMatches_eq_true_iff
    (group : PositivityGroup m) (family : Address)
    (us : Array (KUniv m)) (args : Array (KExpr m)) (nParams : Nat) :
    positivityGroupMatches group family us args nParams = true ↔
      PositivityFlatIdentity group family us args nParams := by
  simp [positivityGroupMatches, PositivityFlatIdentity, Bool.and_eq_true]

end RecM

namespace SpecializationIdentityFixture

private def family : Address := default
private def leftParam : KUniv .anon := .mkParam 0 ()
private def rightParam : KUniv .anon := .mkParam 1 ()
private def leftUniverse : KUniv .anon := .mkMax leftParam rightParam
private def rightUniverse : KUniv .anon := .mkMax rightParam leftParam
private def group : PositivityGroup .anon :=
  { addrs := #[family], params := #[], concreteUs := some #[leftUniverse] }

private theorem semanticUniverseEquality_does_not_collapse_specializationNative :
    univEq leftUniverse rightUniverse = true ∧
      (NestedSpecializationKey.ofApplication family #[leftUniverse] #[] ==
        NestedSpecializationKey.ofApplication family #[rightUniverse] #[]) =
          false ∧
      RecM.positivityGroupMatches group family #[rightUniverse] #[] 0 =
        false := by
  native_decide

/-- Adversarial boundary: commuted maxima are semantically equal universes,
but they are distinct auxiliary specializations and must not close the same
positivity-stack edge. -/
theorem semanticUniverseEquality_does_not_collapse_specialization :
    univEq leftUniverse rightUniverse = true ∧
      (NestedSpecializationKey.ofApplication family #[leftUniverse] #[] ==
        NestedSpecializationKey.ofApplication family #[rightUniverse] #[]) =
          false ∧
      RecM.positivityGroupMatches group family #[rightUniverse] #[] 0 =
        false :=
  semanticUniverseEquality_does_not_collapse_specializationNative

end SpecializationIdentityFixture

end Ix.Tc
