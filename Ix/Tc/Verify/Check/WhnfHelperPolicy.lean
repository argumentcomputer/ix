import Ix.Tc.Verify.Check.WhnfIotaDispatchPolicy

/-!
# Concrete operational policy for every WHNF helper

This module closes `WhnfHelperPolicyAt` over the production helper graph.
The assembled contract contains no abstract helper premise: projection,
application rebuilding, iota, primitive accelerators, Nat-offset handling,
quotient reduction, and delta unfolding are all tied to their concrete
implementations under one fixed predecessor method table.
-/

namespace Ix.Tc

namespace RecM

/-- Every helper called by the structural, no-delta, and full-WHNF reducer
steps restores the caller's inference policy on both success and error. -/
def concreteWhnfHelperPolicy
    (methods : Methods .anon) (hmethods : methods.PreservesInferOnly) :
    WhnfHelperPolicyAt methods where
  proj := tryProjReduce_preservesInferOnly hmethods
  finishApp := finishAppResult_preservesInferOnly
  iota := tryIotaWithFlags_preservesInferOnly hmethods
  bitvec := tryReduceBitvec_preservesInferOnly hmethods
  nat := tryReduceNatWithSuccMode_preservesInferOnly hmethods
  native := tryReduceNative_preservesInferOnly hmethods
  string := tryReduceString_preservesInferOnly
  projectionDefinition := tryReduceProjectionDefinition_preservesInferOnly
  quot := tryQuotReduce_preservesInferOnly hmethods
  decidable := tryReduceDecidable_preservesInferOnly hmethods
  natOffset := tryNatOffsetStuck_preservesInferOnly hmethods
  delta := deltaUnfoldOne_preservesInferOnly

/-- The complete concrete helper graph induces the reducer-step policy used
by all four public WHNF driver variants. -/
def concreteWhnfReductionPolicy
    (methods : Methods .anon) (hmethods : methods.PreservesInferOnly) :
    WhnfReductionPolicyAt methods :=
  (concreteWhnfHelperPolicy methods hmethods).reductionPolicy hmethods

end RecM

end Ix.Tc
