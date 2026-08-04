import Ix.Tc.Verify.Check.DefEqCachePolicy

/-!
# Operational closure of the recursive method table

All concrete WHNF, inference, and DefEq implementations preserve the
caller's `inferOnly` bit when their recursive calls use a predecessor table
with the same six-field frame.  This is the non-circular one-layer theorem
needed to close every finite `methodsN` approximation.
-/

namespace Ix.Tc

namespace Methods

/-- One production `Methods.next` layer preserves inference policy whenever
its strictly smaller callback table does. -/
theorem next_preservesInferOnly
    (methods : Methods .anon) (hmethods : methods.PreservesInferOnly) :
    (Methods.next methods).PreservesInferOnly := by
  let reductionPolicy :=
    RecM.concreteWhnfReductionPolicy methods hmethods
  let noDeltaPolicy : RecM.WhnfNoDeltaPolicyAt methods :=
    reductionPolicy.toWhnfNoDeltaPolicyAt
  have hwhnf : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly :=
    RecM.whnf_preservesInferOnly reductionPolicy
  have hcore : ∀ source,
      ((RecM.whnfCore source).run methods).PreservesInferOnly :=
    RecM.whnfCore_preservesInferOnly noDeltaPolicy
  have hmode : ∀ source mode,
      ((RecM.whnfWithNatSuccMode source mode).run
        methods).PreservesInferOnly :=
    RecM.whnfWithNatSuccMode_preservesInferOnly reductionPolicy
  have hcoreFlags : ∀ source flags,
      ((RecM.whnfCoreWithFlags source flags).run
        methods).PreservesInferOnly :=
    RecM.whnfCoreWithFlags_preservesInferOnly noDeltaPolicy
  have hnoDelta : ∀ source,
      ((RecM.whnfNoDelta source).run methods).PreservesInferOnly :=
    RecM.whnfNoDelta_preservesInferOnly noDeltaPolicy
  have hcheapCore : ∀ source,
      ((RecM.whnfCoreForDefEq source).run methods).PreservesInferOnly :=
    RecM.whnfCoreForDefEq_preservesInferOnly noDeltaPolicy
  have hcheapNoDelta : ∀ source,
      ((RecM.whnfNoDeltaForDefEq source).run
        methods).PreservesInferOnly :=
    RecM.whnfNoDeltaForDefEq_preservesInferOnly noDeltaPolicy
  have hinfer : ∀ source,
      ((RecM.infer source).run methods).PreservesInferOnly :=
    RecM.infer_preservesInferOnly_of_whnf methods hmethods hwhnf
  have hinner : ∀ left right,
      ((RecM.isDefEqInner left right).run
        methods).PreservesInferOnly :=
    RecM.isDefEqInner_preservesInferOnly hmethods hwhnf hcore hnoDelta
      hcheapCore hcheapNoDelta
  have hdefeq : ∀ left right,
      ((RecM.isDefEq left right).run methods).PreservesInferOnly :=
    RecM.isDefEq_preservesInferOnly_of_inner hinner
  exact {
    whnf := hwhnf
    whnfCore := hcore
    whnfMode := hmode
    whnfCoreFlags := hcoreFlags
    infer := hinfer
    isDefEq := hdefeq }

/-- Concrete one-layer closure used by the finite production knot. -/
theorem inferOnlyClosed : Methods.InferOnlyClosed := by
  intro methods hmethods
  exact next_preservesInferOnly methods hmethods

/-- Every depth-indexed production table restores its caller's inference
policy on success and error. -/
theorem methodsN_concrete_preservesInferOnly (depth : Nat) :
    (methodsN (m := .anon) depth).PreservesInferOnly :=
  methodsN_preservesInferOnly inferOnlyClosed depth

end Methods

end Ix.Tc
