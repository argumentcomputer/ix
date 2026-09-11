import Ix.Compiler.IxIR2.Resources
import Ix.Compiler.IxIR2.ReuseSim

/-! Shared-result reclamation transported through the existing semantic heap
relation. Allocation accounting is proved separately from actual physical
execution; it is not added to `StableHeapRel`. -/

namespace Ix.Compiler.IxIR2.ReuseSim

open Eval

/-- Releasing related roots at the same traversal budget preserves successful
reclamation across exact contents and allocation-history isomorphisms. -/
theorem StableHeapRel.sharedReclamation {baseline rewritten released : Store}
    {locRel : Nat → Nat → Prop} {baselineValue rewrittenValue : RVal}
    (heaps : StableHeapRel baseline rewritten locRel)
    (values : IxIR1.Sim.RValIso locRel baselineValue rewrittenValue)
    {fuel remaining : Nat}
    (release : releaseShared fuel baseline baselineValue = .ok (released, remaining))
    (empty : released.live = 0) :
    ∃ output,
      releaseShared fuel rewritten rewrittenValue = .ok (output, remaining) ∧
      output.live = 0 := by
  cases heaps with
  | contents same =>
      have equal : baselineValue = rewrittenValue := by
        cases values with
        | loc related => exact congrArg IxIR1.RVal.loc related
        | lit => rfl
        | erased => rfl
      subst rewrittenValue
      obtain ⟨output, run, outputHeaps⟩ := same.releaseShared release
      refine ⟨output, run, ?_⟩
      simpa only [Store.live_eq_countP, ← outputHeaps.nodes] using empty
  | isomorphic iso =>
      obtain ⟨output, outputHeap, run, relation⟩ :=
        releaseSharedWork_historyIso_sameFuel iso.symm (.cons values .nil) release
      exact ⟨output, run, outputHeap.right_live_eq_zero empty⟩

end Ix.Compiler.IxIR2.ReuseSim
