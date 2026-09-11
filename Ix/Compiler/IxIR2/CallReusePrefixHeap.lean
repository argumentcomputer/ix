import Ix.Compiler.IxIR2.CallReusePrefixTrace

/-! Hot and cold reset facts derived from the actual baseline retain/release pair. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.IxIR1.Sim (RValsIso)

theorem HeapState.hotPrefix {context : Context} {mapping : Array Nat}
    {left right retained released : Store} {leftLocation rightLocation : Nat}
    {cid : CtorId} {fields : Array RVal} {heapFuel remaining : Nat}
    (state : HeapState context mapping left right)
    (mapped : MapRel mapping leftLocation rightLocation)
    (found : left.get? leftLocation = some ⟨.shared, 1, .ctorN cid fields⟩)
    (retains : RetainSharedMany left fields retained)
    (releases : releaseShared heapFuel retained (.loc leftLocation) = .ok (released, remaining)) :
    HeapTransition context mapping mapping left released right
      (ReuseSim.physicalHotResetStore right rightLocation) := by
  cases heapFuel with
  | zero => simp [releaseShared, releaseSharedWork] at releases
  | succ fuel =>
      have contents := hotPrefix_order state.ordered found retains releases
      have heap := (state.heap.reserve mapped found).congr contents.nodes
        (show (ReuseSim.physicalHotResetStore right rightLocation).heap.nodes =
          (right.reserve rightLocation).heap.nodes from rfl)
      have retainedObs := retains.observations
      have releasedObs := releaseShared_observations releases
      refine ⟨⟨heap, (state.ordered.retainMany retains).releaseWork releases,
        (state.shaped.retainMany retains).releaseWork releases⟩,
        MapExtends.refl mapping, ⟨?_, ?_⟩, ?_⟩
      · change right.heap.rcops + left.heap.rcops ≤ released.heap.rcops + right.heap.rcops
        omega
      · intro before
        change right.peakLiveNodes ≤ released.peakLiveNodes
        rw [releasedObs.2.2.1, retainedObs.2.2.1]
        exact before
      · rw [releaseSharedWork_allocationEvents releases, retains.allocationEvents]
        change left.allocationEvents + right.allocationEvents = right.allocationEvents + left.allocationEvents
        omega

theorem HeapState.coldPrefix {context : Context} {mapping : Array Nat}
    {left right retained released : Store} {leftLocation rightLocation rc : Nat}
    {cid : CtorId} {leftFields rightFields : Array RVal} {heapFuel remaining : Nat}
    (state : HeapState context mapping left right)
    (mapped : MapRel mapping leftLocation rightLocation)
    (rightAt : right.get? rightLocation = some ⟨.shared, rc, .ctorN cid rightFields⟩)
    (many : 1 < rc) (fields : RValsIso (MapRel mapping) leftFields.toList rightFields.toList)
    (retains : RetainSharedMany left leftFields retained)
    (releases : releaseShared heapFuel retained (.loc leftLocation) = .ok (released, remaining)) :
    ∃ rightOutput,
      RetainSharedMany
        (ReuseSim.coldResetStartStore right rightLocation ⟨.shared, rc, .ctorN cid rightFields⟩)
        rightFields rightOutput ∧
      HeapTransition context mapping mapping left released right rightOutput := by
  cases heapFuel with
  | zero => simp [releaseShared, releaseSharedWork] at releases
  | succ fuel =>
      obtain ⟨rightRetained, targetRetains, retaining⟩ := state.retainMany fields retains
      obtain ⟨rightReleased, rightRemaining, targetReleases, _, releasing⟩ :=
        retaining.state.releaseWork (Nat.le_refl _) (.cons (.loc mapped) .nil) releases
      obtain ⟨retainedRC, _, commutedRelease, commutedRetain, _⟩ :=
        ReuseSim.coldPrefix_commutes (heapFuel := fuel) rightAt many targetRetains
      have same := Except.ok.inj (targetReleases.symm.trans commutedRelease)
      cases same
      have paired := retaining.trans releasing
      refine ⟨_, commutedRetain, ⟨⟨paired.state.heap.congr rfl rfl,
        paired.state.ordered, paired.state.shaped⟩, MapExtends.refl mapping, ?_, ?_⟩⟩
      · exact ⟨paired.costs.rcops, paired.costs.peakLive⟩
      · exact paired.events

end Ix.Compiler.IxIR2.CallReuse.Sim
