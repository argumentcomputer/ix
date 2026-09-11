import Ix.Compiler.IxIR2.ReuseSim

/-!
# Dynamic shared-reuse simulation fixtures

The fixtures keep the semantic theorems honest without coupling them to the
larger reversal benchmark.  The leaf case exercises physical reuse directly;
the linked case also runs the baseline retain/deep-release prefix and verifies
that its child refcount traffic cancels before the replacement is allocated.
-/

namespace Ix.Compiler.IxIR2.ReuseSim.Examples

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2.Eval

private def blockAddress : Address := Address.replicate 0xa1

private def oldNode : IxIR1.Node :=
  .ctorN { block := blockAddress, indIdx := 0, cidx := 0 } #[]

private def newNode : IxIR1.Node :=
  .ctorN { block := blockAddress, indIdx := 0, cidx := 1 } #[]

private def childNode : IxIR1.Node :=
  .ctorN { block := blockAddress, indIdx := 1, cidx := 0 } #[]

private def childHeap : IxIR1.Store :=
  (({} : IxIR1.Store).allocNode .shared childNode).1

private def childLocation : Nat :=
  (({} : IxIR1.Store).allocNode .shared childNode).2

private def linkedOldNode : IxIR1.Node :=
  .ctorN { block := blockAddress, indIdx := 2, cidx := 0 }
    #[.loc childLocation]

private def linkedNewNode : IxIR1.Node :=
  .ctorN { block := blockAddress, indIdx := 2, cidx := 1 }
    #[.loc childLocation]

private def linkedHeap : IxIR1.Store :=
  (childHeap.allocNode .shared linkedOldNode).1

private def linkedTarget : Nat :=
  (childHeap.allocNode .shared linkedOldNode).2

private def linkedStore : Store :=
  { heap := linkedHeap }

private def initialHeap : IxIR1.Store :=
  (({} : IxIR1.Store).allocNode .shared oldNode).1

private def target : Nat :=
  (({} : IxIR1.Store).allocNode .shared oldNode).2

private def initialStore : Store :=
  { heap := initialHeap }

private theorem target_live :
    initialStore.get? target = some ⟨.shared, 1, oldNode⟩ := by
  exact IxIR1.Sim.HeapIso.get?_allocNode_new
    ({} : IxIR1.Store) .shared oldNode

private theorem initial_owned :
    IxIR1.Sim.RootOwnership initialStore.heap
      [⟨.shared, .loc target⟩] := by
  apply IxIR1.Sim.RootOwnership.allocNode (store := ({} : IxIR1.Store))
  · simpa [oldNode, IxIR1.Sim.nodeChildren, IxIR1.Sim.rootsFor] using
      IxIR1.Sim.RootOwnership.empty
  · trivial

private theorem child_live :
    linkedStore.get? childLocation = some ⟨.shared, 1, childNode⟩ := by
  apply IxIR1.Sim.HeapIso.get?_allocNode_old
  exact IxIR1.Sim.HeapIso.get?_allocNode_new
    ({} : IxIR1.Store) .shared childNode

private theorem linked_target_live :
    linkedStore.get? linkedTarget =
      some ⟨.shared, 1, linkedOldNode⟩ := by
  exact IxIR1.Sim.HeapIso.get?_allocNode_new
    childHeap .shared linkedOldNode

private theorem child_owned :
    IxIR1.Sim.RootOwnership childHeap
      [⟨.shared, .loc childLocation⟩] := by
  apply IxIR1.Sim.RootOwnership.allocNode (store := ({} : IxIR1.Store))
  · simpa [childNode, IxIR1.Sim.nodeChildren,
      IxIR1.Sim.rootsFor] using IxIR1.Sim.RootOwnership.empty
  · trivial

private theorem linked_owned :
    IxIR1.Sim.RootOwnership linkedStore.heap
      [⟨.shared, .loc linkedTarget⟩] := by
  apply IxIR1.Sim.RootOwnership.allocNode (store := childHeap)
  · simpa [linkedOldNode, IxIR1.Sim.nodeChildren,
      IxIR1.Sim.rootsFor] using child_owned
  · trivial

private def linkedRetainedStore : Store :=
  incrementSharedStore linkedStore childLocation
    ⟨.shared, 1, childNode⟩

private theorem linked_retained :
    RetainSharedMany linkedStore #[.loc childLocation]
      linkedRetainedStore := by
  refine RetainSharedMany.cons (middle := linkedRetainedStore) ?_
    (RetainSharedMany.empty _)
  simp [retainShared, child_live, linkedRetainedStore,
    incrementSharedStore]

private theorem linkedRetained_child_live :
    linkedRetainedStore.get? childLocation =
      some ⟨.shared, 2, childNode⟩ := by
  exact get?_incrementSharedStore_same child_live

private theorem linkedRetained_target_live :
    linkedRetainedStore.get? linkedTarget =
      some ⟨.shared, 1, linkedOldNode⟩ := by
  apply get?_incrementSharedStore_other
  · decide
  · exact child_live
  · exact linked_target_live

private def linkedReleaseStart : Store :=
  linkedRetainedStore.rcTick.kill linkedTarget

private theorem linkedReleaseStart_child_live :
    linkedReleaseStart.get? childLocation =
      some ⟨.shared, 2, childNode⟩ := by
  apply IxIR1.Sim.get?_kill_other
  · decide
  · exact linkedRetained_target_live
  · exact linkedRetained_child_live

private def linkedReleasedStore : Store :=
  baselineDecrementStore linkedReleaseStart childLocation
    ⟨.shared, 2, childNode⟩

private theorem linked_released :
    releaseShared 2 linkedRetainedStore (.loc linkedTarget) =
      .ok (linkedReleasedStore, 0) := by
  simp only [releaseShared, releaseSharedWork, linkedRetained_target_live,
    linkedOldNode]
  change releaseSharedWork 1 linkedReleaseStart [.loc childLocation] = _
  simp [releaseSharedWork, linkedReleaseStart_child_live,
    linkedReleasedStore, baselineDecrementStore]

/-- The concrete physical operation succeeds, and its heap is related to the
logical operation's heap by the same live-location bijection exported to the
general block proof. -/
theorem leafHotReuseProducesRelatedHeaps :
    ∃ physical logical,
      physicalHotReuseStore initialStore target newNode 0 = .ok physical ∧
      logical = (logicalHotReuseStore initialStore target newNode).1 ∧
      Nonempty (IxIR1.Sim.HeapIso physical.heap logical.heap) := by
  obtain ⟨physical, reused, iso, _, _, _⟩ :=
    hotReuse_sound (store := initialStore) (target := target)
      (oldNode := oldNode) (newNode := newNode)
      (before := []) (after := []) 0 target_live initial_owned
      (by simp [oldNode, newNode, IxIR1.Sim.nodeChildren,
        IxIR1.Sim.rootsFor])
      (by trivial)
  exact ⟨physical, (logicalHotReuseStore initialStore target newNode).1,
    reused, rfl, ⟨iso⟩⟩

/-- A one-child constructor exercises the whole baseline-prefix theorem:
retain the projected child, deep-release the unit parent, then allocate the
replacement.  Physical reset/reuse reaches a heap isomorphic to that concrete
baseline execution. -/
theorem linkedHotPrefixProducesRelatedHeaps :
    ∃ physical,
      physicalHotReuseStore linkedStore linkedTarget linkedNewNode 1 =
          .ok physical ∧
      Nonempty (IxIR1.Sim.HeapIso physical.heap
        (linkedReleasedStore.allocNode .shared linkedNewNode).1.heap) := by
  obtain ⟨physical, reused, iso, _, _, _⟩ :=
    hotPrefixReuse_sound
      (store := linkedStore)
      (baselineRetained := linkedRetainedStore)
      (baselineReleased := linkedReleasedStore)
      (target := linkedTarget)
      (oldCid := { block := blockAddress, indIdx := 2, cidx := 0 })
      (newCid := { block := blockAddress, indIdx := 2, cidx := 1 })
      (fields := #[.loc childLocation])
      (newFields := #[.loc childLocation])
      (fieldFuel := 1)
      (remaining := 0)
      (before := [])
      (after := [])
      1 linked_target_live linked_owned linked_retained linked_released
      (by simp [IxIR1.Sim.rootsFor])
      (by trivial)
  exact ⟨physical, reused, ⟨iso⟩⟩

end Ix.Compiler.IxIR2.ReuseSim.Examples
