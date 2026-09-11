import Ix.Compiler.IxIR2.CostSteps
import Ix.Compiler.IxIR2.ReuseSim

/-!
# Heap correspondence and separate comparative costs

Live nodes and outstanding references depend only on semantic heap contents.
RC and peak costs are kept in independent, compositional certificates.
-/

namespace Ix.Compiler.IxIR2.ReuseSim

open Eval

private theorem history_live_eq {baseline rewritten : Store}
    (heap : IxIR1.Sim.HeapHistoryIso baseline.heap rewritten.heap) :
    baseline.live = rewritten.live := by
  classical
  by_cases empty : baseline.live = 0
  · exact empty.trans (heap.right_live_eq_zero empty).symm
  have present : ∃ box, some box ∈ baseline.heap.nodes := by
    apply Classical.byContradiction
    intro absent
    simp only [not_exists] at absent
    exact empty ((IxIR1.Reclamation.Store.live_eq_zero_iff_no_live_slot baseline.heap).2 absent)
  obtain ⟨box, member⟩ := present
  obtain ⟨location, slot⟩ := Array.mem_iff_getElem?.mp member
  have found : baseline.get? location = some box := by
    simp [Store.get?, IxIR1.Store.get?, slot]
  obtain ⟨rewrittenLocation, locations⟩ := heap.left_total found
  obtain ⟨rewrittenBox, rewrittenAt, _boxes⟩ := heap.boxes locations found
  have baselineCount := Store.live_kill found
  have rewrittenCount := Store.live_kill (store := rewritten) rewrittenAt
  have remaining := history_live_eq
    (baseline := baseline.kill location) (rewritten := rewritten.kill rewrittenLocation)
    (heap.kill locations found rewrittenAt)
  omega
termination_by baseline.live
decreasing_by
  have _removed := Store.live_kill found
  omega

/-- Allocation-history renaming preserves the number of live nodes even
though dead slots, fresh-allocation counters, and physical addresses differ. -/
theorem StableHeapRel.live_eq {baseline rewritten : Store}
    {locRel : Nat → Nat → Prop} (heap : StableHeapRel baseline rewritten locRel) :
    baseline.live = rewritten.live := by
  cases heap with
  | contents same => simp only [Store.live_eq_countP, same.nodes]
  | isomorphic history => exact (history_live_eq history).symm

end Ix.Compiler.IxIR2.ReuseSim

namespace Ix.Compiler.IxIR2.ReuseSim

open Eval
open Ix.Compiler.IxIR1.CostTrace

/-- An empty live heap carries no outstanding reference-count work. -/
theorem pendingRC_empty {store : Store} (empty : store.live = 0) :
    store.pendingRC = 0 := by
  have absent := (IxIR1.Reclamation.Store.live_eq_zero_iff_no_live_slot store.heap).1 empty
  have loop : ∀ (slots : List (Option IxIR1.NodeBox)),
      (∀ box, some box ∉ slots) → sharedRcPotentialList slots = 0 := by
    intro slots
    induction slots with
    | nil => intro absent; rfl
    | cons slot rest ih =>
        intro absent
        cases slot with
        | some box => exact False.elim (absent box (by simp))
        | none =>
            simpa [sharedRcPotentialList, slotSharedRcPotential] using
              ih (fun box member => absent box (by simp [member]))
  exact loop store.heap.nodes.toList (by simpa using absent)

/-- Allocation-history renaming preserves all pending shared RC work. -/
theorem history_pendingRC_eq {baseline rewritten : Store}
    (heap : IxIR1.Sim.HeapHistoryIso baseline.heap rewritten.heap) :
    baseline.pendingRC = rewritten.pendingRC := by
  classical
  by_cases empty : baseline.live = 0
  · rw [pendingRC_empty empty, pendingRC_empty (heap.right_live_eq_zero empty)]
  have present : ∃ box, some box ∈ baseline.heap.nodes := by
    apply Classical.byContradiction
    intro absent
    simp only [not_exists] at absent
    exact empty ((IxIR1.Reclamation.Store.live_eq_zero_iff_no_live_slot baseline.heap).2 absent)
  obtain ⟨box, member⟩ := present
  obtain ⟨location, slot⟩ := Array.mem_iff_getElem?.mp member
  have found : baseline.get? location = some box := by
    simp [Store.get?, IxIR1.Store.get?, slot]
  obtain ⟨rewrittenLocation, locations⟩ := heap.left_total found
  obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ := heap.boxes locations found
  have leftRemoved := sharedRcPotential_kill (store := baseline.heap) found
  have rightRemoved := sharedRcPotential_kill (store := rewritten.heap) rewrittenAt
  have weights : slotSharedRcPotential (some box) = slotSharedRcPotential (some rewrittenBox) := by
    rcases box with ⟨world, rc, node⟩
    rcases rewrittenBox with ⟨rewrittenWorld, rewrittenRC, rewrittenNode⟩
    have worlds := boxes.world
    have counts := boxes.rc
    dsimp at worlds counts
    subst rewrittenWorld
    subst rewrittenRC
    cases world <;> rfl
  have remaining := history_pendingRC_eq
    (baseline := baseline.kill location) (rewritten := rewritten.kill rewrittenLocation)
    (heap.kill locations found rewrittenAt)
  change sharedRcPotential (baseline.heap.kill location) =
    sharedRcPotential (rewritten.heap.kill rewrittenLocation) at remaining
  unfold Store.pendingRC
  omega
termination_by baseline.live
decreasing_by
  have removed := Store.live_kill found
  omega

theorem StableHeapRel.pendingRC_eq {baseline rewritten : Store}
    {locRel : Nat → Nat → Prop} (heap : StableHeapRel baseline rewritten locRel) :
    baseline.pendingRC = rewritten.pendingRC := by
  cases heap with
  | contents same => simp only [Store.pendingRC, sharedRcPotential, same.nodes]
  | isomorphic history => exact (history_pendingRC_eq history).symm

end Ix.Compiler.IxIR2.ReuseSim

namespace Ix.Compiler.IxIR2.Eval

/-- Comparative observations, independent of the semantic heap relation. -/
structure Store.CostBounds (baseline selected : Store) : Prop where
  rcops : selected.heap.rcops ≤ baseline.heap.rcops
  peakLive : selected.peakLiveNodes ≤ baseline.peakLiveNodes

theorem Store.CostBounds.refl (store : Store) : store.CostBounds store :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- RC increments compare additively; peak comparisons transport any incoming
peak bound. The peak counter already records every intermediate allocation. -/
structure CostDelta (baselineBefore baselineAfter selectedBefore selectedAfter : Store) : Prop where
  rcops : selectedAfter.heap.rcops + baselineBefore.heap.rcops ≤
    baselineAfter.heap.rcops + selectedBefore.heap.rcops
  peakLive : selectedBefore.peakLiveNodes ≤ baselineBefore.peakLiveNodes →
    selectedAfter.peakLiveNodes ≤ baselineAfter.peakLiveNodes

namespace CostDelta

theorem refl (baseline selected : Store) : CostDelta baseline baseline selected selected :=
  ⟨by omega, fun bound => bound⟩

theorem preserves {b₀ b₁ r₀ r₁ : Store} (delta : CostDelta b₀ b₁ r₀ r₁)
    (before : b₀.CostBounds r₀) : b₁.CostBounds r₁ :=
  ⟨by have _ := delta.rcops; have _ := before.rcops; omega, delta.peakLive before.peakLive⟩

theorem trans {b₀ b₁ b₂ r₀ r₁ r₂ : Store}
    (first : CostDelta b₀ b₁ r₀ r₁) (second : CostDelta b₁ b₂ r₁ r₂) :
    CostDelta b₀ b₂ r₀ r₂ :=
  ⟨by have _ := first.rcops; have _ := second.rcops; omega,
    fun bound => second.peakLive (first.peakLive bound)⟩

/-- Equal RC charges and allocation events in corresponding heaps imply
equal raw RC increments and preservation of the peak comparison. -/
theorem of_observations {b₀ b₁ r₀ r₁ : Store} {events : Nat} {charge : Int}
    (pendingBefore : b₀.pendingRC = r₀.pendingRC)
    (pendingAfter : b₁.pendingRC = r₁.pendingRC)
    (liveAfter : b₁.live = r₁.live)
    (baselineRC : (b₁.amortizedRC : Int) = b₀.amortizedRC + charge)
    (selectedRC : (r₁.amortizedRC : Int) = r₀.amortizedRC + charge)
    (baselinePeak : b₁.peakLiveNodes =
      if events = 0 then b₀.peakLiveNodes else max b₀.peakLiveNodes b₁.live)
    (selectedPeak : r₁.peakLiveNodes =
      if events = 0 then r₀.peakLiveNodes else max r₀.peakLiveNodes r₁.live) :
    CostDelta b₀ b₁ r₀ r₁ := by
  constructor
  · change ((b₁.heap.rcops + b₁.pendingRC : Nat) : Int) =
      (b₀.heap.rcops + b₀.pendingRC : Nat) + charge at baselineRC
    change ((r₁.heap.rcops + r₁.pendingRC : Nat) : Int) =
      (r₀.heap.rcops + r₀.pendingRC : Nat) + charge at selectedRC
    omega
  · intro bound
    rw [baselinePeak, selectedPeak, liveAfter]
    split
    · exact bound
    · omega

/-- A physical hot reset performs no RC work. Both allocation endpoints
record their complete peaks after the retained baseline fields are released. -/
theorem hot {baseline selected retained released physical : Store}
    {fields : Array RVal} {location baselineLocation fuel remaining payloadUnits : Nat}
    {baselineNode selectedNode : Node}
    (retains : RetainSharedMany baseline fields retained)
    (releases : releaseShared fuel retained (.loc baselineLocation) = .ok (released, remaining))
    (reuses : (ReuseSim.physicalHotResetStore selected location).reuseReservation
      location .shared selectedNode payloadUnits = .ok physical)
    (live : (released.allocNode .shared baselineNode).1.live = physical.live) :
    CostDelta baseline (released.allocNode .shared baselineNode).1 selected physical := by
  have retainedCosts := retains.observations
  have releasedCosts := releaseShared_observations releases
  have reusedCosts := Store.reuseReservation_observations reuses
  constructor
  · have retainedRC := retainedCosts.1
    have releasedRC := releasedCosts.1
    have selectedRC : physical.heap.rcops = selected.heap.rcops := reusedCosts.1
    simp only [Store.rcops_allocNode]
    omega
  · intro before
    rw [Store.peakLive_allocNode, releasedCosts.2.2.1, retainedCosts.2.2.1, reusedCosts.2.2.1]
    change max selected.peakLiveNodes physical.live ≤ max baseline.peakLiveNodes _
    omega

/-- Cold reset retains the same fields and performs the same root decrement
as the baseline, including aliased fields and arbitrary prior counters. -/
theorem cold {baseline selected baselineRetained selectedRetained : Store}
    {baselineFields selectedFields : Array RVal} {baselineLocation selectedLocation : Nat}
    {baselineBox selectedBox : NodeBox} {baselineNode selectedNode : Node}
    (retains : RetainSharedMany baseline baselineFields baselineRetained)
    (selectedRetains : RetainSharedMany
      (ReuseSim.coldResetStartStore selected selectedLocation selectedBox) selectedFields selectedRetained)
    (fields : referenceCountList baselineFields.toList = referenceCountList selectedFields.toList)
    (live : ((ReuseSim.baselineDecrementStore baselineRetained baselineLocation baselineBox).allocNode
      .shared baselineNode).1.live = (selectedRetained.allocNode .shared selectedNode).1.live) :
    CostDelta baseline
      ((ReuseSim.baselineDecrementStore baselineRetained baselineLocation baselineBox).allocNode
        .shared baselineNode).1 selected (selectedRetained.allocNode .shared selectedNode).1 := by
  have retainedCosts := retains.observations
  have selectedCosts := selectedRetains.observations
  constructor
  · have baselineRC := retainedCosts.1
    have selectedRC := selectedCosts.1
    change selectedRetained.heap.rcops = selected.heap.rcops + 1 + _ at selectedRC
    change selectedRetained.heap.rcops + baseline.heap.rcops ≤
      baselineRetained.heap.rcops + 1 + selected.heap.rcops
    omega
  · intro before
    have baselinePeak := retainedCosts.2.2.1
    have selectedPeak : selectedRetained.peakLiveNodes = selected.peakLiveNodes := selectedCosts.2.2.1
    simp only [Store.peakLive_allocNode, selectedPeak]
    change max selected.peakLiveNodes _ ≤ max baselineRetained.peakLiveNodes _
    rw [baselinePeak]
    omega

end CostDelta

def Result.CostBounds (baseline selected : Result) : Prop :=
  baseline.store.CostBounds selected.store

/-- Complete shared-result release preserves the comparative RC and peak
bounds, even with independent sufficient traversal budgets. -/
theorem Store.CostBounds.releaseShared {baseline selected baselineReleased selectedReleased : Store}
    {baselineValue selectedValue : RVal} {baselineFuel selectedFuel baselineRemaining selectedRemaining : Nat}
    {locRel : Nat → Nat → Prop} (costs : baseline.CostBounds selected)
    (heaps : ReuseSim.StableHeapRel baseline selected locRel)
    (baselineRelease : Eval.releaseShared baselineFuel baseline baselineValue =
      .ok (baselineReleased, baselineRemaining))
    (selectedRelease : Eval.releaseShared selectedFuel selected selectedValue =
      .ok (selectedReleased, selectedRemaining))
    (baselineEmpty : baselineReleased.live = 0) (selectedEmpty : selectedReleased.live = 0) :
    baselineReleased.CostBounds selectedReleased := by
  have baselineObserved := releaseShared_observations baselineRelease
  have selectedObserved := releaseShared_observations selectedRelease
  constructor
  · have baselineRC := baselineObserved.2.1
    have selectedRC := selectedObserved.2.1
    change baselineReleased.heap.rcops + baselineReleased.pendingRC =
      baseline.heap.rcops + baseline.pendingRC at baselineRC
    change selectedReleased.heap.rcops + selectedReleased.pendingRC =
      selected.heap.rcops + selected.pendingRC at selectedRC
    have pending := heaps.pendingRC_eq
    have baselineZero := ReuseSim.pendingRC_empty baselineEmpty
    have selectedZero := ReuseSim.pendingRC_empty selectedEmpty
    have bound := costs.rcops
    omega
  · rw [baselineObserved.2.2.1, selectedObserved.2.2.1]
    exact costs.peakLive

/-- The same two actual reclamations carry R3's accounting and free law,
together with the comparative RC and peak bounds. -/
def Result.ReclaimedCostLaws (baseline selected : Result) : Prop :=
  ∃ releaseFuel baselineReleased selectedReleased remaining,
    releaseShared releaseFuel baseline.store baseline.value = .ok (baselineReleased, remaining) ∧
    releaseShared releaseFuel selected.store selected.value = .ok (selectedReleased, remaining) ∧
    baselineReleased.live = 0 ∧ selectedReleased.live = 0 ∧
    baselineReleased.heap.allocs = baselineReleased.heap.frees ∧
    selectedReleased.heap.allocs = selectedReleased.heap.frees ∧
    baselineReleased.heap.frees = selectedReleased.heap.frees + selectedReleased.heap.reuses ∧
    baselineReleased.CostBounds selectedReleased

end Ix.Compiler.IxIR2.Eval
