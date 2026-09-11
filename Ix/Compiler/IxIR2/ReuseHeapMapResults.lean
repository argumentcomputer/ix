import Ix.Compiler.IxIR2.ReuseHeapMapOps
import Ix.Compiler.IxIR2.ReuseCost

/-!
# Semantic and cost observations of allocation history

The history map has exactly the established live-heap meaning at closed
endpoints. Live-node counts and pending RC agree even during heap traversal,
when the work list temporarily owns children of an already removed node.
-/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Ix.Compiler.IxIR2.Eval
open Ix.Compiler.IxIR1.Sim (NodeIso NodeBoxIso RValIso RValsIso LiveRVal StoreClosed HeapIso)
open Ix.Compiler.IxIR1.CostTrace

def LiveMapRel (left : Store) (mapping : Array Nat) (l r : Nat) : Prop :=
  MapRel mapping l r ∧ LiveRVal left.heap (.loc l)

theorem values_liveMap {left : Store} {mapping : Array Nat} {leftValues rightValues : List RVal}
    (related : RValsIso (MapRel mapping) leftValues rightValues)
    (live : ∀ value ∈ leftValues, LiveRVal left.heap value) :
    RValsIso (LiveMapRel left mapping) leftValues rightValues := by
  induction related with
  | nil => exact .nil
  | @cons lval rval ls rs head tail ih =>
      refine .cons ?_ (ih (fun value member => live value (by simp [member])))
      cases head with
      | @loc l r mapped => exact .loc ⟨mapped, live (.loc l) (by simp)⟩
      | lit => exact .lit
      | erased => exact .erased

theorem node_liveMap {left : Store} {mapping : Array Nat} {leftNode rightNode : Node}
    (related : NodeIso (MapRel mapping) leftNode rightNode)
    (live : ∀ value ∈ IxIR1.Sim.nodeChildren leftNode, LiveRVal left.heap value) :
    NodeIso (LiveMapRel left mapping) leftNode rightNode := by
  cases related with
  | ctor fields => exact .ctor (values_liveMap fields live)
  | pap arguments => exact .pap (values_liveMap arguments live)

def HeapMap.toHeapIso {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) (closed : StoreClosed left.heap) :
    HeapIso left.heap right.heap where
  locRel := LiveMapRel left mapping
  left_unique := fun one two => one.1.functional two.1
  right_unique := by
    intro l k r one two
    obtain ⟨a, firstAt⟩ := one.2
    obtain ⟨b, secondAt⟩ := two.2
    exact heap.injectiveLive one.1 two.1 firstAt secondAt
  left_total := by
    intro l box found
    obtain ⟨r, related⟩ := heap.left_total found
    exact ⟨r, related, box, found⟩
  right_total := by
    intro r box found
    obtain ⟨l, leftBox, related, leftAt⟩ := heap.backward found
    exact ⟨l, related, leftBox, leftAt⟩
  related_live := by
    intro l r related
    obtain ⟨mapped, leftBox, leftAt⟩ := related
    obtain ⟨rightBox, rightAt, boxes⟩ := heap.forward mapped leftAt
    refine ⟨leftBox, rightBox, leftAt, rightAt, boxes.world, boxes.rc, ?_⟩
    exact node_liveMap boxes.node (closed leftAt)

theorem HeapMap.toHeapIso_value {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) (closed : StoreClosed left.heap)
    {leftValue rightValue : RVal} (related : RValIso (MapRel mapping) leftValue rightValue)
    (live : LiveRVal left.heap leftValue) :
    RValIso (heap.toHeapIso closed).locRel leftValue rightValue := by
  cases related with
  | loc mapped => exact .loc ⟨mapped, live⟩
  | lit => exact .lit
  | erased => exact .erased

/-- Live isomorphism is a valid history relation with no dead rows. -/
def liveHistory {left right : IxIR1.Store} (iso : HeapIso left right) :
    IxIR1.Sim.HeapHistoryIso left right where
  locRel := iso.locRel
  left_unique := iso.left_unique
  right_unique := iso.right_unique
  left_bound := by
    intro l r related
    obtain ⟨leftBox, _, leftAt, _, _⟩ := iso.related_live related
    exact (Array.getElem?_eq_some_iff.mp (IxIR1.Sim.nodes_get?_of_get? leftAt)).1
  right_bound := by
    intro l r related
    obtain ⟨_, rightBox, _, rightAt, _⟩ := iso.related_live related
    exact (Array.getElem?_eq_some_iff.mp (IxIR1.Sim.nodes_get?_of_get? rightAt)).1
  left_total := iso.left_total
  right_total := iso.right_total
  related := fun related => .inr (iso.related_live related)

theorem HeapMap.toStable {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) (closed : StoreClosed left.heap) :
    ReuseSim.StableHeapRel left right (LiveMapRel left mapping) :=
  .isomorphic (liveHistory (heap.toHeapIso closed)).symm

theorem HeapMap.right_empty {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) (empty : left.live = 0) : right.live = 0 := by
  apply (IxIR1.Reclamation.Store.live_eq_zero_iff_no_live_slot right.heap).2
  intro box member
  obtain ⟨r, slot⟩ := Array.mem_iff_getElem?.mp member
  have found : right.get? r = some box := by simp [Store.get?, IxIR1.Store.get?, slot]
  obtain ⟨l, leftBox, _, leftAt⟩ := heap.backward found
  have leftMember := Array.mem_iff_getElem?.mpr
    ⟨l, IxIR1.Sim.nodes_get?_of_get? leftAt⟩
  exact (IxIR1.Reclamation.Store.live_eq_zero_iff_no_live_slot left.heap).1 empty
    leftBox leftMember

theorem HeapMap.live_eq {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) : left.live = right.live := by
  classical
  by_cases empty : left.live = 0
  · exact empty.trans (heap.right_empty empty).symm
  have present : ∃ box, some box ∈ left.heap.nodes := by
    apply Classical.byContradiction
    intro absent
    simp only [not_exists] at absent
    exact empty ((IxIR1.Reclamation.Store.live_eq_zero_iff_no_live_slot left.heap).2 absent)
  obtain ⟨box, member⟩ := present
  obtain ⟨l, slot⟩ := Array.mem_iff_getElem?.mp member
  have found : left.get? l = some box := by simp [Store.get?, IxIR1.Store.get?, slot]
  obtain ⟨r, rightBox, mapped, rightAt, _⟩ := heap.get found
  have leftCount := Store.live_kill found
  have rightCount := Store.live_kill rightAt
  have remaining := (heap.kill mapped found).live_eq
  omega
termination_by left.live
decreasing_by
  have _removed := Store.live_kill found
  omega

theorem HeapMap.pendingRC_eq {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) : left.pendingRC = right.pendingRC := by
  classical
  by_cases empty : left.live = 0
  · rw [ReuseSim.pendingRC_empty empty, ReuseSim.pendingRC_empty (heap.right_empty empty)]
  have present : ∃ box, some box ∈ left.heap.nodes := by
    apply Classical.byContradiction
    intro absent
    simp only [not_exists] at absent
    exact empty ((IxIR1.Reclamation.Store.live_eq_zero_iff_no_live_slot left.heap).2 absent)
  obtain ⟨box, member⟩ := present
  obtain ⟨l, slot⟩ := Array.mem_iff_getElem?.mp member
  have found : left.get? l = some box := by simp [Store.get?, IxIR1.Store.get?, slot]
  obtain ⟨r, rightBox, mapped, rightAt, boxes⟩ := heap.get found
  have leftRemoved := sharedRcPotential_kill (store := left.heap) found
  have rightRemoved := sharedRcPotential_kill (store := right.heap) rightAt
  have weights : slotSharedRcPotential (some box) = slotSharedRcPotential (some rightBox) := by
    rcases box with ⟨world, rc, node⟩
    rcases rightBox with ⟨rightWorld, rightRC, rightNode⟩
    have worlds := boxes.world
    have counts := boxes.rc
    dsimp at worlds counts
    subst rightWorld
    subst rightRC
    cases world <;> rfl
  have remaining := (heap.kill mapped found).pendingRC_eq
  change sharedRcPotential (left.heap.kill l) = sharedRcPotential (right.heap.kill r) at remaining
  unfold Store.pendingRC
  omega
termination_by left.live
decreasing_by
  have _removed := Store.live_kill found
  omega

theorem HeapMap.costDelta {beforeLeft beforeRight afterLeft afterRight : Store}
    {beforeMap afterMap : Array Nat} (before : HeapMap beforeLeft beforeRight beforeMap)
    (after : HeapMap afterLeft afterRight afterMap) {events : Nat} {charge : Int}
    (leftRC : (afterLeft.amortizedRC : Int) = beforeLeft.amortizedRC + charge)
    (rightRC : (afterRight.amortizedRC : Int) = beforeRight.amortizedRC + charge)
    (leftPeak : afterLeft.peakLiveNodes = if events = 0 then beforeLeft.peakLiveNodes
      else max beforeLeft.peakLiveNodes afterLeft.live)
    (rightPeak : afterRight.peakLiveNodes = if events = 0 then beforeRight.peakLiveNodes
      else max beforeRight.peakLiveNodes afterRight.live) :
    CostDelta beforeLeft afterLeft beforeRight afterRight :=
  .of_observations before.pendingRC_eq after.pendingRC_eq after.live_eq
    leftRC rightRC leftPeak rightPeak

end Ix.Compiler.IxIR2.CallReuse.Sim
