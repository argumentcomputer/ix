import Ix.Compiler.IxIR2.CallReuseCalls

/-! Compositional heap and cost facts for corresponding executable operations. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso NodeIso)

def MapExtends (before after : Array Nat) : Prop :=
  ∀ {left right}, MapRel before left right → MapRel after left right

theorem MapExtends.refl (mapping : Array Nat) : MapExtends mapping mapping := fun h => h

theorem MapExtends.trans {first middle last : Array Nat}
    (one : MapExtends first middle) (two : MapExtends middle last) : MapExtends first last :=
  fun h => two (one h)

theorem MapExtends.push (mapping : Array Nat) (target : Nat) :
    MapExtends mapping (mapping.push target) := fun h => h.push target

structure HeapState (context : Context) (mapping : Array Nat) (left right : Store) : Prop where
  heap : HeapMap left right mapping
  ordered : Ordered left
  shaped : Shaped context left

theorem MachineRel.heapState {limits : Validate.Limits} {validation : Validate.Context}
    {context : Context} {mapping : Array Nat} {left right : Machine}
    (machines : MachineRel limits validation context mapping left right) :
    HeapState context mapping left.store right.store :=
  ⟨machines.heap, machines.ordered, machines.shaped⟩

structure HeapTransition (context : Context) (before after : Array Nat)
    (leftBefore leftAfter rightBefore rightAfter : Store) : Prop where
  state : HeapState context after leftAfter rightAfter
  extension : MapExtends before after
  costs : CostDelta leftBefore leftAfter rightBefore rightAfter
  events : leftAfter.allocationEvents + rightBefore.allocationEvents =
    rightAfter.allocationEvents + leftBefore.allocationEvents

theorem HeapTransition.refl {context : Context} {mapping : Array Nat} {left right : Store}
    (state : HeapState context mapping left right) :
    HeapTransition context mapping mapping left left right right :=
  ⟨state, MapExtends.refl mapping, .refl left right, by omega⟩

theorem HeapTransition.trans {context : Context} {first middle last : Array Nat}
    {l₀ l₁ l₂ r₀ r₁ r₂ : Store}
    (one : HeapTransition context first middle l₀ l₁ r₀ r₁)
    (two : HeapTransition context middle last l₁ l₂ r₁ r₂) :
    HeapTransition context first last l₀ l₂ r₀ r₂ :=
  ⟨two.state, MapExtends.trans one.extension two.extension, one.costs.trans two.costs,
    by have _ := one.events; have _ := two.events; omega⟩

theorem HeapState.alloc {context : Context} {mapping : Array Nat} {left right : Store}
    (state : HeapState context mapping left right) {world : Owned} {leftNode rightNode : Node}
    (nodes : NodeIso (MapRel mapping) leftNode rightNode)
    (shaped : ShapedNode context world leftNode) :
    HeapTransition context mapping (mapping.push right.heap.nodes.size)
      left (left.allocNode world leftNode).1 right (right.allocNode world rightNode).1 := by
  have heap := state.heap.alloc (world := world) nodes
  refine ⟨⟨heap, state.ordered.alloc state.heap nodes, state.shaped.alloc shaped⟩,
    MapExtends.push mapping right.heap.nodes.size, ?_, by simp; omega⟩
  apply state.heap.costDelta heap (events := 1)
    (charge := if world = .shared then 1 else 0)
  · cases world <;> simp
  · cases world <;> simp
  · rfl
  · rfl

theorem HeapState.retain {context : Context} {mapping : Array Nat} {left right leftOut : Store}
    (state : HeapState context mapping left right) {leftValue rightValue : RVal}
    (values : RValIso (MapRel mapping) leftValue rightValue)
    (run : retainShared left leftValue = .ok leftOut) :
    ∃ rightOut, retainShared right rightValue = .ok rightOut ∧
      HeapTransition context mapping mapping left leftOut right rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.retain values run
  have leftObs := retainShared_observations run
  have rightObs := retainShared_observations targetRun
  have refs : referenceCount leftValue = referenceCount rightValue := by cases values <;> rfl
  refine ⟨rightOut, targetRun, ⟨⟨heap, state.ordered.retain run, state.shaped.retain run⟩,
    MapExtends.refl mapping, ?_, ?_⟩⟩
  · apply state.heap.costDelta heap (events := 0) (charge := 2 * (referenceCount leftValue : Int))
    · omega
    · omega
    · exact leftObs.2.2.1
    · exact rightObs.2.2.1
  · rw [retainShared_allocationEvents run, retainShared_allocationEvents targetRun]
    omega

theorem HeapState.reuse {context : Context} {mapping : Array Nat} {left right rightOut : Store}
    (state : HeapState context mapping left right) {world : Owned} {leftNode rightNode : Node}
    {location payload : Nat} (nodes : NodeIso (MapRel mapping) leftNode rightNode)
    (shaped : ShapedNode context world leftNode)
    (run : right.reuseReservation location world rightNode payload = .ok rightOut) :
    HeapTransition context mapping (mapping.push location)
      left (left.allocNode world leftNode).1 right rightOut := by
  have heap := state.heap.reuse nodes run
  have observed := Store.reuseReservation_observations run
  refine ⟨⟨heap, state.ordered.alloc state.heap nodes, state.shaped.alloc shaped⟩,
    MapExtends.push mapping location, ?_, ?_⟩
  · apply state.heap.costDelta heap (events := 1)
      (charge := if world = .shared then 1 else 0)
    · cases world <;> simp
    · have potential := observed.2.1
      cases world <;> simp_all
    · rfl
    · exact observed.2.2.1
  · rw [Store.allocationEvents_allocNode, Store.reuseReservation_allocationEvents run]
    omega

theorem HeapState.retainMany {context : Context} {mapping : Array Nat} {left right leftOut : Store}
    (state : HeapState context mapping left right) {leftValues rightValues : Array RVal}
    (values : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    (run : RetainSharedMany left leftValues leftOut) :
    ∃ rightOut, RetainSharedMany right rightValues rightOut ∧
      HeapTransition context mapping mapping left leftOut right rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.retainMany values run
  have leftObs := run.observations
  have rightObs := targetRun.observations
  have refs := referenceCountList_iso values
  refine ⟨rightOut, targetRun, ⟨⟨heap, state.ordered.retainMany run, state.shaped.retainMany run⟩,
    MapExtends.refl mapping, ?_, ?_⟩⟩
  · apply state.heap.costDelta heap (events := 0)
      (charge := 2 * (referenceCountList leftValues.toList : Int))
    · omega
    · omega
    · exact leftObs.2.2.1
    · exact rightObs.2.2.1
  · rw [run.allocationEvents, targetRun.allocationEvents]
    omega

theorem HeapState.releaseWork {context : Context} {mapping : Array Nat}
    {left right leftOut : Store} {leftFuel rightFuel leftRemaining : Nat}
    (state : HeapState context mapping left right) (fuel : leftFuel ≤ rightFuel)
    {leftValues rightValues : List RVal} (values : RValsIso (MapRel mapping) leftValues rightValues)
    (run : releaseSharedWork leftFuel left leftValues = .ok (leftOut, leftRemaining)) :
    ∃ rightOut rightRemaining,
      releaseSharedWork rightFuel right rightValues = .ok (rightOut, rightRemaining) ∧
      leftRemaining ≤ rightRemaining ∧
      HeapTransition context mapping mapping left leftOut right rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.releaseWork values run
  have raised := releaseSharedWork_addFuel targetRun (rightFuel - leftFuel)
  rw [Nat.add_sub_of_le fuel] at raised
  have leftObs := releaseSharedWork_observations run
  have rightObs := releaseSharedWork_observations targetRun
  refine ⟨rightOut, leftRemaining + (rightFuel - leftFuel), raised, by omega,
    ⟨⟨heap, state.ordered.releaseWork run, state.shaped.releaseWork run⟩, MapExtends.refl mapping, ?_, ?_⟩⟩
  · apply state.heap.costDelta heap (events := 0) (charge := 0)
    · omega
    · omega
    · exact leftObs.2.2.1
    · exact rightObs.2.2.1
  · rw [releaseSharedWork_allocationEvents run, releaseSharedWork_allocationEvents targetRun]
    omega

theorem HeapState.dropWork {context : Context} {mapping : Array Nat}
    {left right leftOut : Store} {leftFuel rightFuel leftRemaining : Nat}
    (state : HeapState context mapping left right) (fuel : leftFuel ≤ rightFuel)
    {leftValues rightValues : List RVal} (values : RValsIso (MapRel mapping) leftValues rightValues)
    (run : dropUniqueWork leftFuel left leftValues = .ok (leftOut, leftRemaining)) :
    ∃ rightOut rightRemaining,
      dropUniqueWork rightFuel right rightValues = .ok (rightOut, rightRemaining) ∧
      leftRemaining ≤ rightRemaining ∧
      HeapTransition context mapping mapping left leftOut right rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.dropWork values run
  have raised := dropUniqueWork_addFuel targetRun (rightFuel - leftFuel)
  rw [Nat.add_sub_of_le fuel] at raised
  have leftObs := dropUniqueWork_observations run
  have rightObs := dropUniqueWork_observations targetRun
  refine ⟨rightOut, leftRemaining + (rightFuel - leftFuel), raised, by omega,
    ⟨⟨heap, state.ordered.dropWork run, state.shaped.dropWork run⟩, MapExtends.refl mapping, ?_, ?_⟩⟩
  · apply state.heap.costDelta heap (events := 0) (charge := 0)
    · omega
    · omega
    · exact leftObs.2.2.1
    · exact rightObs.2.2.1
  · rw [dropUniqueWork_allocationEvents run, dropUniqueWork_allocationEvents targetRun]
    omega

theorem HeapState.freeUnique {context : Context} {mapping : Array Nat} {left right : Store}
    (state : HeapState context mapping left right) {l r : Nat} {box : NodeBox}
    (mapped : MapRel mapping l r) (found : left.get? l = some box) :
    HeapTransition context mapping mapping left (left.kill l) right (right.kill r) := by
  have heap := state.heap.kill mapped found
  refine ⟨⟨heap, state.ordered.kill found, state.shaped.kill found⟩, MapExtends.refl mapping,
    ⟨by change right.heap.rcops + left.heap.rcops ≤ left.heap.rcops + right.heap.rcops; omega,
      fun bound => bound⟩, by simp; omega⟩

theorem values_size {mapping : Array Nat} {left right : Array RVal}
    (related : RValsIso (MapRel mapping) left.toList right.toList) : left.size = right.size :=
  by simpa using related.lengths

theorem values_extract {mapping : Array Nat} {left right : Array RVal}
    (related : RValsIso (MapRel mapping) left.toList right.toList) (start stop : Nat) :
    RValsIso (MapRel mapping) (left.extract start stop).toList (right.extract start stop).toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  exact (related.drop start).take (stop - start)

theorem scalarOracle_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    (contexts : ContextRel limits validation leftContext rightContext)
    {left right : Array RVal} {address : Ixon.Address} {value : RVal}
    (values : RValsIso (MapRel mapping) left.toList right.toList)
    (called : ScalarOracleCall leftContext address left value) :
    ScalarOracleCall rightContext address right value ∧ RValIso (MapRel mapping) value value := by
  obtain ⟨inputs, result⟩ := called.scalar
  have scalar : (left.toList.all IxIR1.RVal.isScalar) = true := by
    rw [Array.all_toList]
    apply Array.all_eq_true.mpr
    intro i bound
    have valid := Array.all_eq_true.mp inputs i bound
    cases valueAt : left[i] <;> simp_all only [RVal.isScalar, IxIR1.RVal.isScalar]
  have equal := values.eq_of_allScalar scalar
  have same : left = right := Array.toList_inj.mp equal
  subst right
  refine ⟨called.congrOracle contexts.oracle, ?_⟩
  cases value <;> simp_all [RVal.isScalar] <;> constructor

end Ix.Compiler.IxIR2.CallReuse.Sim
