import Ix.Compiler.IxIR2.ReuseHeapMapResults

/-!
# Baseline allocation order for call-spanning reuse

Fresh baseline allocation keeps positive counts and edges to older slots.
This trace property rules out a self-field in the constructor consumed by a
hot prefix. It is independent of exact external root counts.
-/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Ix.Compiler.IxIR2.Eval
open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim (NodeIso RValsIso)
open Ix.Compiler.IxIR1.Reclamation (AllocationOrderInvariant)

def Ordered (store : Store) : Prop := AllocationOrderInvariant store.heap

theorem Ordered.empty : Ordered ({} : Store) := AllocationOrderInvariant.empty

theorem Ordered.congr {before after : Store} (ordered : Ordered before)
    (nodes : after.heap.nodes = before.heap.nodes) : Ordered after := by
  have get : ∀ location, after.heap.get? location = before.heap.get? location := by
    intro location
    simp only [IxIR1.Store.get?, nodes]
  exact ⟨fun found => ordered.rc_pos (by simpa only [get] using found),
    fun found child => ordered.child_lt (by simpa only [get] using found) child⟩

theorem Ordered.retain {store output : Store} (ordered : Ordered store) {value : RVal}
    (run : retainShared store value = .ok output) : Ordered output := by
  cases value with
  | lit => cases run; exact ordered
  | erased => cases run; exact ordered
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp only [retainShared, found, shared, bne_self_eq_false, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at run
            subst output
            have result := (AllocationOrderInvariant.setRc ordered found
              (newRc := box.rc + 1) (by omega)).rcTick
            simpa only [Ordered, Store.setBox_heap, Store.rcTick_heap, shared] using result
          · simp [retainShared, found, shared] at run

theorem Ordered.retainMany {store output : Store} (ordered : Ordered store) {values : Array RVal}
    (run : RetainSharedMany store values output) : Ordered output := by
  have loop : ∀ (values : List RVal) {store output : Store}, Ordered store →
      values.foldlM retainShared store = .ok output → Ordered output := by
    intro values
    induction values with
    | nil => intro store output ordered run; cases run; exact ordered
    | cons head tail ih =>
        intro store output ordered run
        rw [List.foldlM_cons] at run
        cases first : retainShared store head with
        | error error => simp [first, bind, Except.bind] at run
        | ok middle =>
            simp only [first, bind, Except.bind] at run
            exact ih (ordered.retain first) run
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  exact loop values.toList ordered run

theorem Ordered.releaseWork {fuel remaining : Nat} {store output : Store} {values : List RVal}
    (ordered : Ordered store)
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) : Ordered output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact ordered
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact ordered
      | cons value rest =>
          cases value with
          | lit => exact ih ordered run
          | erased => exact ih ordered run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unitRC : box.rc = 1
                      · simp only [releaseSharedWork, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unitRC, beq_self_eq_true] at run
                        exact ih (store := store.rcTick.kill location)
                          (AllocationOrderInvariant.rcTick ordered |>.kill found) run
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        have preserved := (AllocationOrderInvariant.rcTick ordered).setRc found
                          (newRc := box.rc - 1) (by omega)
                        exact ih (store := store.rcTick.setBox location { box with rc := box.rc - 1 })
                          preserved (by simpa only [shared] using run)
                  · simp [releaseSharedWork, found, shared] at run

theorem Ordered.dropWork {fuel remaining : Nat} {store output : Store} {values : List RVal}
    (ordered : Ordered store)
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) : Ordered output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact ordered
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact ordered
      | cons value rest =>
          cases value with
          | lit => exact ih ordered run
          | erased => exact ih ordered run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  by_cases unique : box.world = .unique
                  · cases node : box.node with
                    | papN address arity arguments => simp [dropUniqueWork, found, unique, node] at run
                    | ctorN cid fields =>
                        simp only [dropUniqueWork, found, unique, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, node] at run
                        exact ih (store := store.kill location)
                          (AllocationOrderInvariant.kill ordered found) run
                  · simp [dropUniqueWork, found, unique] at run

theorem HeapMap.valuesBounded {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {leftValues rightValues : List RVal}
    (related : RValsIso (MapRel mapping) leftValues rightValues) :
    IxIR1.Reclamation.ValuesInBounds left.heap leftValues := by
  induction related with
  | nil => simp [IxIR1.Reclamation.ValuesInBounds]
  | cons head tail ih =>
      intro value member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · cases head with
        | loc mapped =>
            change _ < left.heap.nodes.size
            rw [← heap.size]
            exact mapped.bound
        | lit => trivial
        | erased => trivial
      · exact ih value member

theorem Ordered.alloc {left right : Store} {mapping : Array Nat}
    (ordered : Ordered left) (heap : HeapMap left right mapping)
    {world : Owned} {leftNode rightNode : Node}
    (related : NodeIso (MapRel mapping) leftNode rightNode) :
    Ordered (left.allocNode world leftNode).1 :=
  AllocationOrderInvariant.allocNodeOfInBounds ordered
    (heap.valuesBounded (nodeChildren_iso related))

/-- The actual successful retain/release prefix cancels against shallow
removal. Allocation order supplies the missing self-edge exclusion internally. -/
theorem hotPrefix_order {store retained output : Store} {target : Nat} {cid : CtorId}
    {fields : Array RVal} {fieldFuel remaining : Nat} (ordered : Ordered store)
    (targetAt : store.get? target = some ⟨.shared, 1, .ctorN cid fields⟩)
    (retains : RetainSharedMany store fields retained)
    (releases : releaseShared (fieldFuel + 1) retained (.loc target) = .ok (output, remaining)) :
    ReuseSim.HeapContentsEq output (store.kill target) := by
  have different : ∀ value ∈ fields.toList, value ≠ .loc target := by
    intro value member same
    subst value
    have impossible := ordered.child_lt targetAt (show .loc target ∈
      IxIR1.Sim.nodeChildren (.ctorN cid fields) from member)
    omega
  have retainsList : RetainSharedMany store fields.toList.toArray retained := by simpa using retains
  have retainedTarget := ReuseSim.RetainSharedMany.preserves_box targetAt different retainsList
  have childRelease : releaseSharedWork fieldFuel (retained.rcTick.kill target) fields.toList =
      .ok (output, remaining) := by
    simpa [releaseShared, releaseSharedWork, retainedTarget] using releases
  have afterKill := ReuseSim.RetainSharedMany.kill_commute targetAt different retainsList
  have positives : ∀ value ∈ fields.toList, ReuseSim.SharedPositive (store.kill target) value := by
    intro value member
    have world := retainMany_world retains value member
    have positive : ReuseSim.SharedPositive store value := by
      cases value with
      | lit => trivial
      | erased => trivial
      | loc location =>
          cases found : store.get? location with
          | none => simp [RVal.hasWorld, found] at world
          | some box =>
              have shared : box.world = .shared := by simpa [RVal.hasWorld, found] using world
              rcases box with ⟨boxWorld, rc, node⟩
              dsimp at shared
              subst boxWorld
              exact ⟨rc, node, found, ordered.rc_pos found⟩
    exact positive.kill targetAt (different value member)
  exact ReuseSim.retainedFields_release_roundtrip
    (releaseStart := retained.rcTick.kill target) positives afterKill ⟨rfl⟩ childRelease

end Ix.Compiler.IxIR2.CallReuse.Sim
