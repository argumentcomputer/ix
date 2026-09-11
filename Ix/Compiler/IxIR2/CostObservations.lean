import Ix.Compiler.IxIR1.RcPotential
import Ix.Compiler.IxIR2.AllocationEvents

/-!
# RC and peak-live observations of actual heap operations

The shared-reference potential is the existing IxIR₁ cost algebra. These
observations remain independent of semantic heap and value correspondence.
-/

namespace Ix.Compiler.IxIR2.Eval

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1 (Node NodeBox RVal)
open Ix.Compiler.IxIR1.CostTrace

def Store.pendingRC (store : Store) : Nat := sharedRcPotential store.heap

def Store.amortizedRC (store : Store) : Nat := amortizedRc store.heap

def referenceCount : RVal → Nat
  | .loc _ => 1
  | _ => 0

def referenceCountList : List RVal → Nat
  | [] => 0
  | value :: rest => referenceCount value + referenceCountList rest

theorem referenceCountList_iso {locRel : Nat → Nat → Prop}
    {left right : List RVal} (values : IxIR1.Sim.RValsIso locRel left right) :
    referenceCountList left = referenceCountList right := by
  induction values with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [referenceCountList, referenceCount, ih]

@[simp] theorem Store.amortizedRC_allocNode (store : Store) (world : Owned) (node : Node) :
    (store.allocNode world node).1.amortizedRC =
      store.amortizedRC + (if world = .shared then 1 else 0) := by
  cases world <;> simp [Store.amortizedRC, amortizedRc, sharedRcPotential,
    sharedRcPotentialList_append, sharedRcPotentialList, slotSharedRcPotential,
    IxIR1.Store.allocNode] <;> omega

@[simp] theorem Store.peakLive_allocNode (store : Store) (world : Owned) (node : Node) :
    (store.allocNode world node).1.peakLiveNodes =
      max store.peakLiveNodes (store.allocNode world node).1.live := rfl

@[simp] theorem Store.rcops_allocNode (store : Store) (world : Owned) (node : Node) :
    (store.allocNode world node).1.heap.rcops = store.heap.rcops := rfl

theorem retainShared_observations {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) :
    output.heap.rcops = store.heap.rcops + referenceCount value ∧
    output.amortizedRC = store.amortizedRC + 2 * referenceCount value ∧
    output.peakLiveNodes = store.peakLiveNodes ∧ output.live = store.live := by
  cases value with
  | lit literal => cases run; exact ⟨rfl, rfl, rfl, rfl⟩
  | erased => cases run; exact ⟨rfl, rfl, rfl, rfl⟩
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp [retainShared, found, shared] at run
            subst output
            have rc := amortizedRc_incRcStore (store := store.heap)
              (location := location) (rc := box.rc) (node := box.node)
              (by rcases box with ⟨world, rc, node⟩; dsimp at shared; subst world; exact found)
            refine ⟨rfl, ?_, rfl, ?_⟩
            · simpa [Store.amortizedRC, IxIR1.Sim.incRcStore, Store.rcTick,
                Store.setBox, referenceCount, shared] using rc
            · exact Store.live_setBox found
          · simp [retainShared, found, shared] at run

theorem RetainSharedMany.observations {store output : Store} {values : Array RVal}
    (run : RetainSharedMany store values output) :
    output.heap.rcops = store.heap.rcops + referenceCountList values.toList ∧
    output.amortizedRC = store.amortizedRC + 2 * referenceCountList values.toList ∧
    output.peakLiveNodes = store.peakLiveNodes ∧ output.live = store.live := by
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  have loop : ∀ (values : List RVal) {store output : Store},
      values.foldlM retainShared store = .ok output →
        output.heap.rcops = store.heap.rcops + referenceCountList values ∧
        output.amortizedRC = store.amortizedRC + 2 * referenceCountList values ∧
        output.peakLiveNodes = store.peakLiveNodes ∧ output.live = store.live := by
    intro values
    induction values with
    | nil => intro store output run; cases run; exact ⟨rfl, rfl, rfl, rfl⟩
    | cons value rest ih =>
        intro store output run
        rw [List.foldlM_cons] at run
        cases head : retainShared store value with
        | error error => simp [head, bind, Except.bind] at run
        | ok middle =>
            simp only [head, bind, Except.bind] at run
            obtain ⟨firstRC, firstPotential, firstPeak, firstLive⟩ := retainShared_observations head
            obtain ⟨tailRC, tailPotential, tailPeak, tailLive⟩ := ih run
            simp only [referenceCountList]
            exact ⟨by omega, by omega, tailPeak.trans firstPeak, tailLive.trans firstLive⟩
  exact loop values.toList run

theorem releaseSharedWork_observations {fuel remaining : Nat}
    {store output : Store} {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    store.heap.rcops ≤ output.heap.rcops ∧ output.amortizedRC = store.amortizedRC ∧
    output.peakLiveNodes = store.peakLiveNodes ∧ output.live ≤ store.live := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact ⟨Nat.le_refl _, rfl, rfl, Nat.le_refl _⟩
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact ⟨Nat.le_refl _, rfl, rfl, Nat.le_refl _⟩
      | cons value rest =>
          cases value with
          | lit literal => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unitRC : box.rc = 1
                      · simp only [releaseSharedWork, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unitRC, beq_self_eq_true,
                          Nat.reduceBEq] at run
                        obtain ⟨rc, potential, peak, live⟩ := ih run
                        have conserved := amortizedRc_tickKillSharedOne
                          (store := store.heap) (location := location) (node := box.node)
                          (by rcases box with ⟨world, rc, node⟩
                              dsimp at shared unitRC; subst world; subst rc; exact found)
                        have removed := Store.live_kill (store := store.rcTick) found
                        refine ⟨?_, potential.trans ?_, peak, ?_⟩
                        · change store.heap.rcops + 1 ≤ output.heap.rcops at rc; omega
                        · simpa [Store.amortizedRC, Store.kill, Store.rcTick] using conserved
                        · change (store.rcTick.kill location).live + 1 = store.live at removed
                          omega
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        obtain ⟨rc, potential, peak, live⟩ := ih run
                        have conserved := amortizedRc_decRcStore
                          (store := store.heap) (location := location) (rc := box.rc)
                          (node := box.node) (by omega)
                          (by rcases box with ⟨world, rc, node⟩
                              dsimp at shared; subst world; exact found)
                        have unchanged := Store.live_setBox (store := store.rcTick)
                          (new := ⟨.shared, box.rc - 1, box.node⟩) found
                        refine ⟨?_, potential.trans ?_, peak, ?_⟩
                        · change store.heap.rcops + 1 ≤ output.heap.rcops at rc; omega
                        · simpa [Store.amortizedRC, IxIR1.Sim.decRcStore, Store.setBox,
                            Store.rcTick] using conserved
                        · change (store.rcTick.setBox location _).live = store.live at unchanged
                          omega
                  · simp [releaseSharedWork, found, shared] at run

theorem releaseShared_observations {fuel remaining : Nat} {store output : Store} {value : RVal}
    (run : releaseShared fuel store value = .ok (output, remaining)) :
    store.heap.rcops ≤ output.heap.rcops ∧ output.amortizedRC = store.amortizedRC ∧
    output.peakLiveNodes = store.peakLiveNodes ∧ output.live ≤ store.live :=
  releaseSharedWork_observations run

theorem dropUniqueWork_observations {fuel remaining : Nat}
    {store output : Store} {values : List RVal}
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) :
    output.heap.rcops = store.heap.rcops ∧ output.amortizedRC = store.amortizedRC ∧
    output.peakLiveNodes = store.peakLiveNodes ∧ output.live ≤ store.live := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
      | cons value rest =>
          cases value with
          | lit literal => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  by_cases unique : box.world = .unique
                  · cases node : box.node with
                    | papN address arity captured => simp [dropUniqueWork, found, unique, node] at run
                    | ctorN cid fields =>
                        simp only [dropUniqueWork, found, unique, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, node] at run
                        obtain ⟨rc, potential, peak, live⟩ := ih run
                        have conserved := amortizedRc_killUnique
                          (store := store.heap) (location := location) (rc := box.rc)
                          (node := box.node)
                          (by rcases box with ⟨world, rc, node⟩
                              dsimp at unique; subst world; exact found)
                        have removed := Store.live_kill found
                        refine ⟨rc, potential.trans ?_, peak, by omega⟩
                        simpa [Store.amortizedRC, Store.kill] using conserved
                  · simp [dropUniqueWork, found, unique] at run

theorem dropUnique_observations {fuel remaining : Nat} {store output : Store} {value : RVal}
    (run : dropUnique fuel store value = .ok (output, remaining)) :
    output.heap.rcops = store.heap.rcops ∧ output.amortizedRC = store.amortizedRC ∧
    output.peakLiveNodes = store.peakLiveNodes ∧ output.live ≤ store.live :=
  dropUniqueWork_observations run

@[simp] theorem Store.amortizedRC_tickResetAttempt (store : Store) :
    store.tickResetAttempt.amortizedRC = store.amortizedRC := rfl

@[simp] theorem Store.amortizedRC_tickHotReset (store : Store) :
    store.tickHotReset.amortizedRC = store.amortizedRC := rfl

@[simp] theorem Store.amortizedRC_tickColdReset (store : Store) :
    store.tickColdReset.amortizedRC = store.amortizedRC := rfl

theorem Store.amortizedRC_kill {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) :
    (store.kill location).amortizedRC + slotSharedRcPotential (some box) =
      store.amortizedRC := by
  have removed := sharedRcPotential_kill (store := store.heap) found
  unfold Store.amortizedRC amortizedRc
  change store.heap.rcops + sharedRcPotential (store.heap.kill location) + _ = _
  omega

theorem Store.amortizedRC_reserve {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) :
    (store.reserve location).amortizedRC + slotSharedRcPotential (some box) =
      store.amortizedRC := by
  have removed := Store.amortizedRC_kill found
  simpa [Store.amortizedRC, amortizedRc, sharedRcPotential, Store.reserve,
    Store.kill, IxIR1.Store.kill, IxIR1.Store.setBox] using removed

theorem Store.amortizedRC_decrement {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) (shared : box.world = .shared)
    (many : 1 < box.rc) :
    ((store.setBox location { box with rc := box.rc - 1 }).rcTick).amortizedRC =
      store.amortizedRC := by
  have changed := sharedRcPotential_setBox (store := store.heap)
    (new := { box with rc := box.rc - 1 }) found
  have slot : slotSharedRcPotential (some box) = box.rc := by
    rcases box with ⟨world, rc, node⟩
    dsimp at shared
    subst world
    rfl
  rw [slot] at changed
  simp only [slotSharedRcPotential, shared] at changed
  unfold Store.amortizedRC amortizedRc
  change store.heap.rcops + 1 + sharedRcPotential (store.heap.setBox location _) = _
  simp only [shared]
  omega

theorem Store.releaseReservation_observations {store output : Store} {location : Nat}
    (run : store.releaseReservation location = .ok output) :
    output.heap.rcops = store.heap.rcops ∧ output.amortizedRC = store.amortizedRC ∧
    output.peakLiveNodes = store.peakLiveNodes ∧ output.live = store.live := by
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.releaseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.releaseReservation, found] at run
      | none =>
          simp only [Store.releaseReservation, found, Except.ok.injEq] at run
          subst output
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem Store.reuseReservation_observations {store output : Store}
    {location payloadUnits : Nat} {world : Owned} {node : Node}
    (run : store.reuseReservation location world node payloadUnits = .ok output) :
    output.heap.rcops = store.heap.rcops ∧
    output.amortizedRC = store.amortizedRC + (if world = .shared then 1 else 0) ∧
    output.peakLiveNodes = max store.peakLiveNodes output.live ∧
    output.live = store.live + 1 := by
  have live := (Store.reuseReservation_accounting run).1
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.reuseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.reuseReservation, found] at run
      | none =>
          simp only [Store.reuseReservation, found, Except.ok.injEq] at run
          subst output
          refine ⟨rfl, ?_, rfl, live⟩
          have changed := sharedRcPotentialList_set
            (new := some (NodeBox.mk world 1 node))
            (show store.heap.nodes.toList[location]? = some none by simpa using found)
          cases world <;>
            simp only [slotSharedRcPotential, Nat.add_zero] at changed <;>
            simp [Store.amortizedRC, amortizedRc, sharedRcPotential, changed,
              Array.toList_setIfInBounds, Nat.add_assoc]

/-- RC work performed by dynamic application, including the outstanding
references it creates. Deep release is already included by conservation. -/
def applyRCCharge (store : Store) (function : RVal) (arguments : Array RVal) : Int :=
  match function with
  | .loc location =>
      match store.get? location with
      | some box =>
          match box.node with
          | .papN _ _ captured =>
              2 * (referenceCountList captured.toList : Int) +
                (applyAllocationEvents store function arguments : Int)
          | _ => 0
      | none => 0
  | _ => 0

theorem applyRCCharge_history {baseline rewritten : Store}
    (heap : IxIR1.Sim.HeapHistoryIso baseline.heap rewritten.heap)
    {baselineFunction rewrittenFunction : RVal}
    {baselineArguments rewrittenArguments : Array RVal}
    (function : IxIR1.Sim.RValIso heap.locRel baselineFunction rewrittenFunction)
    (argumentCount : baselineArguments.size = rewrittenArguments.size) :
    applyRCCharge baseline baselineFunction baselineArguments =
      applyRCCharge rewritten rewrittenFunction rewrittenArguments := by
  have allocations := applyAllocationEvents_history heap function argumentCount
  cases function with
  | lit => rfl
  | erased => rfl
  | loc locations =>
      rcases heap.related locations with ⟨leftDead, rightDead⟩ |
        ⟨leftBox, rightBox, leftAt, rightAt, boxes⟩
      · simp [applyRCCharge, Store.get?, leftDead, rightDead]
      · simp only [applyRCCharge, Store.get?, leftAt, rightAt]
        have nodes := boxes.node
        generalize leftBox.node = leftNode at nodes ⊢
        generalize rightBox.node = rightNode at nodes ⊢
        cases nodes with
        | ctor fields => rfl
        | pap captured => simp only [referenceCountList_iso captured, allocations]

theorem ApplyTransferCase.rcCharge {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) :
    (target.store.amortizedRC : Int) = store.amortizedRC +
      applyRCCharge store function arguments := by
  cases classified with
  | erased released =>
      have conserved := (releaseSharedWork_observations released).2.1
      simpa only [applyRCCharge, Int.add_zero] using congrArg (fun n : Nat => (n : Int)) conserved
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      have first := retained.observations.2.1
      have second := (releaseSharedWork_observations released).2.1
      simp only [applyRCCharge, boxAt, node, applyAllocationEvents, totalUnder,
        ↓reduceIte, Store.amortizedRC_allocNode, Int.natCast_add]
      omega
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      have first := retained.observations.2.1
      have second := (releaseSharedWork_observations released).2.1
      simp only [applyRCCharge, boxAt, node, applyAllocationEvents,
        Nat.not_lt.mpr totalEnough, ↓reduceIte, Int.natCast_zero, Int.add_zero]
      omega
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      have first := retained.observations.2.1
      have second := (releaseSharedWork_observations released).2.1
      simp only [applyRCCharge, boxAt, node, applyAllocationEvents,
        Nat.not_lt.mpr totalEnough, ↓reduceIte, Int.natCast_zero, Int.add_zero]
      omega

theorem ApplyTransferCase.peakLive {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) :
    target.store.peakLiveNodes =
      if applyAllocationEvents store function arguments = 0 then store.peakLiveNodes
      else max store.peakLiveNodes target.store.live := by
  cases classified with
  | erased released => exact (releaseSharedWork_observations released).2.2.1
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      have first := retained.observations.2.2.1
      have second := (releaseSharedWork_observations released).2.2.1
      simp only [applyAllocationEvents, boxAt, node, totalUnder, ↓reduceIte,
        Nat.one_ne_zero, Store.peakLive_allocNode, second, first]
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      have first := retained.observations.2.2.1
      have second := (releaseSharedWork_observations released).2.2.1
      simp only [applyAllocationEvents, boxAt, node, Nat.not_lt.mpr totalEnough,
        ↓reduceIte, second, first]
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      have first := retained.observations.2.2.1
      have second := (releaseSharedWork_observations released).2.2.1
      simp only [applyAllocationEvents, boxAt, node, Nat.not_lt.mpr totalEnough,
        ↓reduceIte, second, first]

theorem ApplyTransferCase.live_le {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) :
    target.store.live ≤ store.live + applyAllocationEvents store function arguments := by
  cases classified with
  | erased released => exact (releaseSharedWork_observations released).2.2.2
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      have first := retained.observations.2.2.2
      have second := (releaseSharedWork_observations released).2.2.2
      simp only [applyAllocationEvents, boxAt, node, totalUnder, ↓reduceIte,
        Store.live_allocNode]
      omega
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      have first := retained.observations.2.2.2
      have second := (releaseSharedWork_observations released).2.2.2
      simp only [applyAllocationEvents, boxAt, node, Nat.not_lt.mpr totalEnough,
        ↓reduceIte, Nat.add_zero]
      omega
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      have first := retained.observations.2.2.2
      have second := (releaseSharedWork_observations released).2.2.2
      simp only [applyAllocationEvents, boxAt, node, Nat.not_lt.mpr totalEnough,
        ↓reduceIte, Nat.add_zero]
      omega

theorem ApplyTransfer.rcCharge {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) :
    (target.store.amortizedRC : Int) = store.amortizedRC +
      applyRCCharge store function arguments := transferred.classify.rcCharge

theorem ApplyTransfer.peakLive {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) :
    target.store.peakLiveNodes =
      if applyAllocationEvents store function arguments = 0 then store.peakLiveNodes
      else max store.peakLiveNodes target.store.live := transferred.classify.peakLive

theorem ApplyTransfer.live_le {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) :
    target.store.live ≤ store.live + applyAllocationEvents store function arguments :=
  transferred.classify.live_le

theorem ApplyTransfer.rcops_mono {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) : store.heap.rcops ≤ target.store.heap.rcops := by
  cases transferred.classify with
  | erased released => exact (releaseSharedWork_observations released).1
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      have first := retained.observations.1
      have second := (releaseSharedWork_observations released).1
      simp only [Store.rcops_allocNode]
      omega
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      have first := retained.observations.1
      have second := (releaseSharedWork_observations released).1
      dsimp only
      omega
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      have first := retained.observations.1
      have second := (releaseSharedWork_observations released).1
      dsimp only
      omega

end Ix.Compiler.IxIR2.Eval
