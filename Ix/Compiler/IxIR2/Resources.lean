import Ix.Compiler.IxIR2.HeapAccounting

/-!
# Resource accounting for actual physical executions

Every allocated slot is either live, freed, or represented by a present credit
in the current frame or its continuations. Successful physical steps preserve
this balance. A successful main execution therefore has no outstanding
allocation beyond its live heap; reclamation reduces that heap to zero.
-/

namespace Ix.Compiler.IxIR2.Eval

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1 (Node NodeBox RVal)

/-- Allocation accounting includes reservations held anywhere in the machine. -/
def Machine.AllocationAccounting (machine : Machine) : Prop :=
  machine.store.live + machine.store.heap.frees + machine.presentCredits =
    machine.store.heap.allocs

theorem Machine.AllocationAccounting.of_heapBalance {before after : Machine}
    (accounted : before.AllocationAccounting)
    (balanced : HeapBalance before.store after.store)
    (credits : after.presentCredits = before.presentCredits) :
    after.AllocationAccounting := by
  unfold Machine.AllocationAccounting at *
  unfold HeapBalance at balanced
  omega

theorem ApplyTransferCase.allocationAccounting {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {arguments : Array RVal} {resume : Frame} {stack : List Continuation}
    {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target)
    (accounted : (Machine.mk store heapFuel (.running resume stack)).AllocationAccounting) :
    target.AllocationAccounting := by
  cases classified with
  | erased released =>
      exact accounted.of_heapBalance (releaseSharedWork_heapBalance released) rfl
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      exact accounted.of_heapBalance
        ((retained.heapBalance.trans (releaseSharedWork_heapBalance released)).trans
          (.allocNode ..)) rfl
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      refine accounted.of_heapBalance ?_ ?_
      · exact retained.heapBalance.trans (releaseSharedWork_heapBalance released)
      simp only [Machine.presentCredits_running, List.map_cons, List.sum_cons,
        Frame.presentCredits, creditPresentCount_empty, Nat.zero_add]
      split <;> rfl
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      exact accounted.of_heapBalance
        (retained.heapBalance.trans (releaseSharedWork_heapBalance released)) rfl

theorem ApplyTransfer.allocationAccounting {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {arguments : Array RVal} {resume : Frame} {stack : List Continuation}
    {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target)
    (accounted : (Machine.mk store heapFuel (.running resume stack)).AllocationAccounting) :
    target.AllocationAccounting := transferred.classify.allocationAccounting accounted

theorem InstructionTransferCase.allocationAccounting {context : Context}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context .physical store heapFuel frame
      stack instruction target)
    (accounted : (Machine.mk store heapFuel (.running frame stack)).AllocationAccounting) :
    target.AllocationAccounting := by
  cases classified with
  | move resolved => exact accounted
  | alloc schemaAt resolved fields =>
      exact accounted.of_heapBalance (.allocNode ..) rfl
  | allocWithAbsent schemaAt resolved fields taken layout absent =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .allocNode ..
      have count := taken.presentCredits
      simpa [Machine.presentCredits_running, Frame.presentCredits,
        Credit.weight_absent absent] using
        congrArg (· + (stack.map Continuation.presentCredits).sum) count
  | allocWithLogical mode => cases mode
  | allocWithPhysical mode schemaAt resolved fields taken layout present reused =>
      have count := taken.presentCredits
      have heap := Store.reuseReservation_accounting reused
      simp only [Frame.presentCredits, Credit.weight_present present] at count
      simp only [Machine.AllocationAccounting, Machine.presentCredits_running,
        Frame.presentCredits] at accounted ⊢
      omega
  | discardAbsent taken absent =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      have count := taken.presentCredits
      simpa [Machine.presentCredits_running, Frame.presentCredits,
        Credit.weight_absent absent] using
        congrArg (· + (stack.map Continuation.presentCredits).sum) count
  | discardLogical mode => cases mode
  | discardPhysical mode taken present released =>
      have count := taken.presentCredits
      have heap := Store.releaseReservation_accounting released
      simp only [Frame.presentCredits, Credit.weight_present present] at count
      simp only [Machine.AllocationAccounting, Machine.presentCredits_running,
        Frame.presentCredits] at accounted ⊢
      omega
  | takeUniqueLogical mode => cases mode
  | takeUniquePhysical mode schemaAt resolved viewed unitRC =>
      have live := Store.live_reserve viewed.parts.1
      simp only [Machine.AllocationAccounting, Machine.presentCredits_running,
        Frame.presentCredits, creditPresentCount_push, Credit.weight,
        Credit.isPresent] at accounted ⊢
      change _ + _ + (_ + (if true then 1 else 0) + _) = _
      simp only [↓reduceIte]
      change _ + store.heap.frees + _ = store.heap.allocs
      omega
  | resetSharedLogicalHot mode => cases mode
  | resetSharedPhysicalHot mode schemaAt resolved viewed unitRC =>
      have live := Store.live_reserve viewed.parts.1
      simp only [Machine.AllocationAccounting, Machine.presentCredits_running,
        Frame.presentCredits, creditPresentCount_push, Credit.weight,
        Credit.isPresent] at accounted ⊢
      change (store.reserve _).live + store.heap.frees +
        (creditPresentCount frame.credits + 1 + _) = store.heap.allocs
      omega
  | @resetSharedCold target cid schema location box fields outStore
      schemaAt resolved viewed shared retained =>
      have updated := HeapBalance.setBox (new := { box with rc := box.rc - 1 }) viewed.parts.1
      have balanced : HeapBalance store outStore := updated.trans retained.heapBalance
      refine accounted.of_heapBalance ?_ ?_
      · exact balanced
      simp [Machine.presentCredits_running, Frame.presentCredits,
        Credit.weight, Credit.isPresent]
  | retainShared resolved retained =>
      exact accounted.of_heapBalance (retainShared_heapBalance retained) rfl
  | releaseShared resolved released =>
      exact accounted.of_heapBalance (releaseShared_heapBalance released) rfl
  | dropUnique resolved dropped =>
      exact accounted.of_heapBalance (dropUnique_heapBalance dropped) rfl
  | freeUnique resolved viewed scalarFields =>
      exact accounted.of_heapBalance (.kill viewed.parts.1) rfl
  | fetch resolved boxAt node fieldAt => exact accounted
  | callFn noCredits resolved declaration arity nonempty =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp [Machine.presentCredits_running, Frame.presentCredits,
        Continuation.presentCredits]
  | callSelf noCredits resolved arity nonempty =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp [Machine.presentCredits_running, Frame.presentCredits,
        Continuation.presentCredits]
  | pappFn noCredits declaration papSafe resolved under =>
      exact accounted.of_heapBalance (.allocNode ..) rfl
  | pappExtern noCredits declaration resolved under =>
      exact accounted.of_heapBalance (.allocNode ..) rfl
  | apply noCredits functionResolved argumentsResolved transferred =>
      exact transferred.allocationAccounting accounted
  | extern noCredits resolved declaration argumentArity called => exact accounted

theorem TerminatorTransferCase.allocationAccounting {context : Context}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context .physical store heapFuel frame
      stack terminator target)
    (accounted : (Machine.mk store heapFuel (.running frame stack)).AllocationAccounting) :
    target.AllocationAccounting := by
  cases classified with
  | jump transferred =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp only [Machine.presentCredits_running, transferred.presentCredits]
  | switchCtor resolved boxAt node alternativeAt transferred =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp only [Machine.presentCredits_running, transferred.presentCredits]
  | switchNatZero resolved transferred =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp only [Machine.presentCredits_running, transferred.presentCredits]
  | switchNatSucc resolved transferred =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp only [Machine.presentCredits_running, transferred.presentCredits]
  | branchPresent lookedUp present transferred =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp only [Machine.presentCredits_running, transferred.presentCredits]
  | branchAbsent lookedUp absent transferred =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      simp only [Machine.presentCredits_running, transferred.presentCredits]
  | retResume resolved noCredits world =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      have cleared := noCredits.presentCredits
      change creditPresentCount frame.credits = 0 at cleared
      simp [Machine.presentCredits_running, Frame.presentCredits,
        Continuation.presentCredits, cleared]
  | retHalt resolved noCredits world =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      change 0 = frame.presentCredits + 0
      rw [noCredits.presentCredits]
  | retApplyMore resolved noCredits world transferred =>
      apply transferred.allocationAccounting
      simpa only [Machine.AllocationAccounting, Machine.presentCredits_running,
        List.map_cons, List.sum_cons, Continuation.presentCredits,
        noCredits.presentCredits, Nat.zero_add] using accounted
  | tailCallFn noCredits resolved declaration arity nonempty =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      have cleared := noCredits.presentCredits
      change creditPresentCount frame.credits = 0 at cleared
      simp [Machine.presentCredits_running, Frame.presentCredits, cleared]
  | tailCallSelf noCredits resolved arity nonempty =>
      refine accounted.of_heapBalance ?_ ?_
      · exact .refl _
      have cleared := noCredits.presentCredits
      change creditPresentCount frame.credits = 0 at cleared
      simp [Machine.presentCredits_running, Frame.presentCredits, cleared]

/-- Every actual successful physical step preserves allocation accounting. -/
theorem Step.allocationAccounting {context : Context} {before after : Machine}
    (stepped : Step context .physical before after)
    (accounted : before.AllocationAccounting) : after.AllocationAccounting := by
  cases stepped.classify with
  | halted => exact accounted
  | instruction blockAt pc instructionAt classified =>
      exact classified.allocationAccounting accounted
  | terminator blockAt pc terminatorAt classified =>
      exact classified.allocationAccounting accounted

theorem Steps.allocationAccounting {context : Context} {count : Nat}
    {before after : Machine} (steps : Steps context .physical count before after)
    (accounted : before.AllocationAccounting) : after.AllocationAccounting := by
  induction steps with
  | refl => exact accounted
  | cons running head tail ih => exact ih (head.allocationAccounting accounted)

/-- A successful physical runner has accounted for every reservation at halt. -/
theorem runMachine_allocationAccounting {context : Context} {controlFuel : Nat}
    {machine : Machine} {result : Result}
    (run : runMachine context .physical controlFuel machine = .ok result)
    (accounted : machine.AllocationAccounting) :
    result.store.live + result.store.heap.frees = result.store.heap.allocs := by
  obtain ⟨count, budget, steps⟩ := runMachine_steps run
  simpa [Machine.AllocationAccounting, Machine.presentCredits] using
    steps.allocationAccounting accounted

theorem initialMachine_allocationAccounting (definition : Function)
    (arguments : Array RVal) (heapFuel : Nat) :
    (initialMachine definition arguments heapFuel).AllocationAccounting := rfl

/-- The successful physical main has no outstanding allocation beyond its live
nodes. The entry facts are checked by the evaluator and also certified by the
compiler attachment. -/
theorem runMain_allocationAccounting {context : Context} {program : Program}
    {controlFuel heapFuel : Nat} {result : Result}
    (arity : program.main.signature.params.size = 0)
    (nonempty : program.main.blocks.isEmpty = false)
    (run : runMain context .physical program controlFuel heapFuel = .ok result) :
    result.store.live + result.store.heap.frees = result.store.heap.allocs := by
  rw [runMain_eq_runMachine arity nonempty] at run
  exact runMachine_allocationAccounting run (initialMachine_allocationAccounting ..)

/-- Terminal resource contract for a shared result: the main has no unaccounted
reservation, and releasing its returned root empties the heap and balances all
fresh allocations with frees. Release fuel is independent of execution fuel. -/
def Result.SharedResources (result : Result) : Prop :=
  result.store.live + result.store.heap.frees = result.store.heap.allocs ∧
    ∃ releaseFuel released remaining,
      releaseShared releaseFuel result.store result.value = .ok (released, remaining) ∧
      released.live = 0 ∧ released.heap.allocs = released.heap.frees

theorem Result.sharedResources_of_release {result : Result}
    (accounted : result.store.live + result.store.heap.frees = result.store.heap.allocs)
    {releaseFuel remaining : Nat} {released : Store}
    (release : releaseShared releaseFuel result.store result.value = .ok (released, remaining))
    (empty : released.live = 0) : result.SharedResources := by
  have balance := releaseShared_heapBalance release
  unfold HeapBalance at balance
  exact ⟨accounted, releaseFuel, released, remaining, release, empty, by omega⟩

end Ix.Compiler.IxIR2.Eval
