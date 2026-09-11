import Ix.Compiler.IxIR2.CreditHeapObservations
import Ix.Compiler.IxIR2.CallReuseOrder

/-! Heap operations with exact logical/physical cost agreement. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso NodeIso NodeBoxIso)
open CallReuse.Sim (MapRel HeapMap Ordered)
open Ix.Compiler.IxIR1.Reclamation (AllocationOrderInvariant)

/-- Reuse changes fresh allocation and free counts. Allocation events, RC,
peak live nodes, and reset decisions agree throughout execution. -/
structure HeapRel (mapping : Array Nat) (left right : Store) : Prop where
  heap : HeapMap left right mapping
  events : left.allocationEvents = right.allocationEvents
  rcops : left.heap.rcops = right.heap.rcops
  peak : left.peakLiveNodes = right.peakLiveNodes
  attempts : left.resetAttempts = right.resetAttempts
  hot : left.hotResets = right.hotResets
  cold : left.coldResets = right.coldResets
  ordered : Ordered left

theorem HeapRel.empty : HeapRel #[] ({} : Store) ({} : Store) :=
  ⟨.empty, rfl, rfl, rfl, rfl, rfl, rfl, .empty⟩

theorem HeapRel.passive {mapping : Array Nat} {left right leftOut rightOut : Store}
    (state : HeapRel mapping left right) (heap : HeapMap leftOut rightOut mapping)
    (leftPassive : passiveCounters leftOut = passiveCounters left)
    (rightPassive : passiveCounters rightOut = passiveCounters right)
    (rcops : leftOut.heap.rcops = rightOut.heap.rcops) (ordered : Ordered leftOut) :
    HeapRel mapping leftOut rightOut := by
  have eventsLeft := congrArg (fun c => c.allocs + c.reuses) leftPassive
  have eventsRight := congrArg (fun c => c.allocs + c.reuses) rightPassive
  refine ⟨heap, eventsLeft.trans (state.events.trans eventsRight.symm), rcops, ?_, ?_, ?_, ?_, ordered⟩
  · exact (congrArg Counters.peakLiveNodes leftPassive).trans
      (state.peak.trans (congrArg Counters.peakLiveNodes rightPassive).symm)
  · exact (congrArg Counters.resetAttempts leftPassive).trans
      (state.attempts.trans (congrArg Counters.resetAttempts rightPassive).symm)
  · exact (congrArg Counters.hotResets leftPassive).trans
      (state.hot.trans (congrArg Counters.hotResets rightPassive).symm)
  · exact (congrArg Counters.coldResets leftPassive).trans
      (state.cold.trans (congrArg Counters.coldResets rightPassive).symm)

theorem HeapRel.alloc {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) {world : Owned} {leftNode rightNode : Node}
    (nodes : NodeIso (MapRel mapping) leftNode rightNode) :
    HeapRel (mapping.push right.heap.nodes.size)
      (left.allocNode world leftNode).1 (right.allocNode world rightNode).1 := by
  have heap := state.heap.alloc (world := world) nodes
  refine ⟨heap, by simp only [Store.allocationEvents_allocNode, state.events],
    state.rcops, ?_, state.attempts, state.hot, state.cold, state.ordered.alloc state.heap nodes⟩
  simp only [Store.peakLive_allocNode, state.peak, heap.live_eq]

theorem HeapRel.kill {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) {l r : Nat} {box : NodeBox}
    (mapped : MapRel mapping l r) (found : left.get? l = some box) :
    HeapRel mapping (left.kill l) (right.kill r) :=
  ⟨state.heap.kill mapped found, state.events, state.rcops, state.peak,
    state.attempts, state.hot, state.cold, AllocationOrderInvariant.kill state.ordered found⟩

theorem HeapRel.reserve {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) {l r : Nat} {box : NodeBox}
    (mapped : MapRel mapping l r) (found : left.get? l = some box) :
    HeapRel mapping (left.kill l) (right.reserve r) :=
  ⟨state.heap.reserve mapped found, state.events, state.rcops, state.peak,
    state.attempts, state.hot, state.cold, AllocationOrderInvariant.kill state.ordered found⟩

theorem HeapRel.setBox {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) {l r : Nat} {old newLeft newRight : NodeBox}
    (mapped : MapRel mapping l r) (found : left.get? l = some old)
    (boxes : NodeBoxIso (MapRel mapping) newLeft newRight)
    (ordered : Ordered (left.setBox l newLeft)) :
    HeapRel mapping (left.setBox l newLeft) (right.setBox r newRight) :=
  ⟨state.heap.setBox mapped found boxes, state.events, state.rcops, state.peak,
    state.attempts, state.hot, state.cold, ordered⟩

theorem HeapRel.rcTick {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) : HeapRel mapping left.rcTick right.rcTick :=
  ⟨state.heap.rcTick, state.events, congrArg (· + 1) state.rcops, state.peak,
    state.attempts, state.hot, state.cold, AllocationOrderInvariant.rcTick state.ordered⟩

theorem HeapRel.tickAttempt {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) :
    HeapRel mapping left.tickResetAttempt right.tickResetAttempt :=
  ⟨state.heap.congr rfl rfl, state.events, state.rcops, state.peak,
    congrArg (· + 1) state.attempts, state.hot, state.cold, state.ordered⟩

theorem HeapRel.tickHot {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) :
    HeapRel mapping left.tickHotReset right.tickHotReset :=
  ⟨state.heap.congr rfl rfl, state.events, state.rcops, state.peak,
    state.attempts, congrArg (· + 1) state.hot, state.cold, state.ordered⟩

theorem HeapRel.tickCold {mapping : Array Nat} {left right : Store}
    (state : HeapRel mapping left right) :
    HeapRel mapping left.tickColdReset right.tickColdReset :=
  ⟨state.heap.congr rfl rfl, state.events, state.rcops, state.peak,
    state.attempts, state.hot, congrArg (· + 1) state.cold, state.ordered⟩

theorem HeapRel.reuse {mapping : Array Nat} {left right rightOut : Store}
    (state : HeapRel mapping left right) {location payload : Nat} {world : Owned}
    {leftNode rightNode : Node} (nodes : NodeIso (MapRel mapping) leftNode rightNode)
    (run : right.reuseReservation location world rightNode payload = .ok rightOut) :
    HeapRel (mapping.push location) (left.allocNode world leftNode).1 rightOut := by
  have heap := state.heap.reuse nodes run
  have observed := Store.reuseReservation_observations run
  have events := Store.reuseReservation_allocationEvents run
  refine ⟨heap, by rw [Store.allocationEvents_allocNode, events, state.events],
    state.rcops.trans observed.1.symm, ?_, ?_, ?_, ?_, state.ordered.alloc state.heap nodes⟩
  · rw [Store.peakLive_allocNode, observed.2.2.1, state.peak, heap.live_eq]
  all_goals
    unfold Store.reuseReservation at run
    split at run
    · cases run
      first | exact state.attempts | exact state.hot | exact state.cold
    · cases run

theorem HeapRel.discard {mapping : Array Nat} {left right rightOut : Store}
    (state : HeapRel mapping left right) {location : Nat}
    (run : right.releaseReservation location = .ok rightOut) :
    HeapRel mapping left rightOut := by
  unfold Store.releaseReservation at run
  split at run
  · cases run
    exact ⟨state.heap.congr rfl rfl, state.events, state.rcops, state.peak,
      state.attempts, state.hot, state.cold, state.ordered⟩
  · cases run

theorem HeapRel.retain {mapping : Array Nat} {left right leftOut : Store}
    (state : HeapRel mapping left right) {leftValue rightValue : RVal}
    (values : RValIso (MapRel mapping) leftValue rightValue)
    (run : retainShared left leftValue = .ok leftOut) :
    ∃ rightOut, retainShared right rightValue = .ok rightOut ∧ HeapRel mapping leftOut rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.retain values run
  refine ⟨rightOut, targetRun, state.passive heap (retain_passive run)
    (retain_passive targetRun) ?_ (state.ordered.retain run)⟩
  have leftRC := (retainShared_observations run).1
  have rightRC := (retainShared_observations targetRun).1
  have refs : referenceCount leftValue = referenceCount rightValue := by cases values <;> rfl
  rw [leftRC, rightRC, state.rcops, refs]

theorem HeapRel.retainMany {mapping : Array Nat} {left right leftOut : Store}
    (state : HeapRel mapping left right) {leftValues rightValues : Array RVal}
    (values : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    (run : RetainSharedMany left leftValues leftOut) :
    ∃ rightOut, RetainSharedMany right rightValues rightOut ∧ HeapRel mapping leftOut rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.retainMany values run
  refine ⟨rightOut, targetRun, state.passive heap (retainMany_passive run)
    (retainMany_passive targetRun) ?_ (state.ordered.retainMany run)⟩
  rw [run.observations.1, targetRun.observations.1, state.rcops, referenceCountList_iso values]

theorem HeapRel.releaseWork {mapping : Array Nat} {left right leftOut : Store}
    (state : HeapRel mapping left right) {fuel remaining : Nat}
    {leftValues rightValues : List RVal} (values : RValsIso (MapRel mapping) leftValues rightValues)
    (run : releaseSharedWork fuel left leftValues = .ok (leftOut, remaining)) :
    ∃ rightOut, releaseSharedWork fuel right rightValues = .ok (rightOut, remaining) ∧
      HeapRel mapping leftOut rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.releaseWork values run
  refine ⟨rightOut, targetRun, state.passive heap (releaseWork_passive run)
    (releaseWork_passive targetRun) ?_ (state.ordered.releaseWork run)⟩
  have beforePending := state.heap.pendingRC_eq
  have afterPending := heap.pendingRC_eq
  have leftRC := (releaseSharedWork_observations run).2.1
  have rightRC := (releaseSharedWork_observations targetRun).2.1
  change leftOut.heap.rcops + leftOut.pendingRC = left.heap.rcops + left.pendingRC at leftRC
  change rightOut.heap.rcops + rightOut.pendingRC = right.heap.rcops + right.pendingRC at rightRC
  have initial := state.rcops
  omega

theorem HeapRel.dropWork {mapping : Array Nat} {left right leftOut : Store}
    (state : HeapRel mapping left right) {fuel remaining : Nat}
    {leftValues rightValues : List RVal} (values : RValsIso (MapRel mapping) leftValues rightValues)
    (run : dropUniqueWork fuel left leftValues = .ok (leftOut, remaining)) :
    ∃ rightOut, dropUniqueWork fuel right rightValues = .ok (rightOut, remaining) ∧
      HeapRel mapping leftOut rightOut := by
  obtain ⟨rightOut, targetRun, heap⟩ := state.heap.dropWork values run
  exact ⟨rightOut, targetRun, state.passive heap (dropWork_passive run)
    (dropWork_passive targetRun) ((dropUniqueWork_observations run).1.trans
      (state.rcops.trans (dropUniqueWork_observations targetRun).1.symm))
    (state.ordered.dropWork run)⟩

end Ix.Compiler.IxIR2.CreditRefinement
