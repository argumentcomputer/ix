import Compilatrix.X86.PhysicalHeapPrimitiveReuse

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros HeapPrimitives
open IxIR2.Eval (Store RVal Credit)

def releaseStore (world : Ixon.Owned) (store : Store) : Store :=
  if world == .shared then store.rcTick else store

@[simp] theorem releaseStore_nodes (world : Ixon.Owned) (store : Store) : (releaseStore world store).heap.nodes = store.heap.nodes := by
  cases world <;> rfl

theorem HeapAt.sharedRelease {schemas constructors offset store reserved} {state : State}
    (related : HeapAt schemas constructors offset store reserved state.words) (world : Ixon.Owned) :
    HeapAt schemas constructors offset (releaseStore world store) reserved (HeapPrimitives.sharedRelease world state).words := by
  cases world with
  | unique => exact related
  | shared => exact related.rcTick

theorem primitive_free {schemas constructors layout offset store reserved frame scope nextScope values credits state world source operand location}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (taken : scope.take source = .ok (.node, operand, nextScope))
    (resolved : IxIR2.Eval.resolveAtom values source = .ok (.loc location)) :
    let after := release frame state (location - offset) world operand
    let output := releaseStore world (store.kill location)
    Executes layout frame (.release world operand) state after ∧
      HeapAt schemas constructors offset output reserved after.words ∧
      ScopeAt layout offset (output.heap.nodes.size - offset) frame nextScope values credits after := by
  obtain ⟨remaining, above, below, pointer⟩ := locals.takeNode taken resolved
  have bound : location < store.heap.nodes.size := by have := heap.extent; omega
  have allocated : location - offset < capacity := by have := heap.bounded; have := heap.extent; omega
  let loaded := load frame state operand
  let killed := freeState loaded (location - offset) false
  have loadedHeap : HeapAt schemas constructors offset store reserved loaded.words := heap
  have killedHeap : HeapAt schemas constructors offset (store.kill location) reserved killed.words :=
    loadedHeap.kill above bound (fun _ _ member => member) rfl
  have loadedLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame nextScope values credits loaded :=
    remaining.setReg .rax (HeapCopies.atomValue frame state operand)
  have killedLocals := loadedLocals.heap separate (fun _ upper => freeState_heap loaded allocated false upper)
  refine ⟨.release state _ world operand allocated pointer, killedHeap.sharedRelease world, ?_⟩
  simpa only [release, releaseStore_nodes, Store.kill, IxIR1.Store.kill, Array.size_set!, Array.size_setIfInBounds,
    killed, freeState, Bool.false_eq_true, ↓reduceIte, loaded] using killedLocals.sharedRelease separate world

theorem primitive_discard {schemas constructors layout offset store output reserved outReserved frame scope nextScope values credits state index id credit location}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (taken : scope.takeCredit index = .ok (id, nextScope))
    (found : credits[index]? = some (some credit))
    (present : credit.presence = .present (some location))
    (released : store.releaseReservation location = .ok output)
    (kept : ∀ other, other ≠ location → other ∈ reserved → other ∈ outReserved)
    (count : outReserved.length + 1 = reserved.length) :
    let after := discard frame state (location - offset) index
    Executes layout frame (.discard index) state after ∧
      HeapAt schemas constructors offset output outReserved after.words ∧
      ScopeAt layout offset (output.heap.nodes.size - offset) frame nextScope values
        (credits.setIfInBounds index none) after := by
  obtain ⟨remaining, above, below, pointer⟩ := locals.takeCreditLocation taken found present
  have bound : location < store.heap.nodes.size := by have := heap.extent; omega
  have allocated : location - offset < capacity := by have := heap.bounded; have := heap.extent; omega
  have outputEq := releaseReservation_kill released
  subst output
  let loaded := creditState frame state index
  have loadedHeap : HeapAt schemas constructors offset store reserved loaded.words := heap
  have afterHeap := loadedHeap.kill (consume := true) above bound kept count
  have loadedLocals : ScopeAt layout offset (store.heap.nodes.size - offset) frame nextScope values
      (credits.setIfInBounds index none) loaded := remaining.words (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have afterLocals := loadedLocals.heap separate (fun _ upper => freeState_heap loaded allocated true upper)
  refine ⟨.discard state _ index allocated pointer, afterHeap, ?_⟩
  simpa only [HeapPrimitives.discard, freeState, loaded, ↓reduceIte, Store.kill, IxIR1.Store.kill, Array.size_set!, Array.size_setIfInBounds] using afterLocals

end Compilatrix.X86.PhysicalHeap
