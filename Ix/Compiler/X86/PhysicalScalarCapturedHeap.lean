import Ix.Compiler.X86.PhysicalScalarSourceHeap

namespace Ix.Compiler.X86.PhysicalScalar.Captured

def emptyHeap (store : IxIR1.Store) : Prop := ∀ location, store.get? location = none

theorem emptyHeap.nodes {store : IxIR1.Store} (empty : emptyHeap store) :
    store.nodes = Array.replicate store.nodes.size none := by
  apply Array.ext
  · simp
  · intro index small _
    have absent := empty index
    cases slot : store.nodes[index] with
    | none => simp
    | some box => simp [IxIR1.Store.get?, Array.getElem?_eq_getElem small, slot] at absent

theorem emptyHeap.renamed {store : IxIR1.Store} (empty : emptyHeap store) (rename : Ixon.Address → Ixon.Address) :
    IxIR1.Readdress.Store.mapAddresses rename store = store := by
  cases store with
  | mk nodes allocs reuses frees rcops =>
      have shape := empty.nodes
      simp only at shape
      simp only [IxIR1.Readdress.Store.mapAddresses]
      congr 1
      conv => lhs; rw [shape]
      simpa only [Array.map_replicate, Option.map_none] using shape.symm

theorem emptyHeap.runtime {store : IxIR1.Store} (empty : emptyHeap store) (values : Array Word) :
    IxIR2.Lower.Sim.SourceRuntimeInvariant store (values.map rval).toList.reverse := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_⟩⟩
  · intro location box found
    simp [empty location] at found
  · intro parent box child found
    simp [empty parent] at found
  · intro value member
    simp only [List.mem_reverse, Array.toList_map, List.mem_map] at member
    obtain ⟨word, _, rfl⟩ := member
    trivial
  · intro location world rc address arity captured found
    simp [empty location] at found

theorem emptyHeap.image {store : IxIR1.Store} (empty : emptyHeap store)
    {world fuel} (attached : IxIR2.Pipeline.CompiledAttachment world fuel) : attached.SourceStoreImage store := by
  refine ⟨store, empty.renamed _, ?_⟩
  constructor
  intro location world rc identity fields found
  simp [empty location] at found

theorem emptyHeap.owned {store : IxIR1.Store} (empty : emptyHeap store) (values : Array Word) :
    IxIR1.Sim.RootOwnership store (IxIR1.Sim.rootsFor .shared (values.map rval).toList) := by
  have ownership : IxIR1.Sim.RootOwnership store [] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · intro location box found
      simp [empty location] at found
    · intro location box address arity captured found
      simp [empty location] at found
    · intro location box found
      simp [empty location] at found
  simpa using scalarArguments_owned ownership values

/-- A closed initializer may leave dead slots, but its only live value is
the returned shared PAP with one exact Word capture. -/
structure Heap (store : IxIR1.Store) (address : Ixon.Address) (capture : Word) where
  location : Nat
  found : store.get? location = some ⟨.shared, 1, .papN address 2 #[rval capture]⟩
  exclusive : ∀ index box, store.get? index = some box → index = location

def exclusive (store : IxIR1.Store) (location : Nat) : Bool :=
  (Array.range store.nodes.size).all fun index => index == location || (store.get? index).isNone

theorem exclusive_sound {store : IxIR1.Store} {location : Nat} (accepted : exclusive store location = true) :
    ∀ index box, store.get? index = some box → index = location := by
  intro index box found
  have small : index < store.nodes.size := by
    by_cases small : index < store.nodes.size
    · exact small
    · simp [IxIR1.Store.get?, Array.getElem?_eq_none (Nat.le_of_not_gt small)] at found
  have selected := Array.all_eq_true.mp accepted index (by simpa using small)
  simpa [Array.getElem_range, found] using selected

theorem Heap.box {store address capture} (heap : Heap store address capture)
    {index box} (found : store.get? index = some box) :
    box = ⟨.shared, 1, .papN address 2 #[rval capture]⟩ := by
  have same := heap.exclusive index box found
  subst index
  exact (Option.some.inj (heap.found.symm.trans found)).symm

theorem Heap.edges {store address capture} (heap : Heap store address capture) :
    IxIR1.Sim.edgeLocations store = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro slot member
  cases slot with
  | none => rfl
  | some box =>
      obtain ⟨index, small, located⟩ := Array.mem_iff_getElem.mp
        (show some box ∈ store.nodes from by simpa using member)
      have found : store.get? index = some box := by
        simp [IxIR1.Store.get?, Array.getElem?_eq_getElem small, located]
      rw [heap.box found]
      simp [IxIR1.Sim.slotEdgeLocations, IxIR1.Sim.nodeChildren, rval, IxIR1.Sim.rvalLocation?]

theorem Heap.owned {store address capture} (heap : Heap store address capture) :
    IxIR1.Sim.RootOwnership store [⟨.shared, .loc heap.location⟩] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root member
    simp only [List.mem_singleton] at member
    subst root
    exact ⟨_, heap.found, rfl⟩
  · intro index box found child member
    rw [heap.box found] at member ⊢
    simp only [IxIR1.Sim.nodeChildren, List.mem_singleton] at member
    subst child
    trivial
  · intro index box function arity arguments found _
    rw [heap.box found]
  · intro index box found
    rw [heap.box found, heap.exclusive index box found]
    simp [IxIR1.Sim.incoming, heap.edges, IxIR1.Sim.rootLocation?, IxIR1.Sim.rvalLocation?]

def Heap.spent {store address capture} (heap : Heap store address capture) : IxIR1.Store :=
  store.rcTick.kill heap.location

theorem Heap.spent_empty {store address capture} (heap : Heap store address capture) : emptyHeap heap.spent := by
  intro index
  have small : heap.location < store.nodes.size := by
    by_cases small : heap.location < store.nodes.size
    · exact small
    · have found := heap.found
      simp [IxIR1.Store.get?, Array.getElem?_eq_none (Nat.le_of_not_gt small)] at found
  by_cases same : index = heap.location
  · subst index
    simp [Heap.spent, IxIR1.Store.kill, IxIR1.Store.rcTick, IxIR1.Store.get?, small]
  · have absent : store.get? index = none := by
      cases found : store.get? index with
      | none => rfl
      | some box => exact False.elim (same (heap.exclusive index box found))
    simpa [Heap.spent, IxIR1.Store.kill, IxIR1.Store.rcTick, IxIR1.Store.get?, Array.getElem?_setIfInBounds, same, Ne.symm same] using absent

theorem Heap.drop {store address capture} (heap : Heap store address capture) (context : IxIR1.Ctx) (fuel : Nat) :
    IxIR1.dropVal context (fuel + 4) store (.loc heap.location) = .ok heap.spent := by
  simp [IxIR1.dropVal, heap.found, IxIR1.dropMany, Heap.spent, rval]

/-- Successful ordinary application supplies the captured Word before the
runtime argument and completely consumes the exported closure. -/
theorem Heap.applied {store address capture} (heap : Heap store address capture)
    {context : IxIR1.Ctx} {declaration : IxIR1.Decl}
    (declared : context.decls address = some declaration) (safe : IxIR1.declPapSafe declaration = true)
    (argument : Word) {fuel : Nat} {output : IxIR1.Store × IxIR1.RVal}
    (applied : IxIR1.applyGo context fuel store (.loc heap.location) [rval argument] = .ok output) :
    ∃ callFuel, IxIR1.invoke context callFuel address [rval capture, rval argument] heap.spent = .ok output := by
  have padded := IxIR1.applyGo_mono (larger := fuel + 5) (by omega) applied
  refine ⟨fuel + 4, ?_⟩
  simpa [IxIR1.applyGo, heap.found, IxIR1.dupVals, heap.drop, declared, safe,
    bind, Except.bind, pure, Except.pure, rval] using padded

end Ix.Compiler.X86.PhysicalScalar.Captured
