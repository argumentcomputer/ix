import Compilatrix.Cfg.Rc.Proof.Physical.HeapPlacement

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Rt.Rc.Procs

theorem allocated_cell (heap : Own.Heap) (body : Own.Body) (location : Nat) :
    (heap.alloc .rc body).2.cell? location =
      if location = heap.size then some (.live 1 .dyn body) else heap.cell? location := by
  simp only [Own.Heap.alloc, Own.Heap.cell?, Own.Heap.size, Own.AllocPol.mode, Array.getElem?_push]
  rfl

theorem allocated_old {heap : Own.Heap} {body other : Own.Body} {location refs : Nat}
    (old : heap.cell? location = some (.live refs .dyn other)) :
    (heap.alloc .rc body).2.cell? location = some (.live refs .dyn other) := by
  have bound : location < heap.size := (Array.getElem?_eq_some_iff.mp old).1
  simpa only [allocated_cell, if_neg (Nat.ne_of_lt bound)] using old

/-- Add the fresh abstract live cell after concrete publication. Existing live
storage, new payload words and physical interval separation are independent
premises proved by the allocator/publication frame lemmas. Dead mappings need
not be injective and are not inspected. -/
theorem heapLive_append {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    (old : HeapLive heap addresses mem) {body : Own.Body} {address : Lir.Word}
    (mapped : addresses heap.size = some address)
    (published : LiveCell addresses mem address 1 body)
    (children : ∀ child, Own.RVal.loc child ∈ body.fields →
      ∃ refs other, heap.cell? child = some (.live refs .dyn other))
    (separate : ∀ location refs other placed,
      heap.cell? location = some (.live refs .dyn other) → addresses location = some placed →
      address.toNat + Rt.cellBytes body.fields.length ≤ placed.toNat ∨
        placed.toNat + Rt.cellBytes other.fields.length ≤ address.toNat) :
    HeapLive (heap.alloc .rc body).2 addresses mem := by
  refine {cell := ?_, fields_live := ?_, disjoint := ?_}
  · intro location refs mode other cell
    by_cases fresh : location = heap.size
    · subst location
      have equal : 1 = refs ∧ Own.OMode.dyn = mode ∧ body = other := by
        simpa [allocated_cell] using cell
      rcases equal with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, address, mapped, published⟩
    · have previous : heap.cell? location = some (.live refs mode other) := by
        simpa only [allocated_cell, if_neg fresh] using cell
      exact old.cell location refs mode other previous
  · intro location refs other child cell member
    by_cases fresh : location = heap.size
    · subst location
      have equal : 1 = refs ∧ body = other := by
        simpa [allocated_cell] using cell
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨childRefs, childBody, childCell⟩ := children child member
      exact ⟨childRefs, childBody, allocated_old childCell⟩
    · have previous : heap.cell? location = some (.live refs .dyn other) := by
        simpa only [allocated_cell, if_neg fresh] using cell
      obtain ⟨childRefs, childBody, childCell⟩ := old.fields_live location refs other child previous member
      exact ⟨childRefs, childBody, allocated_old childCell⟩
  · intro l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ cell₁ cell₂ map₁ map₂ different
    by_cases fresh₁ : l₁ = heap.size
    · subst l₁
      have fresh₂ : l₂ ≠ heap.size := Ne.symm different
      have equal : 1 = r₁ ∧ body = b₁ := by
        simpa [allocated_cell] using cell₁
      rcases equal with ⟨rfl, rfl⟩
      have addressEq : address = a₁ := Option.some.inj (mapped.symm.trans map₁)
      subst a₁
      exact separate l₂ r₂ b₂ a₂ (by simpa only [allocated_cell, if_neg fresh₂] using cell₂) map₂
    · by_cases fresh₂ : l₂ = heap.size
      · subst l₂
        have equal : 1 = r₂ ∧ body = b₂ := by
          simpa [allocated_cell] using cell₂
        rcases equal with ⟨rfl, rfl⟩
        have addressEq : address = a₂ := Option.some.inj (mapped.symm.trans map₂)
        subst a₂
        exact (separate l₁ r₁ b₁ a₁ (by simpa only [allocated_cell, if_neg fresh₁] using cell₁) map₁).symm
      · exact old.disjoint l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂
          (by simpa only [allocated_cell, if_neg fresh₁] using cell₁)
          (by simpa only [allocated_cell, if_neg fresh₂] using cell₂) map₁ map₂ different


end Compilatrix.Cfg.Rc.Native
