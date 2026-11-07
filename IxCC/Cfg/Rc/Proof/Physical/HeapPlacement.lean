import IxCC.Cfg.Rc.Proof.Physical.Placement

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Procs

theorem heapLive_fieldBounded {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    (live : HeapLive heap addresses mem) {location refs : Nat} {body : Own.Body}
    (cell : heap.cell? location = some (.live refs .dyn body)) :
    Own.Plain.ValuesBounded heap.size body.fields := by
  intro value member
  cases value with
  | loc child =>
    obtain ⟨childRefs, childBody, childCell⟩ := live.fields_live location refs body child cell member
    exact (Array.getElem?_eq_some_iff.mp childCell).1
  | lit _ | ctor0 _ | erased => trivial

/-- Extending the address map at the fresh abstract index preserves every
existing live representation, even if the chosen physical address is retained
by dead-location mappings. Its separation from live storage is checked when
the newly allocated cell is added, not by global address-map injectivity. -/
theorem heapLive_placeFresh {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    (live : HeapLive heap addresses mem) (address : Lir.Word) :
    HeapLive heap (placeFresh addresses heap.size address) mem := by
  refine {cell := ?_, fields_live := live.fields_live, disjoint := ?_}
  · intro location refs mode body cell
    obtain ⟨dynamic, actual, mapped, represented⟩ := live.cell location refs mode body cell
    subst mode
    have bound : location < heap.size := (Array.getElem?_eq_some_iff.mp cell).1
    refine ⟨rfl, actual, ?_, ?_⟩
    · simpa [placeFresh, Nat.ne_of_lt bound] using mapped
    · refine {represented with fields := ?_}
      intro j value lookup
      obtain ⟨word, encoded, bytes⟩ := represented.fields j value lookup
      refine ⟨word, ?_, bytes⟩
      rw [placeFresh_old (heapLive_fieldBounded live cell value (List.mem_of_getElem? lookup))]
      exact encoded
  · intro l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ cell₁ cell₂ map₁ map₂ different
    have bound₁ : l₁ < heap.size := (Array.getElem?_eq_some_iff.mp cell₁).1
    have bound₂ : l₂ < heap.size := (Array.getElem?_eq_some_iff.mp cell₂).1
    have old₁ : addresses l₁ = some a₁ := by simpa [placeFresh, Nat.ne_of_lt bound₁] using map₁
    have old₂ : addresses l₂ = some a₂ := by simpa [placeFresh, Nat.ne_of_lt bound₂] using map₂
    exact live.disjoint l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ cell₁ cell₂ old₁ old₂ different


end IxCC.Cfg.Rc.Native
