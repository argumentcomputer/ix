import IxCC.Rt.Rc.Gen.Proof.ReleaseInvariant
import IxCC.Own.Rc.Proof.Allocation

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

theorem idle_field_tokens {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (idle : Gen.ReleaseInvariant maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields) none []
      context base bump limit slots lists) : Balance heap external body.fields := by
  intro location
  simpa [cursorTokens, flattenPending, refsIn] using idle.balance location

/-- Constructor publication consumes its existing field tokens as edges and
adds exactly one returned root. Aliased fields retain their multiplicity. -/
theorem publication_balance {heap : Heap} {external : Nat → Nat} {body : Own.Body}
    (fields : Balance heap external body.fields) :
    Balance (heap.alloc .rc body).2
      (fun location => external location + refsIn location [(heap.alloc .rc body).1]) [] := by
  intro location
  simpa [refsIn] using balance_alloc fields location

theorem publication_children {heap : Heap} {external : Nat → Nat} {body : Own.Body}
    (fields : Balance heap external body.fields) (child : Nat) (member : RVal.loc child ∈ body.fields) :
    ∃ refs other, heap.cell? child = some (.live refs .dyn other) := by
  obtain ⟨refs, other, cell, _⟩ := balance_pending_live fields member
  exact ⟨refs, other, cell⟩



end IxCC.Cfg.Rc.Native
