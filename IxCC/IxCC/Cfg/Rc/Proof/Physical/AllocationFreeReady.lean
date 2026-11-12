import IxCC.Cfg.Rc.Proof.Physical.PublicationReady
import IxCC.Cfg.Rc.Proof.Physical.ReservedReady
import IxCC.Rt.Rc.Gen.Proof.ReserveFree
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- The concrete free-pop allocator followed by actual payload stores yields
a complete allocator-ready heap with one returned root. The only input tokens
are the constructor's fields; no allocation-success premise is assumed. -/
theorem allocation_free_ready {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    {target : Slot} (member : target ∈ slots) {tail : List Word}
    (head : lists target.cls = target.address :: tail)
    (sizeClass : target.cls = fieldsClass body.fields.length)
    (positive : 0 < body.fields.length) (small : body.fields.length ≤ maxFields)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j)) :
    let reservedMem := Gen.reserveFree mem context target.address (tail.headD 0)
      (CellLayout.ofFields body.fields.length body.ctor.tag) (fieldsClass body.fields.length)
    eval (Gen.allocProgram (CellLayout.ofFields body.fields.length body.ctor.tag)) 0 [] mem context =
      .ok ([target.address], reservedMem) ∧
    Gen.AllocatorReady maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size target.address)
      (publishFields reservedMem target.address words (List.range body.fields.length))
      (fun location => external location + refsIn location [(heap.alloc .rc body).1])
      context base bump limit
      (publishSlots heap.size target.address (Gen.reserveSlots target.address slots))
      (Gen.popFree lists target.cls) := by
  obtain ⟨execution, reserved, placed, header⟩ :=
    ready.reserve_free member head sizeClass (Gen.ofFields_layout positive small tagBound).1
      (Gen.ofFields_layout (tag := body.ctor.tag) positive small tagBound).2 0
  refine ⟨execution, ?_⟩
  have storage := reserved_from_ready reserved placed body sizeClass
    positive small tagBound nobj nscalar shared header
  exact publication_ready reserved placed rfl sizeClass storage words values


end IxCC.Cfg.Rc.Native
