import Compilatrix.Cfg.Rc.Proof.Physical.PublicationReady
import Compilatrix.Cfg.Rc.Proof.Physical.ReservedReady
import Compilatrix.Rt.Rc.Proof.ReserveFree

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt Compilatrix.Rt.Rc Compilatrix.Rt.Rc.Procs

/-- The concrete free-pop allocator followed by actual payload stores yields
a complete allocator-ready heap with one returned root. The only input tokens
are the constructor's fields; no allocation-success premise is assumed. -/
theorem allocation_free_ready {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : AllocatorReady heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    {target : Slot} (member : target ∈ slots) {tail : List Word}
    (head : lists target.cls = target.address :: tail)
    (sizeClass : target.cls = smallClass body.fields.length)
    (positive : 0 < body.fields.length) (small : body.fields.length < 32)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j)) :
    let reservedMem := reserveFree mem context target.address (tail.headD 0)
      body.fields.length body.ctor.tag
    eval (allocProgram body.fields.length body.ctor.tag) 0 [] mem context =
      .ok ([target.address], reservedMem) ∧
    AllocatorReady (heap.alloc .rc body).2 (placeFresh addresses heap.size target.address)
      (publishFields reservedMem target.address words (List.range body.fields.length))
      (fun location => external location + refsIn location [(heap.alloc .rc body).1])
      context base bump limit
      (publishSlots heap.size target.address (reserveSlots target.address slots))
      (popFree lists target.cls) := by
  obtain ⟨execution, reserved, placed, header⟩ :=
    ready.reserve_free member head sizeClass positive small tagBound 0
  refine ⟨execution, ?_⟩
  have storage := reserved_from_ready reserved placed body sizeClass
    positive small tagBound nobj nscalar shared header
  exact publication_ready reserved placed rfl sizeClass storage words values


end Compilatrix.Cfg.Rc.Native
