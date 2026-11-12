import IxCC.Cfg.Rc.Proof.Physical.PublicationReady
import IxCC.Cfg.Rc.Proof.Physical.ReservedReady
import IxCC.Rt.Rc.Gen.Proof.ReserveBump
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- Actual bump allocation and payload publication extend the occupied arena
and logical heap together. The free lists stay unchanged and the updated
bump control word remains part of the final allocator-ready invariant. -/
theorem allocation_bump_ready {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    (positive : 0 < body.fields.length) (small : body.fields.length ≤ maxFields)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    (empty : lists (fieldsClass body.fields.length) = [])
    (space : bump.toNat + classBytes (fieldsClass body.fields.length) ≤ limit.toNat)
    (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j)) :
    let next := bump + UInt64.ofNat (classBytes (fieldsClass body.fields.length))
    let reservedMem := Gen.reserveBump mem context bump next (CellLayout.ofFields body.fields.length body.ctor.tag) (fieldsClass body.fields.length)
    eval (Gen.allocProgram (CellLayout.ofFields body.fields.length body.ctor.tag)) 0 [] mem context =
      .ok ([bump], reservedMem) ∧
    Gen.AllocatorReady maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size bump)
      (publishFields reservedMem bump words (List.range body.fields.length))
      (fun location => external location + refsIn location [(heap.alloc .rc body).1])
      context base next limit
      (publishSlots heap.size bump (Gen.bumpSlot bump (fieldsClass body.fields.length) :: slots)) lists := by
  obtain ⟨execution, reserved, header⟩ := ready.reserve_bump (Gen.ofFields_layout positive small tagBound).1
    (Gen.ofFields_layout (tag := body.ctor.tag) positive small tagBound).2 (Gen.fieldsClass_spec positive small).2.1
    empty space 0
  have member : Gen.bumpSlot bump (fieldsClass body.fields.length) ∈ Gen.bumpSlot bump (fieldsClass body.fields.length) :: slots := by simp
  have storage := reserved_from_ready reserved member body rfl
    positive small tagBound nobj nscalar shared header
  exact ⟨execution, publication_ready reserved member rfl rfl storage words values⟩


end IxCC.Cfg.Rc.Native
